module Unison.LSP.SignatureHelp where

import Control.Lens hiding (List)
import Control.Monad.Reader
import Data.Char (ord)
import Data.IntervalMap.Lazy qualified as IM
import Data.List (findIndex)
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text
import Language.LSP.Protocol.Lens
import Language.LSP.Protocol.Message qualified as Msg
import Language.LSP.Protocol.Types
import Unison.ABT qualified as ABT
import Unison.Codebase qualified as Codebase
import Unison.ConstructorType qualified as CT
import Unison.HashQualified qualified as HQ
import Unison.LSP.Conversions (annToRange, lspToUPos)
import Unison.LSP.FileAnalysis (getFileSummary, ppedForFile)
import Unison.LSP.FileAnalysis qualified as FileAnalysis
import Unison.LSP.Queries (removeInferredTypeAnnotations)
import Unison.LSP.Types
import Unison.LabeledDependency qualified as LD
import Unison.Lexer.Pos (Pos)
import Unison.Parser.Ann (Ann)
import Unison.Parser.Ann qualified as Ann
import Unison.Prelude
import Unison.PrettyPrintEnv qualified as PPE
import Unison.PrettyPrintEnvDecl qualified as PPED
import Unison.Reference qualified as Reference
import Unison.Referent qualified as Referent
import Unison.Symbol (Symbol)
import Unison.Syntax.Name qualified as Name
import Unison.Syntax.TypePrinter qualified as TypePrinter
import Unison.Term (Term)
import Unison.Term qualified as Term
import Unison.Type qualified as Type
import Unison.Typechecker.Context qualified as Context
import Unison.Typechecker.TypeVar qualified as TypeVar
import Unison.UnisonFile.Summary (FileSummary (..))
import Unison.Util.Pretty qualified as Pretty
import Unison.Var qualified as Var

signatureHelpHandler ::
  Msg.TRequestMessage 'Msg.Method_TextDocumentSignatureHelp ->
  (Either (Msg.TResponseError 'Msg.Method_TextDocumentSignatureHelp) (Msg.MessageResult 'Msg.Method_TextDocumentSignatureHelp) -> Lsp ()) ->
  Lsp ()
signatureHelpHandler m respond =
  respond . Right . maybe (InR Null) InL =<< runMaybeT do
    let pos = m ^. params . position
    let fileUri = m ^. params . textDocument . uri
    sigHelp fileUri pos

sigHelp :: (Lspish m, MonadUnliftIO m) => Uri -> Position -> MaybeT m SignatureHelp
sigHelp uri pos = do
  let uPos = lspToUPos pos
  (FileSummary {termsBySymbol, testWatchSummary, exprWatchSummary}) <- getFileSummary uri
  let trms = termsBySymbol & foldMap \(_ann, _ref, trm, _mayTyp) -> [trm]
  let allTerms =
        trms
          <> (testWatchSummary ^.. folded . _4)
          <> (exprWatchSummary ^.. folded . _4)
  (funcTerm, args, activeParamIdx) <-
    MaybeT . pure $
      altMap (findEnclosingApp uPos . removeInferredTypeAnnotations) allTerms

  let numArgs = Prelude.length args

  funcType <- getFuncType uri funcTerm
  pped <- lift $ ppedForFile uri
  let suffixifiedPPE = PPED.suffixifiedPPE pped
  let prettyWidth = Pretty.Width 40

  -- Strip forall quantifiers before decomposing arrows.
  -- The type may be `∀ a. a -> a` which needs unwrapping first.
  let (_quantifiedVars, funcTypeBody) = Type.unForallsOpt funcType

  -- Count the type's arrow params to validate
  case Type.unEffectfulArrows funcTypeBody of
    Nothing -> empty
    Just (_firstParam, rest) -> do
      let typeArity = Prelude.length rest
      guard (typeArity > 0)
      guard (activeParamIdx < fromIntegral numArgs)

      let funcLabel = renderFuncLabel suffixifiedPPE funcTerm
      let prefix = funcLabel <> " : "
      -- Use the full type pretty-printer for the signature label.
      -- This correctly handles parenthesization and effects.
      let fullSig = TypePrinter.prettyStr prettyWidth suffixifiedPPE funcTypeBody
      -- Split the rendered type at top-level arrows, then group segments
      -- to match the call-site arity.
      paramNames <- lift $ getParamNames uri funcTerm
      let (sigLabel, paramLabels) = buildSignatureLabel prefix fullSig numArgs paramNames

      pure
        SignatureHelp
          { _signatures =
              [ SignatureInformation
                  { _label = sigLabel,
                    _documentation = Nothing,
                    _parameters = Just paramLabels,
                    _activeParameter = Just (InL activeParamIdx)
                  }
              ],
            _activeSignature = Just 0,
            _activeParameter = Just (InL activeParamIdx)
          }

-- | Get a human-readable label for the function being called,
-- using the PPE to resolve references to nice names.
renderFuncLabel :: PPE.PrettyPrintEnv -> Term Symbol Ann -> Text
renderFuncLabel ppe term = case ABT.out term of
  ABT.Var v -> Var.name v
  ABT.Tm f -> case f of
    Term.Ref ref -> HQ.toTextWith Name.toText $ PPE.termName ppe (Referent.Ref ref)
    Term.Constructor conRef -> HQ.toTextWith Name.toText $ PPE.termName ppe (Referent.Con conRef CT.Data)
    Term.Request conRef -> HQ.toTextWith Name.toText $ PPE.termName ppe (Referent.Con conRef CT.Effect)
    _ -> "fn"
  _ -> "fn"

-- | Get the type of a function term.
-- Returns a Context.Type which uses TypeVar variables (from the typechecker).
getFuncType :: (Lspish m, MonadUnliftIO m) => Uri -> Term Symbol Ann -> MaybeT m (Context.Type Symbol Ann)
getFuncType uri funcTerm =
  getFromLocalBindings <|> getFromRef
  where
    getFromRef = do
      ref <- MaybeT . pure $ refInTermForSigHelp funcTerm
      case ref of
        LD.TermReferent referent ->
          -- Type.Type Symbol Ann needs to be generalized to Context.Type Symbol Ann
          generalize <$> getTypeOfReferent uri referent
        LD.TypeReference _typeRef -> empty

    getFromLocalBindings = do
      let funcAnn = ABT.annotation funcTerm
      case annToRange funcAnn of
        Nothing -> empty
        Just range -> do
          FileAnalysis {localBindingInfo} <- FileAnalysis.getFileAnalysis uri
          let startPos = range ^. start
          (_interval, (typ, _definitionSite)) <-
            MaybeT . pure $
              IM.lookupMin $
                IM.intersecting localBindingInfo (IM.ClosedInterval startPos startPos)
          pure typ

-- | Get parameter names from the function definition, if available.
-- Extracts variable names from the lambda abstractions of the term body.
getParamNames :: (Lspish m, MonadUnliftIO m) => Uri -> Term Symbol Ann -> m [Text]
getParamNames uri funcTerm = do
  mayTerm <- runMaybeT $ getTermBody uri funcTerm
  pure $ case mayTerm of
    Just t -> case Term.unLams' (peelAnns t) of
      Just (vs, _body) -> fmap Var.name vs
      Nothing -> []
    Nothing -> []

-- | Get the term body for a function, looking in the file first, then the codebase.
getTermBody :: (Lspish m, MonadUnliftIO m) => Uri -> Term Symbol Ann -> MaybeT m (Term Symbol Ann)
getTermBody uri funcTerm = case ABT.out funcTerm of
  ABT.Var v -> do
    -- Local variable: look up its definition in the file's termsBySymbol.
    -- We match by name rather than exact Symbol equality because the
    -- typechecker may freshen the variable at the call site.
    FileSummary {termsBySymbol} <- getFileSummary uri
    let vName = Var.name v
    MaybeT . pure . listToMaybe $
      [ trm
      | (sym, (_ann, _ref, trm, _typ)) <- Map.toList termsBySymbol,
        Var.name sym == vName
      ]
  ABT.Tm f -> case f of
    Term.Ref (Reference.DerivedId refId) -> do
      -- Try file first, then codebase
      let getFromFile = do
            FileSummary {termsByReference} <- getFileSummary uri
            MaybeT . pure $ termsByReference ^? ix (Just refId) . folded . _2
          getFromCodebase = do
            Env {codebase} <- ask
            MaybeT . liftIO $ Codebase.runTransaction codebase $ Codebase.getTerm codebase refId
      getFromFile <|> getFromCodebase
    _ -> empty
  _ -> empty

-- | Peel off top-level Ann wrappers from a term.
-- The typechecker wraps terms in Ann nodes (both inferred and user-provided).
-- We need to strip these to find the underlying lambda parameters.
peelAnns :: Term Symbol Ann -> Term Symbol Ann
peelAnns t = case ABT.out t of
  ABT.Tm (Term.Ann inner _typ) -> peelAnns inner
  _ -> t

-- | Generalize a Type from plain Symbol variables to TypeVar variables.
generalize :: Type.Type Symbol Ann -> Context.Type Symbol Ann
generalize = ABT.vmap TypeVar.Universal

-- | Gets the type of a referent from either the parsed file or the codebase.
getTypeOfReferent :: (Lspish m) => Uri -> Referent.Referent -> MaybeT m (Type.Type Symbol Ann)
getTypeOfReferent fileUri ref =
  getFromFile <|> getFromCodebase
  where
    getFromFile = do
      FileSummary {termsByReference} <- getFileSummary fileUri
      case ref of
        Referent.Ref (Reference.Builtin {}) -> empty
        Referent.Ref (Reference.DerivedId termRefId) ->
          MaybeT . pure $ (termsByReference ^? ix (Just termRefId) . folded . _3 . _Just)
        Referent.Con {} -> empty
    getFromCodebase = do
      Env {codebase} <- ask
      MaybeT . liftIO $ Codebase.runTransaction codebase $ Codebase.getTypeOfReferent codebase ref

-- | Extract a labeled dependency from a term (for the head of a function application).
refInTermForSigHelp :: Term Symbol Ann -> Maybe LD.LabeledDependency
refInTermForSigHelp term = case ABT.out term of
  ABT.Tm f -> case f of
    Term.Ref ref -> Just (LD.TermReference ref)
    Term.Constructor conRef -> Just (LD.ConReference conRef CT.Data)
    Term.Request conRef -> Just (LD.ConReference conRef CT.Effect)
    _ -> Nothing
  _ -> Nothing

-- | Find the innermost function application chain where the cursor is on an argument,
-- returning (function, arguments, active parameter index).
--
-- For a call like `f a b c` with cursor on `b`, returns `(f, [a, b, c], 1)`.
-- Crucially, if the cursor is on the function head (e.g. on `f` itself), this does NOT
-- match — we let the parent application claim it. This way, in `outer (inner x)` with
-- the cursor on `inner`, we show `outer`'s signature (with `inner x` as the active param)
-- rather than `inner`'s signature.
findEnclosingApp :: Pos -> Term Symbol Ann -> Maybe (Term Symbol Ann, [Term Symbol Ann], UInt)
findEnclosingApp pos term =
  -- Try to find a match in children first (deeper/innermost apps),
  -- then try matching here.
  findInChildren <|> findHere
  where
    termAnn = ABT.annotation term

    findHere :: Maybe (Term Symbol Ann, [Term Symbol Ann], UInt)
    findHere = case ABT.out term of
      ABT.Tm (Term.App _ _)
        | termAnn `Ann.contains` pos -> do
            let (func, args) = collectApps term
            -- Only match if the cursor is on an argument, NOT on the function head.
            -- If the cursor is on the function head, this app isn't the right context.
            guard (not $ cursorOnFuncHead pos func)
            let activeParam = findActiveParam pos args
            Just (func, args, activeParam)
      _ -> Nothing

    findInChildren :: Maybe (Term Symbol Ann, [Term Symbol Ann], UInt)
    findInChildren = case ABT.out term of
      ABT.Tm f -> case f of
        Term.App _ _ ->
          -- For application chains, only recurse into the arguments,
          -- NOT the left spine. Otherwise `App (App f a) b` with cursor on `a`
          -- would match the inner `App f a` instead of the full chain.
          let (_func, args) = collectApps term
           in altMap (findEnclosingApp pos) args
        Term.Handle a b -> findEnclosingApp pos a <|> findEnclosingApp pos b
        Term.Ann a _typ -> findEnclosingApp pos a
        Term.List xs -> altSum (findEnclosingApp pos <$> xs)
        Term.If cond a b -> findEnclosingApp pos cond <|> findEnclosingApp pos a <|> findEnclosingApp pos b
        Term.And l r -> findEnclosingApp pos l <|> findEnclosingApp pos r
        Term.Or l r -> findEnclosingApp pos l <|> findEnclosingApp pos r
        Term.Lam a -> findEnclosingApp pos a
        Term.LetRec _isTop xs y ->
          altSum (findEnclosingApp pos <$> xs) <|> findEnclosingApp pos y
        Term.Let _isTop a b ->
          findEnclosingApp pos a <|> findEnclosingApp pos b
        Term.Match a cases ->
          findEnclosingApp pos a
            <|> altSum
              ( cases <&> \(Term.MatchCase _pat grd body) ->
                  (grd >>= findEnclosingApp pos) <|> findEnclosingApp pos body
              )
        _ -> Nothing
      ABT.Var {} -> Nothing
      ABT.Cycle r -> findEnclosingApp pos r
      ABT.Abs _v r -> findEnclosingApp pos r

-- | Check if the cursor is on the function head of an application.
-- The function head is the leftmost non-App term in the application chain.
-- We walk through nested Apps to find the true function head and check
-- if its annotation contains the cursor.
cursorOnFuncHead :: Pos -> Term Symbol Ann -> Bool
cursorOnFuncHead pos func = ABT.annotation func `Ann.contains` pos

-- | Collect the function and all arguments from a chain of App nodes.
-- `f a b c` is represented as `App (App (App f a) b) c`
-- This returns `(f, [a, b, c])`.
collectApps :: Term Symbol Ann -> (Term Symbol Ann, [Term Symbol Ann])
collectApps = go []
  where
    go args (Term.App' f x) = go (x : args) f
    go args f = (f, args)

-- | Determine which parameter is active based on cursor position.
-- Returns the 0-indexed parameter index.
findActiveParam :: Pos -> [Term Symbol Ann] -> UInt
findActiveParam pos args =
  case findIndex (\arg -> ABT.annotation arg `Ann.contains` pos) args of
    Just idx -> fromIntegral idx
    Nothing ->
      -- Cursor is not directly on any argument (between args or after last).
      -- Count how many args end before or at the cursor position.
      let numArgsBefore = Prelude.length $ filter (argEndsBefore pos) args
       in fromIntegral numArgsBefore

-- | Check if an argument's annotation ends before the given position.
argEndsBefore :: Pos -> Term Symbol Ann -> Bool
argEndsBefore pos arg = case safeAnnEnd (ABT.annotation arg) of
  Nothing -> False
  Just endPos -> endPos <= pos

-- | Safely extract the end position from an Ann.
safeAnnEnd :: Ann -> Maybe Pos
safeAnnEnd (Ann.Ann _ e) = Just e
safeAnnEnd (Ann.GeneratedFrom a) = safeAnnEnd a
safeAnnEnd _ = Nothing

--

-- | Build the full signature label with parameter names inlined, and compute
-- offset-based parameter labels. For a function `foo(a, b) : Text -> Nat -> Bool`,
-- produces label "foo : (a : Text) -> (b : Nat) -> Bool" with offsets pointing
-- to each "(name : Type)" span.
--
-- Splits the rendered type at top-level arrows, groups segments to match
-- call-site arity, prepends parameter names where available, then reassembles.
buildSignatureLabel :: Text -> Text -> Int -> [Text] -> (Text, [ParameterInformation])
buildSignatureLabel prefix fullSig numArgs paramNames =
  let (segments, arrows) = splitTopLevelArrows fullSig
      -- segments has (typeArity + 1) entries; arrows has typeArity entries
      typeArity = Prelude.length segments - 1
      nParams = min numArgs typeArity
      -- Group segments into nParams parameter chunks + return type.
      -- If typeArity > nParams, merge the first (typeArity - nParams + 1)
      -- segments into one parameter (for higher-order function args).
      groupSize = typeArity - nParams + 1
      -- Each param chunk is a list of (segment, trailing arrow) pairs,
      -- except the last segment in a chunk has no trailing arrow.
      paramChunks = makeChunks groupSize nParams segments arrows
      -- Return type is everything after the params
      retStart = groupSize + nParams - 1
      retSegs = drop retStart segments
      retArrows = drop retStart arrows
      returnText = mconcat $ interleave retSegs retArrows
      -- Decorate each param chunk with its name
      names = (fmap Just paramNames <> repeat Nothing) & take nParams
      chunkTexts = fmap (\segsAndArrows -> mconcat $ interleave (fmap fst segsAndArrows) (fmap snd segsAndArrows)) paramChunks
      labeledParams = zipWith decorateSeg names chunkTexts
      -- Get the arrows between params (arrow after each grouped chunk)
      paramSepArrows = take (nParams - 1) (drop (groupSize - 1) arrows)
      -- Arrow between last param and return type
      lastArrow = case drop (retStart - 1) arrows of
        (a : _) -> a
        [] -> " -> "
      -- Assemble the label
      paramPart = mconcat $ interleave labeledParams paramSepArrows
      sigBody = if null retSegs then paramPart else paramPart <> lastArrow <> returnText
      sigLabel = prefix <> sigBody
      -- Compute UTF-16 offsets for each labeled param
      prefixU16 = utf16Length prefix
      allSepArrows = paramSepArrows <> [lastArrow]
      paramInfos = snd $ foldl'
        (\(curOffset, acc) (seg, idx) ->
          let segU16 = utf16Length seg
              arrowU16 = if idx < Prelude.length allSepArrows
                         then utf16Length (allSepArrows !! idx)
                         else 0
              info = ParameterInformation
                { _label = InR (curOffset, curOffset + segU16),
                  _documentation = Nothing
                }
           in (curOffset + segU16 + arrowU16, acc <> [info])
        )
        (prefixU16, [])
        (zip labeledParams [0 :: Int ..])
   in (sigLabel, paramInfos)
  where
    decorateSeg :: Maybe Text -> Text -> Text
    decorateSeg (Just n) typeSeg = "(" <> n <> " : " <> typeSeg <> ")"
    decorateSeg Nothing typeSeg = typeSeg

    -- Build nParams chunks from segments and arrows.
    -- The first chunk has groupSize segments, the rest have 1 each.
    makeChunks :: Int -> Int -> [Text] -> [Text] -> [[(Text, Text)]]
    makeChunks _ 0 _ _ = []
    makeChunks gs nP segs arrs =
      let chunkSegs = take gs segs
          chunkArrows = take (gs - 1) arrs
          -- Pair each segment with its trailing arrow (last seg gets "")
          chunk = zipWith (,) chunkSegs (chunkArrows <> [""])
          rest = makeChunks 1 (nP - 1) (drop gs segs) (drop gs arrs)
       in chunk : rest

-- | Interleave two lists: [a,b,c] [x,y] -> [a,x,b,y,c]
interleave :: [a] -> [a] -> [a]
interleave [] _ = []
interleave [x] _ = [x]
interleave (x : xs) (y : ys) = x : y : interleave xs ys
interleave (x : xs) [] = x : xs

-- | Split a rendered type string at top-level " -> " arrows.
-- Returns (segments, arrows) where segments are the type parts between arrows,
-- and arrows are the full separator strings (e.g. " -> " or " ->{e} ").
-- segments always has one more element than arrows.
-- Respects nesting in (), {}, and [].
splitTopLevelArrows :: Text -> ([Text], [Text])
splitTopLevelArrows txt = go 0 0 0 (Text.unpack txt)
  where
    go :: Int -> Int -> Int -> String -> ([Text], [Text])
    go _depth segStart pos [] =
      ([textSlice segStart pos], [])
    go depth segStart pos ('-' : '>' : rest)
      | depth == 0 =
          let seg = Text.stripEnd $ textSlice segStart pos
              (skipped, rest') = skipArrowPrefix rest
              newStart = pos + 2 + skipped
              -- Arrow text: from end of trimmed segment to start of next segment
              arrowStart = segStart + Text.length seg
              arrow = textSlice arrowStart newStart
              (segs, arrows) = go depth newStart newStart rest'
           in (seg : segs, arrow : arrows)
    go depth segStart pos (c : rest) =
      let depth' = case c of
            '(' -> depth + 1
            '{' -> depth + 1
            '[' -> depth + 1
            ')' -> depth - 1
            '}' -> depth - 1
            ']' -> depth - 1
            _ -> depth
       in go depth' segStart (pos + 1) rest

    textSlice :: Int -> Int -> Text
    textSlice start end = Text.take (end - start) (Text.drop start txt)

    -- Skip spaces and effect annotations after "->", return count and remaining
    skipArrowPrefix :: String -> (Int, String)
    skipArrowPrefix (' ' : rest) = let (n, r) = skipArrowPrefix rest in (n + 1, r)
    skipArrowPrefix ('{' : rest) =
      let (n, rest') = skipUntilClose rest
       in skipArrowPrefix rest' & \(m, r) -> (1 + n + m, r)
    skipArrowPrefix s = (0, s)

    skipUntilClose :: String -> (Int, String)
    skipUntilClose [] = (0, [])
    skipUntilClose ('}' : rest) =
      case rest of
        ' ' : rest' -> (2, rest')
        _ -> (1, rest)
    skipUntilClose (_ : rest) = let (n, r) = skipUntilClose rest in (n + 1, r)

-- | Number of UTF-16 code units for a single Char.
-- Characters in the Basic Multilingual Plane (U+0000..U+FFFF) take 1 unit,
-- supplementary characters (U+10000+) take 2 (surrogate pair).
utf16Width :: Char -> UInt
utf16Width c
  | ord c < 0x10000 = 1
  | otherwise = 2

-- | Compute UTF-16 code unit length of a Text.
utf16Length :: Text -> UInt
utf16Length = Text.foldl' (\n c -> n + utf16Width c) 0
