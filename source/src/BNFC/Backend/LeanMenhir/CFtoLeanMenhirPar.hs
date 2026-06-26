{-# LANGUAGE LambdaCase #-}

{- |
Module      : BNFC.Backend.LeanMenhir.CFtoLeanMenhirPar
Description : Emit the Lean 4 parser modules that drive the verified
              LeanMenhir LR(1) runtime.

The parser is split across **four** Lean modules so that Lake can build the
two long-running @native_decide@ certificates concurrently:

  * @Par<LANG>Tables.lean@ — the sequentially-dependent core: grammar,
    @build_tables%@ splice, @ntType@/@termType@, the typed @actions@
    dispatcher, and the @Automaton@ instance.

  * @Par<LANG>Safe.lean@ — imports @…Tables@, proves @safe@ by
    @native_decide@, and hosts @adapt@/@eofAt@/@parse<Entry>@ (which need
    @safe@ to feed into @parseWith@).

  * @Par<LANG>Complete.lean@ — imports @…Tables@, proves @complete@ by
    @native_decide@.  Also exposes @unambig@ as a one-liner specialisation
    of @LeanMenhir.Main.unambiguity@ to this grammar's @safe@/@complete@
    (downstream theorem, no extra @decide@).

  * @Par<LANG>.lean@ — an umbrella module that @import@s @…Safe@ and
    @…Complete@.  Defines nothing; its purpose is to let the test driver
    @import Par<LANG>@ and transitively pick up @Par<LANG>.parse<Entry>@.

Lake's build DAG ends up as

      AbsLANG, LexLANG, ParserRuntime
                  │
                  ▼
            Par<LANG>Tables          ← sequential bottleneck
              │           │
              ▼           ▼
        Par<LANG>Safe   Par<LANG>Complete   ← parallel `native_decide`s
              │           │
              └─────┬─────┘
                    ▼
                Par<LANG>            ← umbrella
                    │
                    ▼
                TestLANG

so the two certificates run concurrently, saving ~one cert's worth of
wall-clock time on every build.

The CF→Grammar0 mapping rules are unchanged from the single-file design:

  * Every parsable rule contributes one production.  Precedence levels
    (@Exp@, @Exp1@, @Exp2@, ...) become distinct nonterminals related by
    identity coercions — this is what gives LeanMenhir its precedence
    handling.
  * Action arguments are bound in the REVERSE of the forward RHS order
    (because the bridge types actions over @prodRhsRev@); the constructor
    is then applied to the non-keyword arguments in their FORWARD order.
  * Keyword/punctuation RHS items become @Unit@-typed arguments (named
    @_@); token-category items get their concrete payload type (@Int@,
    @Float@, @Char@, @String@); nonterminals get their AST type.
  * Coercion rules (@_@) become identity functions on the single
    non-keyword argument.  List rules (@[]@/@(:[])@/@(:)@) build
    @[]@/@[x]@/@x :: xs@ respectively.
-}

module BNFC.Backend.LeanMenhir.CFtoLeanMenhirPar
  ( -- * Per-module emitters (one per generated parser file)
    cf2LeanMenhirParTables
  , cf2LeanMenhirParSafe
  , cf2LeanMenhirParComplete
  , cf2LeanMenhirParUmbrella
  ) where

import Data.List   ( intercalate, sort, sortBy )
import Data.Map    ( Map )
import qualified Data.Map as Map
import Data.Maybe  ( mapMaybe )

import BNFC.CF
import BNFC.Backend.Lean.LeanUtil
  ( catToLeanType, constructorName, sanitizeLeanUpper )

----------------------------------------------------------------------------
-- Public entrypoints
----------------------------------------------------------------------------

-- | Emit the @Par<LANG>Tables.lean@ module: grammar, tables, ntType/
--   termType, the typed @actions@ dispatcher, and the @automaton@ instance.
--   Self-contained except for upstream imports (AbsLANG, ParserRuntime for
--   @BNFC.Position@).  All defs live in the umbrella namespace (e.g.
--   @ParCalc@), not a per-module namespace, so the file split is invisible
--   to downstream code.
cf2LeanMenhirParTables
  :: String  -- ^ Tables module name (file), e.g. @"ParCalcTables"@.
  -> String  -- ^ Umbrella namespace, e.g. @"ParCalc"@ (shared by all 4 files).
  -> String  -- ^ AST module name (e.g. @"AbsCalc"@).
  -> String  -- ^ Runtime module name (for @BNFC.Position@).
  -> CF
  -> String
cf2LeanMenhirParTables tablesMod nsMod absMod runtimeMod cf =
    unlines $ concat
      [ tablesHeader tablesMod nsMod absMod runtimeMod
      , [""]
      , grammarBlock gn prods
      , [""]
      , tablesDefBlock
      , [""]
      , ntTypeBlock gn
      , [""]
      , termTypeBlock gn
      , [""]
      , actionsBlock gn prods
      , [""]
      , automatonBlock
      , [""]
      , [ "end " ++ nsMod ]
      ]
  where
    gn    = buildNumbering cf
    prods = startProd gn : map (toUserProd gn) (parsableRules cf)

-- | Emit the @Par<LANG>Safe.lean@ module.
cf2LeanMenhirParSafe
  :: String  -- ^ Safe module name (file), e.g. @"ParCalcSafe"@.
  -> String  -- ^ Tables module name (for @import@).
  -> String  -- ^ Umbrella namespace.
  -> String  -- ^ AST module name.
  -> String  -- ^ Lex module name.
  -> String  -- ^ Runtime module name.
  -> CF
  -> String
cf2LeanMenhirParSafe _safeMod tablesMod nsMod absMod lexMod runtimeMod cf =
    unlines $ concat
      [ safeHeader tablesMod nsMod absMod lexMod runtimeMod
      , [""]
      , safeCertBlock
      , [""]
      , adapterBlock gn
      , [""]
      , parseEntryBlock gn lexMod
      , [""]
      , [ "end " ++ nsMod ]
      ]
  where
    gn = buildNumbering cf

-- | Emit the @Par<LANG>Complete.lean@ module.  Does NOT depend on @…Safe@,
--   so Lake can run this and @…Safe@ concurrently.
cf2LeanMenhirParComplete
  :: String  -- ^ Complete module name (file), e.g. @"ParCalcComplete"@.
  -> String  -- ^ Tables module name.
  -> String  -- ^ Umbrella namespace.
  -> String
cf2LeanMenhirParComplete _completeMod tablesMod nsMod =
    unlines $ completeHeader tablesMod nsMod
      ++ [""]
      ++ completeCertBlock
      ++ [""]
      ++ [ "end " ++ nsMod ]

-- | Emit the umbrella @Par<LANG>.lean@.
cf2LeanMenhirParUmbrella
  :: String  -- ^ Umbrella module name (and namespace), e.g. @"ParCalc"@.
  -> String  -- ^ Tables module name.
  -> String  -- ^ Safe module name.
  -> String  -- ^ Complete module name.
  -> String
cf2LeanMenhirParUmbrella umbrellaMod tablesMod safeMod completeMod = unlines $
  [ "import " ++ tablesMod
  , "import " ++ safeMod
  , "import " ++ completeMod
  , ""
  , "/-! Umbrella for the LeanMenhir-generated parser.  Real content lives"
  , "    in `" ++ tablesMod ++ "` (grammar + tables + automaton),"
  , "    `" ++ safeMod ++ "` (parser + safety cert), and"
  , "    `" ++ completeMod ++ "` (completeness cert).  All three define"
  , "    into the `" ++ umbrellaMod ++ "` namespace, so downstream code"
  , "    just `import " ++ umbrellaMod ++ "` and refers to e.g."
  , "    `" ++ umbrellaMod ++ ".parseExp`, `" ++ umbrellaMod ++ ".safe`,"
  , "    `" ++ umbrellaMod ++ ".complete` and `" ++ umbrellaMod ++ ".unambig`."
  , ""
  , "    `unambig` lives here (not in `…Complete`) so the two `native_decide`"
  , "    sibling modules build in parallel. -/"
  , ""
  , "namespace " ++ umbrellaMod
  , ""
  , "open LeanMenhir"
  , ""
  , "/-- Unambiguity, specialised to this grammar's `safe`/`complete`."
  , "    Given a token, an initial state, a word and two parse trees of"
  , "    the same word, their semantic values are equal.  No further"
  , "    `decide`/`native_decide` is required — this is a pure consequence"
  , "    of `LeanMenhir.Main.parse_complete`."
  , ""
  , "    (`def` rather than `theorem` so we can omit the (long, universally-"
  , "    quantified) signature and let Lean infer it from the body.) -/"
  , "def unambig := Main.unambiguity " ++ umbrellaMod ++ ".safe "
                                      ++ umbrellaMod ++ ".complete"
  , ""
  , "end " ++ umbrellaMod
  ]

----------------------------------------------------------------------------
-- Per-module headers
----------------------------------------------------------------------------

-- | Header for @Par<LANG>Tables.lean@.  This is the only module that
--   pays the @maxRecDepth@/@maxHeartbeats@ cost — the others build
--   fast against the precompiled olean.  All defs land in the umbrella
--   namespace (e.g. @ParCalc@), not a per-file namespace.
tablesHeader :: String -> String -> String -> String -> [String]
tablesHeader _tablesMod nsMod absMod runtimeMod =
  [ "import " ++ absMod
  , "import " ++ runtimeMod
  , "import LeanMenhir.Runtime"
  , "import LeanMenhir.Generator.BuildTables"
  , "import Mathlib.Data.Stream.Init"
  , ""
  , "/-! Parser tables and `automaton` instance generated by BNFC's"
  , "    `--leanmenhir` backend.  This module is the sequential bottleneck;"
  , "    the safety/completeness certificates live in sibling modules so"
  , "    Lake can build them in parallel against the precompiled olean. -/"
  , ""
  , "namespace " ++ nsMod
  , ""
  , "open LeanMenhir LeanMenhir.Gen"
  , "open " ++ absMod
  , ""
  , "set_option linter.unusedVariables false"
  , "-- `build_tables%` reifies the full SLR(1) tables as a literal `GenTables`"
  , "-- term; for non-trivial grammars this term is deep, so bump `maxRecDepth`."
  , "-- With LeanMenhir's `prodLhsFn`/`prodRhsRevFn` jump-trees (≥ f3715cea) the"
  , "-- `actions` dispatcher's per-arm dependent-type reduction is the binding"
  , "-- heartbeats consumer (~2–4 M for L0-sized grammars); 4 M is comfortable."
  , "set_option maxRecDepth 1048576"
  , "set_option maxHeartbeats 4000000"
  ]

-- | Header for @Par<LANG>Safe.lean@.
safeHeader :: String -> String -> String -> String -> String -> [String]
safeHeader tablesMod nsMod absMod lexMod runtimeMod =
  [ "import " ++ tablesMod
  , "import " ++ absMod    -- entry AST type for the `parse<Entry>` signature
  , "import " ++ lexMod    -- `tokenize` for `parse<Entry>`
  , "import " ++ runtimeMod
  , "import LeanMenhir.Runtime"
  , ""
  , "/-! Safety certificate for the LeanMenhir-generated parser, plus the"
  , "    lexer-token → grammar-terminal adapter and the user-facing"
  , "    `parse<Entry>` driver (which needs `safe` to feed into"
  , "    `LeanMenhir.Runtime.parseWith`). -/"
  , ""
  , "namespace " ++ nsMod   -- same namespace as Tables — shared umbrella
  , ""
  , "open LeanMenhir"
  , "open " ++ absMod
  ]

-- | Header for @Par<LANG>Complete.lean@.  Importantly does NOT import
--   the @…Safe@ module — that's what lets Lake build the two
--   @native_decide@ jobs in parallel.
completeHeader :: String -> String -> [String]
completeHeader tablesMod nsMod =
  [ "import " ++ tablesMod
  , "import LeanMenhir.Runtime"
  , ""
  , "/-! Completeness certificate for the LeanMenhir-generated parser."
  , "    Sibling of `Par<LANG>Safe`; the two `native_decide` jobs build"
  , "    concurrently because this module does NOT import `…Safe`. -/"
  , ""
  , "namespace " ++ nsMod
  , ""
  , "open LeanMenhir"
  ]

----------------------------------------------------------------------------
-- Numbering of terminals + nonterminals
----------------------------------------------------------------------------

-- | All the indexing data the emitter needs.
data Numbering = Numbering
  { gnEntry       :: Cat
      -- ^ User-declared entry category (its AST type is the result of
      --   @parse<Entry>@).
  , gnKeywords    :: [String]
      -- ^ Keyword/punctuation strings in index order (indices 0..k-1).
  , gnTokenCats   :: [TokenCat]
      -- ^ Token categories used by the grammar in index order
      --   (indices k+1..numTerm-1).  Index k is reserved for EOF.
  , gnKwIdx       :: Map String Int
  , gnTokIdx      :: Map TokenCat Int
  , gnEofIdx      :: Int
  , gnNumTerm     :: Int
      -- ^ Total number of real terminals (keywords + EOF + token cats).
  , gnNts         :: [Cat]
      -- ^ Non-start nonterminals in index order (indices 1..numNt-1).
      --   The synthesised @Start@ symbol is always index 0.
  , gnNtIdx       :: Map String Int
      -- ^ @catToStr c@ → its index (1..numNt-1 for real cats; the
      --   synthesised Start has no entry here, it is always 0).
  , gnNumNt       :: Int
      -- ^ Total number of nonterminals (1 for Start + real ones).
  }

-- | Build the deterministic numbering from the CF.
buildNumbering :: CF -> Numbering
buildNumbering cf =
    Numbering
      { gnEntry      = entry
      , gnKeywords   = keywords
      , gnTokenCats  = tokenCats
      , gnKwIdx      = Map.fromList (zip keywords [0..])
      , gnTokIdx     = tokIdxMap
      , gnEofIdx     = eofIdx
      , gnNumTerm    = numTerm
      , gnNts        = ntCats
      , gnNtIdx      = ntIdxMap
      , gnNumNt      = 1 + length ntCats
      }
  where
    entry  = firstEntry cf
    rules  = parsableRules cf

    -- ---- Keywords --------------------------------------------------------
    keywords =
      sort . dedup $ [ s | r <- rules, Right s <- rhsRule r ]

    -- ---- Token categories ------------------------------------------------
    tokenCats =
      sort . dedup $ [ t | r <- rules, c <- rhsCats r, TokenCat t <- [c] ]
      where
        rhsCats r = [ c | Left c <- rhsRule r ] ++ [valCat r]
        -- (The valCat shouldn't be a TokenCat for a parsable rule, but
        -- it's harmless to include.)

    eofIdx  = length keywords
    tokIdxMap =
      Map.fromList (zip tokenCats [eofIdx + 1 ..])
    numTerm = eofIdx + 1 + length tokenCats

    -- ---- Nonterminals ----------------------------------------------------
    -- Every Cat / CoercCat / ListCat reachable from a parsable rule's
    -- LHS or RHS (excluding TokenCats, which are terminals).
    ntCats0 =
      [ c | r <- rules
          , c <- valCat r : [c' | Left c' <- rhsRule r]
          , not (isTokenCat c) ]
    ntCats = sortBy (\a b -> compare (catToStr a) (catToStr b)) (dedupBy catToStr ntCats0)
    ntIdxMap =
      Map.fromList [ (catToStr c, i) | (c, i) <- zip ntCats [1..] ]

-- | The CF rules we actually emit productions for: parsable, not
--   user-defined macros (lower-case @defFun@ labels).
parsableRules :: CF -> [Rule]
parsableRules cf =
  [ r | r <- cfgRules cf, isParsable r, not (isDefinedRule (funRule r)) ]

----------------------------------------------------------------------------
-- Productions
----------------------------------------------------------------------------

-- | One production we emit (both into @Grammar0.prods@ and into the
--   typed @actions@ dispatcher).
data Production
  = -- | The synthesised start production @Start → Entry EOF@.  Its
    --   action just unwraps the entry value.
    StartProd
      { prodEntryNt :: Int
        -- ^ Nonterm index of the user entry category.
      , prodEofIx   :: Int
        -- ^ Terminal index of EOF.
      , prodEntryTy :: String
        -- ^ Lean type expression for the entry's AST type.
      }
    -- | A user rule promoted to a production.  The @prodRhs@ list is in
    --   FORWARD order (this is what @Grammar0@ wants).  The reversed
    --   form is computed at action-emission time.
  | UserProd
      { prodLhsIdx :: Int
        -- ^ Nonterm index of @valCat r@.
      , prodRhs    :: [Either Cat String]
      , prodRule   :: Rule
      }

-- | Build the Start production.
startProd :: Numbering -> Production
startProd gn = StartProd
  { prodEntryNt = lookupNt gn (gnEntry gn)
  , prodEofIx   = gnEofIdx gn
  , prodEntryTy = catToLeanType (gnEntry gn)
  }

-- | Build a user production from a CF rule.
toUserProd :: Numbering -> Rule -> Production
toUserProd gn r = UserProd
  { prodLhsIdx = lookupNt gn (valCat r)
  , prodRhs    = rhsRule r
  , prodRule   = r
  }

----------------------------------------------------------------------------
-- Grammar block
----------------------------------------------------------------------------

grammarBlock :: Numbering -> [Production] -> [String]
grammarBlock gn ps =
  [ "/-! ### Grammar (forward-order productions; bridge reverses them internally). -/"
  , ""
  , "def grammar : Grammar0 where"
  , "  numTerm := " ++ show (gnNumTerm gn)
  , "  numNonterm := " ++ show (gnNumNt gn)
  , "  start := 0"
  , "  eof := " ++ show (gnEofIdx gn)
  , "  prods := #["
  ] ++ withTrailingCommas (map (prodLine gn) ps) ++ [ "  ]" ]

-- | Add trailing commas to all elements except the last.  The element
--   text may include an end-of-line @--@ comment; the comma is inserted
--   BEFORE the comment (and any preceding whitespace) so the array
--   literal stays well-formed.
withTrailingCommas :: [String] -> [String]
withTrailingCommas []     = []
withTrailingCommas [x]    = [x]
withTrailingCommas (x:xs) = appendCommaBeforeComment x : withTrailingCommas xs

appendCommaBeforeComment :: String -> String
appendCommaBeforeComment s =
  case splitOnComment s of
    (pre, "") -> pre ++ ","
    (pre, cs) -> trimEnd pre ++ "," ++ "   " ++ cs

-- | Split a line at the first @--@ that starts a comment, returning
--   the code portion and the comment portion (the @--@ itself stays
--   in the comment portion).
splitOnComment :: String -> (String, String)
splitOnComment = go []
  where
    go acc ('-' : '-' : rest) = (reverse acc, "--" ++ rest)
    go acc (c : rest)         = go (c : acc) rest
    go acc []                 = (reverse acc, "")

trimEnd :: String -> String
trimEnd = reverse . dropWhile (== ' ') . reverse

prodLine :: Numbering -> Production -> String
prodLine _gn (StartProd ent eof _) =
  "    (0, #[.nonterm " ++ show ent
    ++ ", .term " ++ show eof ++ "])   -- Start → Entry EOF"
prodLine gn (UserProd lhs rhs r) =
  let syms = intercalate ", " (map (rhsSymToLean gn) rhs)
  in "    (" ++ show lhs ++ ", #[" ++ syms ++ "])"
       ++ "   -- " ++ prodComment r

prodComment :: Rule -> String
prodComment r =
  let label = funName (funRule r)
  in label ++ ". " ++ show (valCat r) ++ " ::= "
       ++ unwords (map showItem (rhsRule r))
  where
    showItem (Left c)  = show c
    showItem (Right s) = show s   -- shown with quotes

rhsSymToLean :: Numbering -> Either Cat String -> String
rhsSymToLean gn = \case
  Left (TokenCat t) ->
    ".term " ++ show (lookupTok gn t)
  Left c ->
    ".nonterm " ++ show (lookupNt gn c)
  Right s ->
    ".term " ++ show (lookupKw gn s)

----------------------------------------------------------------------------
-- Tables block
----------------------------------------------------------------------------

tablesDefBlock :: [String]
tablesDefBlock =
  [ "/-! ### Tables (SLR(1), generated at elaboration time by `build_tables%`). -/"
  , ""
  , "def tables : GenTables := build_tables% grammar"
  ]

----------------------------------------------------------------------------
-- ntType / termType
----------------------------------------------------------------------------

ntTypeBlock :: Numbering -> [String]
ntTypeBlock gn =
  [ "/-! ### Heterogeneous semantic types -/"
  , ""
  , "def ntType : Fin (tables.numNonterm + 1) → Type"
  , "  | 0 => " ++ entryLean   -- Start carries the entry's AST type
  ] ++ map renderNt (zip [1 :: Int ..] (gnNts gn))
    ++ [ "  | _ => Unit   -- dummy nonterminal index = numNonterm" ]
  where
    entryLean = catToLeanType (gnEntry gn)
    renderNt (i, c) =
      "  | " ++ show i ++ " => " ++ catToLeanType c
        ++ "   -- " ++ catToStr c

termTypeBlock :: Numbering -> [String]
termTypeBlock gn =
  [ "def termType : Fin (tables.numTerm + 1) → Type"
  ] ++ map renderTok (Map.toAscList (gnTokIdx gn))
    ++ [ "  | _ => Unit   -- keywords, EOF, padding dummy" ]
  where
    renderTok (cat, i) =
      "  | " ++ show i ++ " => " ++ termTypeFor cat
        ++ "   -- " ++ cat

-- | The Lean type the lexer hands the parser for a given token category.
termTypeFor :: TokenCat -> String
termTypeFor "Integer" = "Int"
termTypeFor "Double"  = "Float"
termTypeFor "Char"    = "Char"
termTypeFor "String"  = "String"
termTypeFor _         = "String"   -- Ident, user tokens

----------------------------------------------------------------------------
-- Actions
----------------------------------------------------------------------------

actionsBlock :: Numbering -> [Production] -> [String]
actionsBlock gn ps =
  [ "/-! ### Typed semantic actions (arguments in reverse-RHS order). -/"
  , ""
  , "def actions : (p : Fin (tables.numProd + 1)) →"
  , "    arrowsRight (symTypeOf tables ntType termType (.NT (prodLhsOf tables p)))"
  , "                ((prodRhsRevOf tables p).map (symTypeOf tables ntType termType))"
  ] ++ zipWith renderAction [0..] ps
    ++ [ "  | " ++ show (length ps) ++ " => ()   -- dummy padding production"
       , "  | ⟨_ + " ++ show (length ps + 1) ++ ", h⟩ => elimOutOfRange h"
         ++ "   -- exhaustiveness shim (Lean's equation compiler doesn't"
         ++ " prove `Fin n` literal matches complete past ~15 arms; see"
         ++ " LeanMenhir.Gen.elimOutOfRange)"
       ]
  where
    renderAction i p =
      "  | " ++ show i ++ " => " ++ actionBody gn p
        ++ commentFor p
    commentFor (StartProd _ _ _)            = "   -- Start → Entry EOF"
    commentFor (UserProd _ _ r)             = "   -- " ++ prodComment r

-- | Render the lambda for one production.  The lambda binds arguments
--   in the order they appear in @prodRhsRev@ (i.e. reversed forward
--   RHS); the constructor is applied to non-keyword arguments in their
--   ORIGINAL forward order.
actionBody :: Numbering -> Production -> String
actionBody _gn (StartProd _ent _eof entryTy) =
  -- Reversed RHS for Start is [.term EOF, .nonterm Entry], so:
  "fun (_ : Unit) (e : " ++ entryTy ++ ") => e"

actionBody gn (UserProd _lhs rhs r) =
  let
    -- Number forward items 1..n.
    indexed :: [(Int, Either Cat String)]
    indexed = zip [1..] rhs

    -- Reversed (action arg order).
    revIndexed = reverse indexed

    binders :: [String]
    binders = map (renderBinder gn) revIndexed

    body :: String
    body = renderBody gn (funRule r) (valCat r) indexed
  in
    case binders of
      -- Zero-arg production (e.g. `[]. [C] ::= ;`): the action type
      -- reduces to a plain value, not a function — emit the body raw.
      [] -> body
      _  -> "fun" ++ concatMap (" " ++) binders ++ " => " ++ body

renderBinder :: Numbering -> (Int, Either Cat String) -> String
renderBinder _gn (_, Right _) =
  "(_ : Unit)"
renderBinder _gn (i, Left (TokenCat t)) =
  "(a" ++ show i ++ " : " ++ termTypeFor t ++ ")"
renderBinder _gn (i, Left c) =
  "(a" ++ show i ++ " : " ++ catToLeanType c ++ ")"

-- | Render the body of an action given the (forward-ordered, 1-indexed)
--   RHS items and the rule's function/category.
renderBody :: Numbering -> RFun -> Cat -> [(Int, Either Cat String)] -> String
renderBody _gn f cat indexed
  | isNilFun f = "[]"
  | isOneFun f =
      case nonKwArgs indexed of
        [n] -> "[a" ++ show n ++ "]"
        _   -> "[]   -- malformed singleton list rule"
  | isConsFun f =
      case nonKwArgs indexed of
        [hd, tl] -> "a" ++ show hd ++ " :: a" ++ show tl
        _        -> "[]   -- malformed cons list rule"
  | isCoercion f =
      case nonKwArgs indexed of
        [n] -> "a" ++ show n
        _   -> "()   -- malformed coercion (need exactly 1 non-keyword arg)"
  | otherwise =
      -- Ordinary labelled rule:
      let ctor = sanitizeLeanUpper (catToStr (normCat cat))
                   ++ "." ++ constructorName (funName f)
          args = nonKwArgs indexed
      in case args of
           [] -> ctor
           _  -> ctor ++ concat [ " a" ++ show n | n <- args ]

-- | The 1-indexed forward positions of non-keyword RHS items.
nonKwArgs :: [(Int, Either Cat String)] -> [Int]
nonKwArgs = mapMaybe $ \case
  (i, Left _)  -> Just i
  (_, Right _) -> Nothing

----------------------------------------------------------------------------
-- Automaton + certificates
----------------------------------------------------------------------------

automatonBlock :: [String]
automatonBlock =
  [ "/-! ### Automaton instance (no certificates yet — those live in the"
  , "    sibling `…Safe` and `…Complete` modules so Lake can build them in"
  , "    parallel). -/"
  , ""
  , "/-- Tokens carry a `BNFC.Position` (used only for error reporting). -/"
  , "instance automaton : Automaton :="
  , "  automatonOfTablesTyped tables ntType termType BNFC.Position actions"
  ]

----------------------------------------------------------------------------
-- Per-cert blocks (live in the Safe / Complete modules)
----------------------------------------------------------------------------

-- | The safety cert, emitted into the @Safe@ module.
safeCertBlock :: [String]
safeCertBlock =
  [ "/-! ### Safety certificate."
  , ""
  , "    `native_decide` compiles `Main.safeValidator (A := automaton) ()` to"
  , "    native code and runs it.  The validator is a pure boolean function over"
  , "    the closed `tables` literal; its result extends the trust base by the"
  , "    standard `_native_decide_*` compiler-trust axiom (a per-theorem version"
  , "    of `Lean.ofReduceBool`).  Kernel `decide` is sound but currently"
  , "    infeasible at BNFC-grammar scale (the 480-state L0 automaton did not"
  , "    finish in 10+ min of kernel reduction); LeanMenhir keeps an experimental"
  , "    `BTree`-data + `rfl` route should a kernel-only trust story ever be"
  , "    needed. -/"
  , ""
  , "theorem safe : Main.safeValidator (A := automaton) () = true := by native_decide"
  ]

-- | The completeness cert, emitted into the @Complete@ module.  The
--   unambiguity specialisation lives in the umbrella module instead,
--   so that this module need not import @…Safe@.
completeCertBlock :: [String]
completeCertBlock =
  [ "/-! ### Completeness certificate."
  , ""
  , "    Like `safe`, `complete` is discharged by `native_decide`.  Once"
  , "    both certs are in scope, `LeanMenhir.Main.unambiguity` gives us"
  , "    that any two parse trees of the same word have the same semantic"
  , "    value — see `<umbrella>.unambig`.  No additional `decide` is"
  , "    required for unambiguity; it is a downstream theorem. -/"
  , ""
  , "theorem complete : Main.completeValidator (A := automaton) () = true := by native_decide"
  ]

----------------------------------------------------------------------------
-- Adapter: BNFC.Token → automaton.Token
----------------------------------------------------------------------------

adapterBlock :: Numbering -> [String]
adapterBlock gn =
  [ "/-! ### Lexer-token → grammar-terminal adapter. -/"
  , ""
  , "abbrev Tok : Type := automaton.Token"
  , ""
  , "def adapt : BNFC.Token → Except String Tok"
  ] ++ map tokenCatArm (gnTokenCats gn)
    ++ map keywordArm (gnKeywords gn)
    ++ [ "  | { kind := k, pos := pos } =>"
       , "      .error s!\"{pos}: unexpected token {repr k}\""
       , ""
       , "def eofAt (p : BNFC.Position) : Tok := (p, ⟨" ++ show (gnEofIdx gn) ++ ", ()⟩)"
       ]
  where
    keywordArm s =
      "  | { kind := .keyword " ++ show s ++ ", pos } => .ok (pos, ⟨"
        ++ show (lookupKw gn s) ++ ", ()⟩)"

    tokenCatArm cat =
      let i = lookupTok gn cat
          (pat, payload) = tokenCatPat cat
      in "  | { kind := " ++ pat ++ ", pos } => .ok (pos, ⟨"
           ++ show i ++ ", " ++ payload ++ "⟩)"

-- | Map a token category to the lexer pattern that produces it plus
--   the payload expression for the @Σ@-pair.
tokenCatPat :: TokenCat -> (String, String)
tokenCatPat "Integer" = (".intLit n",        "(n : Int)")
tokenCatPat "Double"  = (".floatLit x",      "(x : Float)")
tokenCatPat "Char"    = (".charLit c",       "(c : Char)")
tokenCatPat "String"  = (".strLit s",        "(s : String)")
tokenCatPat "Ident"   = (".ident s",         "(s : String)")
tokenCatPat cat       =
  -- User-defined token category.  The lexer's `userTok` constructor
  -- carries both the category name and the lexeme.
  (".userTok " ++ show cat ++ " s", "(s : String)")

----------------------------------------------------------------------------
-- Entry point: parse<Entry>
----------------------------------------------------------------------------

parseEntryBlock :: Numbering -> String -> [String]
parseEntryBlock gn lexMod =
  [ "/-! ### Top-level entrypoint matching BNFC's test driver signature. -/"
  , ""
  , "def " ++ parseName ++ " (input : String) : Except String " ++ entryTy ++ " :="
  , "  match " ++ lexMod ++ ".tokenize input with"
  , "  | .error e => .error (toString e)"
  , "  | .ok toks =>"
  , "    let endPos : BNFC.Position :="
  , "      match toks.reverse with"
  , "      | [] => { line := 1, col := 1 }"
  , "      | t :: _ => t.pos"
  , "    LeanMenhir.Runtime.parseWith (A := automaton) (0 : Fin 1) safe"
  , "      (eofAt endPos) adapt"
  , "      (fun _ tok => s!\"{(tok.1 : BNFC.Position)}: syntax error\")"
  , "      \"input too large\" toks"
  ]
  where
    parseName = "parse" ++ identCat (gnEntry gn)
    entryTy   = catToLeanType (gnEntry gn)

----------------------------------------------------------------------------
-- Helpers
----------------------------------------------------------------------------

lookupKw :: Numbering -> String -> Int
lookupKw gn s = case Map.lookup s (gnKwIdx gn) of
  Just i  -> i
  Nothing -> error $ "cf2LeanMenhirPar: missing keyword index for " ++ show s

lookupTok :: Numbering -> TokenCat -> Int
lookupTok gn t = case Map.lookup t (gnTokIdx gn) of
  Just i  -> i
  Nothing -> error $ "cf2LeanMenhirPar: missing token-cat index for " ++ show t

lookupNt :: Numbering -> Cat -> Int
lookupNt gn c = case Map.lookup (catToStr c) (gnNtIdx gn) of
  Just i  -> i
  Nothing -> error $ "cf2LeanMenhirPar: missing nonterm index for " ++ show c

dedup :: Eq a => [a] -> [a]
dedup = foldr (\x acc -> if x `elem` acc then acc else x : acc) []

dedupBy :: Eq b => (a -> b) -> [a] -> [a]
dedupBy f = go []
  where
    go _ []     = []
    go seen (x:xs)
      | f x `elem` seen = go seen xs
      | otherwise       = x : go (f x : seen) xs
