{-# LANGUAGE LambdaCase #-}

{- |
Module      : BNFC.Backend.Lean.CFtoLeanPrinter
Description : Generate a Lean 4 pretty-printer for the abstract syntax.

The printer produces an @IO@-free pure-`String` result.  Each category
gets a function `prCat : C → String`; inside a `mutual` block they may
recurse freely.  Sub-expressions of higher precedence are printed with
parentheses when they would otherwise be ambiguous.
-}

module BNFC.Backend.Lean.CFtoLeanPrinter ( cf2Printer ) where

import BNFC.CF
import BNFC.Backend.Lean.LeanUtil

cf2Printer :: String -> String -> CF -> String
cf2Printer modName absMod cf = unlines $ concat
  [ header
  , [ "" ]
  , [ "/-- Render an `Int` as decimal text. -/"
    , "def prInt (n : Int) : String := toString n"
    , "/-- Render a `Float` literal. -/"
    , "def prFloat (x : Float) : String := toString x"
    , "/-- Render a `String` literal with surrounding double quotes. -/"
    , "def prString (s : String) : String := \"\\\"\" ++ s ++ \"\\\"\""
    , "/-- Render a `Char` literal with surrounding single quotes. -/"
    , "def prChar (c : Char) : String := \"'\" ++ c.toString ++ \"'\""
    , "/-- Render a token category alias (`Ident` etc.). -/"
    , "def prToken (s : String) : String := s"
    , ""
    ]
  , [ "mutual" ]
  , concatMap printerFor dataCats
  , listPrinters
  , [ "end" ]
  , [ "" ]
  , [ "/-- Render a list of pretty-printed elements separated by spaces. -/"
    , "def prSep (sep : String) (xs : List String) : String :="
    , "  String.intercalate sep xs"
    , ""
    ]
  , [ ""
    , "/-- Top-level pretty-printer for the first entry point. -/"
    , "def printTree : " ++ catToLeanType firstE ++ " → String :="
    , "  " ++ printerName firstE
    , ""
    , "end " ++ modName
    ]
  ]
  where
    header =
      [ "import " ++ absMod
      , ""
      , "/-! Pretty-printer.  Produces a single-line `String` representation"
      , "    of any AST node.  No layout/indentation logic is applied;"
      , "    customise `prSep` if you need richer output. -/"
      , ""
      , "namespace " ++ modName
      , "open " ++ absMod
      , ""
      ]
    firstE = firstEntry cf
    dataCats = filter (not . null . snd) (cf2data cf)

    printerFor :: Data -> [String]
    printerFor (cat, ctors) =
      let typeName = sanitizeLeanUpper (catToStr (normCat cat))
          fnName = printerName cat
      in concat
         [ [ "  /-- Pretty-printer for `" ++ typeName ++ "`. -/"
           , "  partial def " ++ fnName ++ " : " ++ typeName ++ " → String"
           ]
         , map (renderArm cat typeName) ctors
         ]

    renderArm :: Cat -> String -> (Fun, [Cat]) -> String
    renderArm _cat typeName (fun, args) =
      let ctor = typeName ++ "." ++ constructorName fun
          (pat, body) = mkArm ctor fun args
      in "    | " ++ pat ++ " => " ++ body

    -- Build a pattern and pretty-print body.  We don't yet know the
    -- positional symbols for this rule (they live in `cfgRules`), so
    -- look them up.
    mkArm :: String -> Fun -> [Cat] -> (String, String)
    mkArm ctor fun args =
      let pat = ctor ++ concat [ " a" ++ show i | i <- [1 .. length args] ]
          rule = lookupParseRule fun cf
          rhs  = case rule of
                   Just r  -> rhsRule r
                   Nothing -> map Left args   -- fallback
          body = renderRhs args rhs
      in (pat, body)

    renderRhs :: [Cat] -> SentForm -> String
    renderRhs args items =
      let parts = renderParts 1 args items
      in case parts of
           []   -> "\"\""
           [p]  -> p
           _    -> "String.intercalate \" \" [" ++ commaSep parts ++ "]"

    renderParts :: Int -> [Cat] -> SentForm -> [String]
    renderParts _   _    []                  = []
    renderParts idx (a:as) (Left _ : rest)   =
      let arg = "a" ++ show idx
          call = case a of
            TokenCat "Integer" -> "prInt " ++ arg
            TokenCat "Double"  -> "prFloat " ++ arg
            TokenCat "String"  -> "prString " ++ arg
            TokenCat "Char"    -> "prChar " ++ arg
            TokenCat _         -> "prToken " ++ arg
            ListCat inner      -> "(" ++ printerName (ListCat inner) ++ " " ++ arg ++ ")"
            _                  -> printerName a ++ " " ++ arg
      in call : renderParts (idx + 1) as rest
    renderParts _idx [] (Left _ : rest)      =
      "\"<arg?>\"" : renderParts _idx [] rest
    renderParts idx args' (Right sym : rest) =
      ("\"" ++ escape sym ++ "\"") : renderParts idx args' rest

    listPrinters :: [String]
    listPrinters = concatMap renderListPr listCats

    listCats :: [Cat]
    listCats =
      let inner = [ c | (_, ctors) <- dataCats
                      , (_, args) <- ctors
                      , a <- args
                      , ListCat c <- [a]
                      ]
      in dedupCats (map ListCat inner)

    dedupCats :: [Cat] -> [Cat]
    dedupCats = go []
      where
        go acc [] = reverse acc
        go acc (x:xs)
          | any (\y -> catToStr x == catToStr y) acc = go acc xs
          | otherwise = go (x : acc) xs

    renderListPr :: Cat -> [String]
    renderListPr lc@(ListCat inner) =
      let separator = lookupListSeparator cf inner
          fn = printerName lc
          innerCall = case inner of
            TokenCat "Integer" -> "prInt"
            TokenCat "Double"  -> "prFloat"
            TokenCat "String"  -> "prString"
            TokenCat "Char"    -> "prChar"
            TokenCat _         -> "prToken"
            _                  -> printerName inner
      in [ "  /-- Pretty-printer for `[" ++ catToStr inner ++ "]`. -/"
         , "  partial def " ++ fn ++ " (xs : List " ++ catToLeanType inner ++ ") : String :="
         , "    String.intercalate " ++ show separator ++ " (xs.map " ++ innerCall ++ ")"
         ]
    renderListPr _ = []

    escape :: String -> String
    escape = concatMap (\c -> if c == '"' || c == '\\' then ['\\', c] else [c])

    commaSep :: [String] -> String
    commaSep = go
      where
        go []     = ""
        go [x]    = x
        go (x:xs) = x ++ ", " ++ go xs

----------------------------------------------------------------------------
-- Helpers
----------------------------------------------------------------------------

-- | Find the canonical parsable rule for a constructor, if any.
lookupParseRule :: Fun -> CF -> Maybe Rule
lookupParseRule f cf =
  case [ r | r <- cfgRules cf
           , isParsable r
           , funName (funRule r) == f
           ] of
    (r:_) -> Just r
    []    -> Nothing

-- | Best-effort look up of a separator for `[C]`.  Returns " " if none found.
lookupListSeparator :: CF -> Cat -> String
lookupListSeparator cf inner =
  case [ s | r <- rulesForCat cf (ListCat inner)
           , isConsFun (funRule r)
           , [Left _, Right s, Left _] <- [rhsRule r]
       ] of
    (s:_) -> if null s then " " else s
    []    -> " "
