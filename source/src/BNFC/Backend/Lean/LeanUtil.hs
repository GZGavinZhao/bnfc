{-# LANGUAGE LambdaCase #-}

{- |
Module      : BNFC.Backend.Lean.LeanUtil
Description : Common utilities for the Lean 4 backend.

File-naming conventions, identifier sanitisation and a list of Lean reserved
words.  The naming scheme mirrors @BNFC.Backend.Haskell.HsOpts@ so that the
Lean backend supports @--outputdir@ and the standard 'lang'-suffix convention.
-}

module BNFC.Backend.Lean.LeanUtil
  ( -- * File names
    absLeanFile, absLeanModule
  , lexLeanFile, lexLeanModule
  , parLeanFile, parLeanModule
    -- ** Split-parser modules (used only by the LeanMenhir backend, but live
    --    here so the path/module conventions stay in one place).
  , parTablesLeanFile, parTablesLeanModule
  , parSafeLeanFile,   parSafeLeanModule
  , parCompleteLeanFile, parCompleteLeanModule
  , printLeanFile, printLeanModule
  , skelLeanFile, skelLeanModule
  , testLeanFile, testLeanModule
  , runtimeLeanFile, runtimeLeanModule
  , lakeFile, leanToolchainFile
    -- * Identifiers
  , leanReserved
  , sanitizeLeanLower
  , sanitizeLeanUpper
  , catToLeanType
  , constructorName
  , ctorRefName
  , parserName
  , printerName
    -- * Misc
  , leanComment
  ) where

import Data.Char    ( toLower, toUpper )

import BNFC.CF
import BNFC.Options ( SharedOptions(..) )

----------------------------------------------------------------------------
-- File and module names
----------------------------------------------------------------------------

-- | Capitalize the first character.
cap :: String -> String
cap []     = []
cap (c:cs) = toUpper c : cs

-- | Append the language name (CamelCase).
withLang :: SharedOptions -> String -> String
withLang opts base = base ++ cap (lang opts)

absLeanModule, lexLeanModule, parLeanModule,
  parTablesLeanModule, parSafeLeanModule, parCompleteLeanModule,
  printLeanModule, skelLeanModule, testLeanModule,
  runtimeLeanModule :: SharedOptions -> String
absLeanModule         = (`withLang` "Abs")
lexLeanModule         = (`withLang` "Lex")
parLeanModule         = (`withLang` "Par")
-- Note: these read as @ParCalcTables@ / @ParCalcSafe@ / @ParCalcComplete@
-- (i.e. @Par<LANG><Suffix>@) — using the @parLeanModule@ name plus a
-- direct suffix so the language sits in the middle, not at the end.
parTablesLeanModule   opts = parLeanModule opts ++ "Tables"
parSafeLeanModule     opts = parLeanModule opts ++ "Safe"
parCompleteLeanModule opts = parLeanModule opts ++ "Complete"
printLeanModule       = (`withLang` "Print")
skelLeanModule        = (`withLang` "Skel")
testLeanModule        = (`withLang` "Test")
runtimeLeanModule     = const "ParserRuntime"

absLeanFile, lexLeanFile, parLeanFile,
  parTablesLeanFile, parSafeLeanFile, parCompleteLeanFile,
  printLeanFile, skelLeanFile, testLeanFile,
  runtimeLeanFile :: SharedOptions -> FilePath
absLeanFile         opts = absLeanModule         opts ++ ".lean"
lexLeanFile         opts = lexLeanModule         opts ++ ".lean"
parLeanFile         opts = parLeanModule         opts ++ ".lean"
parTablesLeanFile   opts = parTablesLeanModule   opts ++ ".lean"
parSafeLeanFile     opts = parSafeLeanModule     opts ++ ".lean"
parCompleteLeanFile opts = parCompleteLeanModule opts ++ ".lean"
printLeanFile       opts = printLeanModule       opts ++ ".lean"
skelLeanFile        opts = skelLeanModule        opts ++ ".lean"
testLeanFile        opts = testLeanModule        opts ++ ".lean"
runtimeLeanFile     opts = runtimeLeanModule     opts ++ ".lean"

-- | Path of @lakefile.toml@ (relative to the output dir).
lakeFile :: FilePath
lakeFile = "lakefile.toml"

-- | Path of the Lean toolchain pin.
leanToolchainFile :: FilePath
leanToolchainFile = "lean-toolchain"

----------------------------------------------------------------------------
-- Reserved word handling
----------------------------------------------------------------------------

-- | A conservative list of Lean 4 reserved words and built-ins.
--   It is intentionally large: extra escapes never hurt, but missing ones
--   yield syntax errors in user output.
leanReserved :: [String]
leanReserved =
  [ "abbrev", "and", "as", "axiom", "begin", "by", "class", "constant"
  , "deriving", "def", "do", "else", "end", "example", "exists", "export"
  , "extends", "false", "for", "from", "fun", "have", "hiding"
  , "if", "import", "in", "include", "inductive", "infix", "infixl", "infixr"
  , "instance", "is", "lemma", "let", "macro", "match", "match_syntax"
  , "meta", "mut", "mutual", "namespace", "noncomputable", "not", "notation"
  , "of", "omit", "open", "or", "partial", "postfix", "prefix", "private"
  , "protected", "renaming", "return", "section", "set_option", "show"
  , "structure", "syntax", "the", "then", "theorem", "this", "true", "try"
  , "type", "universe", "universes", "unsafe", "using", "variable", "variables"
  , "where", "while", "with"
  -- Built-in types and constructors that we want to avoid clashing with.
  , "Bool", "Char", "Float", "Int", "List", "Nat", "Option", "String"
  , "Array", "Prop", "Type", "Unit", "Sort", "Function", "Except"
  , "True", "False"
  -- Common operations from Init that show up frequently.
  , "id", "fst", "snd", "head", "tail", "map", "filter", "foldr", "foldl"
  ]

-- | Make a name safe by suffixing if it clashes with a Lean reserved word.
escape :: String -> String
escape s
  | s `elem` leanReserved = s ++ "_"
  | otherwise             = s

-- | Lower-case identifier, e.g. for variables and parser/printer functions.
sanitizeLeanLower :: String -> String
sanitizeLeanLower = escape . toLowerFirst . map underscoreToCamel . onlyAlphaNumUnder
  where
    onlyAlphaNumUnder = map (\c -> if c == '\'' then 'P' else c)
    underscoreToCamel = id  -- reserve real camel-casing for sanitizeLeanUpper
    toLowerFirst []     = []
    toLowerFirst (c:cs) = toLower c : cs

-- | Upper-case identifier, e.g. for type and constructor names.
sanitizeLeanUpper :: String -> String
sanitizeLeanUpper = escape . cap . map (\c -> if c == '\'' then 'P' else c)

----------------------------------------------------------------------------
-- Cat → Lean type
----------------------------------------------------------------------------

-- | Render a category as a Lean type expression.  Coerced (numbered)
--   categories are normalised away (`Exp1` → `Exp`) since at the AST level
--   precedence is irrelevant.
catToLeanType :: Cat -> String
catToLeanType c = case normCat c of
  ListCat c' -> "List " ++ parens (catToLeanType c')
  TokenCat t -> tokenCatToLean t
  Cat s      -> sanitizeLeanUpper s
  CoercCat s _ -> sanitizeLeanUpper s   -- shouldn't reach here after normCat
  where
    parens s = "(" ++ s ++ ")"

-- | Built-in token categories map to native Lean types where possible.
--   Token data is otherwise represented as @String@.
tokenCatToLean :: TokenCat -> String
tokenCatToLean = \case
  "Integer" -> "Int"
  "Double"  -> "Float"
  "Char"    -> "Char"
  "String"  -> "String"
  cat       -> sanitizeLeanUpper cat

-- | Constructor name as it appears in the inductive declaration (without the
--   @Cat.@ qualifier).
constructorName :: Fun -> String
constructorName = sanitizeLeanUpper

-- | Fully qualified constructor reference @Cat.Ctor@.
ctorRefName :: Cat -> Fun -> String
ctorRefName c f = sanitizeLeanUpper (catToStr (normCat c)) ++ "." ++ constructorName f

-- | Parser function name for a category.
parserName :: Cat -> String
parserName c = "p" ++ identCat (normCat c)

-- | Printer function name for a category.
printerName :: Cat -> String
printerName c = "pr" ++ identCat (normCat c)

----------------------------------------------------------------------------

-- | Lean comment prefix used by 'mkfile'.
leanComment :: String -> String
leanComment = ("-- " ++)
