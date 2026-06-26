{-# LANGUAGE LambdaCase #-}

{- |
Module      : BNFC.Backend.Lean.CFtoLeanLex
Description : Generate a hand-rolled longest-match lexer in Lean 4.

Strategy:

  * Convert the input @String@ to a @List Char@ once (this avoids
    relying on the rapidly-evolving @String.Pos@ / @String.Iterator@
    APIs and makes termination obvious).
  * Skip whitespace and BNFC-defined comments at every step.
  * For each step, try in order:
      1. integer / float literals;
      2. string and character literals;
      3. user-defined @token@ regex pragmas (longest match wins
         among them; reserved-word fallback when the matched lexeme
         is also a keyword);
      4. identifiers and reserved words (the latter take precedence);
      5. punctuation symbols (sorted by descending length).
  * If nothing matches, return a parse error with the offending position.

User-defined @token@ pragmas are compiled into closed @BNFC.Reg@
literals via the runtime's regex matcher
('BNFC.Backend.Lean.CFtoLeanRuntime.runtimeContent').  See the runtime
docstring for the matcher's semantics.
-}

module BNFC.Backend.Lean.CFtoLeanLex ( cf2Lex ) where

import Data.List ( sortBy )
import Data.Ord  ( Down(..), comparing )

import BNFC.Abs  ( Reg(..) )
import BNFC.CF
import BNFC.Backend.Lean.LeanUtil ()

cf2Lex :: String -> String -> CF -> String
cf2Lex modName runtimeMod cf = unlines $ concat
  [ [ "import " ++ runtimeMod
    , ""
    , "/-! Hand-rolled longest-match lexer.  Token kinds are defined in"
    , "    `" ++ runtimeMod ++ "`. -/"
    , ""
    , "namespace " ++ modName
    , "open BNFC"
    , ""
    , "set_option linter.unusedVariables false"
    , ""
    ]
  , [ literalsBlock keywords sortedSymbols ]
  , [ "" ]
  , [ commentDataBlock blockComments lineComments ]
  , [ "" ]
  , [ userTokensBlock userTokens ]
  , [ "" ]
  , [ helpersBlock ]
  , [ "" ]
  , [ tokenizeBlock ]
  , [ ""
    , "end " ++ modName
    ]
  ]
  where
    (blockComments, lineComments) = comments cf
    keywords      = reservedWords cf
    sortedSymbols = sortBy (comparing (Down . length)) (cfgSymbols cf)
    userTokens    = tokenPragmas cf

----------------------------------------------------------------------------
-- Static data
----------------------------------------------------------------------------

literalsBlock :: [String] -> [String] -> String
literalsBlock kws syms = unlines
  [ "/-- Reserved words declared by the grammar. -/"
  , "private def reserved : List String :="
  , "  " ++ leanList kws
  , ""
  , "/-- Punctuation symbols, sorted by descending length so that the"
  , "    longest match wins. -/"
  , "private def symbols : List String :="
  , "  " ++ leanList syms
  ]

commentDataBlock :: [(String, String)] -> [String] -> String
commentDataBlock blocks lines_ = unlines
  [ "/-- @comment Open Close@ pragmas as `(open, close)` pairs. -/"
  , "private def blockCommentMarkers : List (String × String) :="
  , "  " ++ leanList' (map renderPair blocks)
  , ""
  , "/-- @comment Marker@ pragmas: line comments starting with these. -/"
  , "private def lineCommentMarkers : List String :="
  , "  " ++ leanList lines_
  ]
  where
    renderPair (op, cl) = "(" ++ show op ++ ", " ++ show cl ++ ")"

----------------------------------------------------------------------------
-- Lexer helpers, working over `List Char`.
----------------------------------------------------------------------------

helpersBlock :: String
helpersBlock = unlines
  [ "/-- Bump the column counter, advancing line on `\\n`. -/"
  , "private def stepCol (p : BNFC.Position) (c : Char) : BNFC.Position :="
  , "  if c == '\\n' then { line := p.line + 1, col := 1 }"
  , "  else { p with col := p.col + 1 }"
  , ""
  , "/-- Match the literal `lit` (as `List Char`) at the head of `cs`."
  , "    Returns the rest of `cs` on success. -/"
  , "private def matchLitChars : List Char → List Char → Option (List Char)"
  , "  | [],         cs        => some cs"
  , "  | _ :: _,     []        => none"
  , "  | l :: ls,    c :: cs   => if l == c then matchLitChars ls cs else none"
  , ""
  , "private def matchLit (lit : String) (cs : List Char) : Option (List Char) :="
  , "  matchLitChars lit.toList cs"
  , ""
  , "/-- Advance the position cursor over `n` characters. -/"
  , "private def advanceN : List Char → BNFC.Position → Nat → BNFC.Position"
  , "  | _,        p, 0     => p"
  , "  | [],       p, _     => p"
  , "  | c :: cs,  p, n + 1 => advanceN cs (stepCol p c) n"
  , ""
  , "/-- Skip whitespace, line comments, and block comments. -/"
  , "private partial def skipWs (cs : List Char) (p : BNFC.Position)"
  , "    : List Char × BNFC.Position :="
  , "  match cs with"
  , "  | [] => (cs, p)"
  , "  | c :: rest =>"
  , "    if c.isWhitespace then skipWs rest (stepCol p c)"
  , "    else"
  , "      match tryLineComment lineCommentMarkers cs p with"
  , "      | some (cs', p') => skipWs cs' p'"
  , "      | none =>"
  , "        match tryBlockComment blockCommentMarkers cs p with"
  , "        | some (cs', p') => skipWs cs' p'"
  , "        | none           => (cs, p)"
  , "where"
  , "  tryLineComment : List String → List Char → BNFC.Position → Option (List Char × BNFC.Position)"
  , "    | [], _, _ => none"
  , "    | m :: ms, cs, p =>"
  , "        match matchLit m cs with"
  , "        | some cs' =>"
  , "            let p' := advanceN cs p m.length"
  , "            some (skipToNewline cs' p')"
  , "        | none     => tryLineComment ms cs p"
  , "  skipToNewline : List Char → BNFC.Position → List Char × BNFC.Position"
  , "    | [],        p => ([], p)"
  , "    | '\\n' :: rest, p => (rest, stepCol p '\\n')"
  , "    | c :: rest,    p => skipToNewline rest (stepCol p c)"
  , "  tryBlockComment : List (String × String) → List Char → BNFC.Position → Option (List Char × BNFC.Position)"
  , "    | [], _, _ => none"
  , "    | (op, cl) :: rest, cs, p =>"
  , "        match matchLit op cs with"
  , "        | some cs' =>"
  , "            let p' := advanceN cs p op.length"
  , "            some (skipToClose cl cs' p')"
  , "        | none     => tryBlockComment rest cs p"
  , "  skipToClose (cl : String) : List Char → BNFC.Position → List Char × BNFC.Position"
  , "    | [], p => ([], p)"
  , "    | cs, p =>"
  , "        match matchLit cl cs with"
  , "        | some cs' =>"
  , "            let p' := advanceN cs p cl.length"
  , "            (cs', p')"
  , "        | none =>"
  , "            match cs with"
  , "            | []        => ([], p)"
  , "            | c :: rest => skipToClose cl rest (stepCol p c)"
  , ""
  , "/-- Match a maximal `[A-Za-z_][A-Za-z0-9_']*`. -/"
  , "private def matchIdent : List Char → Option (String × List Char)"
  , "  | [] => none"
  , "  | c :: rest =>"
  , "      if c.isAlpha || c == '_' then"
  , "        let (lex, after) := scan rest [c]"
  , "        some (String.ofList lex, after)"
  , "      else none"
  , "where"
  , "  scan : List Char → List Char → List Char × List Char"
  , "    | [],        acc => (acc.reverse, [])"
  , "    | c :: rest, acc =>"
  , "        if c.isAlphanum || c == '_' || c == '\\'' then scan rest (c :: acc)"
  , "        else (acc.reverse, c :: rest)"
  , ""
  , "/-- Convert a `Nat` to `Float`, going through `UInt64` (which is the"
  , "    only natively-coerced numeric type in core Lean).  Saturates at"
  , "    `UInt64.size`; for the literals BNFC grammars emit, this is fine. -/"
  , "private def natToFloat (n : Nat) : Float :="
  , "  (n.toUInt64).toFloat"
  , ""
  , "/-- 10^n as a `Float` (computed by repeated multiplication). -/"
  , "private def pow10 : Nat → Float"
  , "  | 0     => 1.0"
  , "  | n + 1 => 10.0 * pow10 n"
  , ""
  , "/-- Combine a non-negative integer part and a fractional digit list"
  , "    into a `Float` using `int + frac / 10^|frac|`. -/"
  , "private def buildFloat (intPart : Nat) (frac : List Char) : Float :="
  , "  let fracStr := String.ofList frac"
  , "  let fracN := natToFloat (fracStr.toNat?.getD 0)"
  , "  natToFloat intPart + fracN / pow10 frac.length"
  , ""
  , "/-- Match an integer or float literal.  Returns the new cursor and the"
  , "    number of characters consumed (for position tracking). -/"
  , "private def matchNumber : List Char → Option (Sum Int Float × List Char × Nat)"
  , "  | [] => none"
  , "  | c :: rest =>"
  , "      if c.isDigit then"
  , "        let (intDigits, afterInt) := scanDigits rest [c]"
  , "        let intLen := intDigits.length"
  , "        let intLex := String.ofList intDigits"
  , "        let intVal : Int := intLex.toInt?.getD 0"
  , "        let intNat : Nat := intLex.toNat?.getD 0"
  , "        match afterInt with"
  , "        | '.' :: d :: more =>"
  , "            if d.isDigit then"
  , "              let (frac, afterFrac) := scanDigits more [d]"
  , "              some (Sum.inr (buildFloat intNat frac), afterFrac, intLen + 1 + frac.length)"
  , "            else"
  , "              some (Sum.inl intVal, afterInt, intLen)"
  , "        | _ =>"
  , "            some (Sum.inl intVal, afterInt, intLen)"
  , "      else none"
  , "where"
  , "  scanDigits : List Char → List Char → List Char × List Char"
  , "    | [],        acc => (acc.reverse, [])"
  , "    | c :: rest, acc =>"
  , "        if c.isDigit then scanDigits rest (c :: acc)"
  , "        else (acc.reverse, c :: rest)"
  , ""
  , "/-- Match a double-quoted string literal with `\\n`/`\\t`/`\\\\`/`\\\"` escapes."
  , "    Returns the unescaped contents, the rest of the input, and the"
  , "    number of source characters consumed (including delimiters). -/"
  , "private def matchStringLit : List Char → Option (String × List Char × Nat)"
  , "  | '\"' :: rest =>"
  , "      match go rest [] 1 with"
  , "      | some (s, rest', n) => some (s, rest', n)"
  , "      | none               => none"
  , "  | _ => none"
  , "where"
  , "  go : List Char → List Char → Nat → Option (String × List Char × Nat)"
  , "    | [],            _,   _ => none"
  , "    | '\"' :: rest,    acc, n => some (String.ofList acc.reverse, rest, n + 1)"
  , "    | '\\\\' :: e :: rest, acc, n =>"
  , "        let d := match e with"
  , "                 | 'n'  => '\\n'"
  , "                 | 't'  => '\\t'"
  , "                 | 'r'  => '\\r'"
  , "                 | '\\\\' => '\\\\'"
  , "                 | '\"' => '\"'"
  , "                 | _    => e"
  , "        go rest (d :: acc) (n + 2)"
  , "    | c :: rest,      acc, n => go rest (c :: acc) (n + 1)"
  , ""
  , "/-- Match a single-quoted character literal. -/"
  , "private def matchCharLit : List Char → Option (Char × List Char × Nat)"
  , "  | '\\'' :: '\\\\' :: e :: '\\'' :: rest =>"
  , "      let d := match e with"
  , "               | 'n'  => '\\n'"
  , "               | 't'  => '\\t'"
  , "               | 'r'  => '\\r'"
  , "               | '\\\\' => '\\\\'"
  , "               | '\\'' => '\\''"
  , "               | _    => e"
  , "      some (d, rest, 4)"
  , "  | '\\'' :: c :: '\\'' :: rest => some (c, rest, 3)"
  , "  | _ => none"
  , ""
  , "/-- Try every symbol in `symbols`; return the first (longest) match. -/"
  , "private def matchSymbol (cs : List Char) : Option (String × List Char) :="
  , "  go symbols"
  , "where"
  , "  go : List String → Option (String × List Char)"
  , "    | []          => none"
  , "    | sym :: rest =>"
  , "        match matchLit sym cs with"
  , "        | some cs' => some (sym, cs')"
  , "        | none     => go rest"
  ]

----------------------------------------------------------------------------
-- User-defined `token` pragmas
----------------------------------------------------------------------------

-- | Emit the per-grammar `userTokens : List (String × BNFC.Reg)` table.
--   Each entry is a `(category name, regex literal)` pair, in declaration
--   order (which BNFC's convention says wins on length ties).  The lexer
--   loop runs @BNFC.matchUserToks userTokens@ at every input position;
--   the longest user-token match is preferred over `Ident`/`Integer`/
--   `Float` matchers, with a reserved-word fallback so that words like
--   @inf@ still lex as keywords when the grammar declares them as such.
userTokensBlock :: [(TokenCat, Reg)] -> String
userTokensBlock toks = unlines $
  [ "/-- User-defined @token@ pragmas, in declaration order. -/"
  , "private def userTokens : List (String × BNFC.Reg) :="
  , "  ["
  ] ++ withTrailingCommas (map renderEntry toks) ++
  [ "  ]"
  ]
  where
    renderEntry (cat, r) =
      "    (" ++ show cat ++ ", " ++ regToLeanExpr r ++ ")"

    withTrailingCommas :: [String] -> [String]
    withTrailingCommas []     = []
    withTrailingCommas [x]    = [x]
    withTrailingCommas (x:xs) = (x ++ ",") : withTrailingCommas xs

-- | Render a BNFC `Reg` value as a Lean expression of type `BNFC.Reg`.
--   Mirrors the constructor names in the runtime's `inductive Reg`.
regToLeanExpr :: Reg -> String
regToLeanExpr = \case
  REps        -> ".eps"
  RChar c     -> "(.char " ++ leanCharLit c ++ ")"
  RAlts s     -> "(.alts " ++ leanCharList s ++ ")"
  RSeqs s     -> "(.seqs " ++ show s ++ ")"
  RDigit      -> ".digit"
  RLetter     -> ".letter"
  RUpper      -> ".upper"
  RLower      -> ".lower"
  RAny        -> ".anyCh"
  RSeq a b    -> "(.seq "   ++ regToLeanExpr a ++ " " ++ regToLeanExpr b ++ ")"
  RAlt a b    -> "(.alt "   ++ regToLeanExpr a ++ " " ++ regToLeanExpr b ++ ")"
  RStar a     -> "(.star "  ++ regToLeanExpr a ++ ")"
  RPlus a     -> "(.plus "  ++ regToLeanExpr a ++ ")"
  ROpt a      -> "(.opt "   ++ regToLeanExpr a ++ ")"
  RMinus a b  -> "(.minus " ++ regToLeanExpr a ++ " " ++ regToLeanExpr b ++ ")"
  where
    leanCharLit c = "'" ++ escapeChar c ++ "'"
    leanCharList s = "[" ++ intercalateStr ", " (map leanCharLit s) ++ "]"
    -- Escape characters that have special meaning inside a Lean Char literal.
    escapeChar '\'' = "\\'"
    escapeChar '\\' = "\\\\"
    escapeChar '\n' = "\\n"
    escapeChar '\t' = "\\t"
    escapeChar '\r' = "\\r"
    escapeChar c    = [c]

----------------------------------------------------------------------------
-- Main tokenize loop
----------------------------------------------------------------------------

tokenizeBlock :: String
tokenizeBlock = unlines
  [ "/-- Tokenise an entire input string into a list of `BNFC.Token`s. -/"
  , "partial def tokenize (input : String) : Except BNFC.ParseError (List BNFC.Token) :="
  , "  loop input.toList { line := 1, col := 1 } []"
  , "where"
  , "  loop (cs : List Char) (p : BNFC.Position) (acc : List BNFC.Token)"
  , "      : Except BNFC.ParseError (List BNFC.Token) :="
  , "    let (cs, p) := skipWs cs p"
  , "    match cs with"
  , "    | [] => .ok acc.reverse"
  , "    | c :: _ =>"
  , "      -- 1. Try user-defined `token` pragmas first.  They take priority"
  , "      --    over the built-in number/ident matchers, BUT a matched"
  , "      --    lexeme that also happens to be a reserved word loses to the"
  , "      --    keyword interpretation (this preserves BNFC's usual"
  , "      --    \"reserved words beat identifiers\" semantics)."
  , "      let userResult :="
  , "        match BNFC.matchUserToks userTokens cs with"
  , "        | some (cat, lex, cs') =>"
  , "            if reserved.contains lex then none"
  , "            else                          some (cat, lex, cs')"
  , "        | none => none"
  , "      match userResult with"
  , "      | some (cat, lex, cs') =>"
  , "          let p' := advanceN cs p lex.length"
  , "          loop cs' p' ({ kind := .userTok cat lex, pos := p } :: acc)"
  , "      | none =>"
  , "      -- 2. Fall through to the built-in pipeline."
  , "      match matchNumber cs with"
  , "      | some (Sum.inl n, cs', len) =>"
  , "          let p' := advanceN cs p len"
  , "          loop cs' p' ({ kind := .intLit n, pos := p } :: acc)"
  , "      | some (Sum.inr x, cs', len) =>"
  , "          let p' := advanceN cs p len"
  , "          loop cs' p' ({ kind := .floatLit x, pos := p } :: acc)"
  , "      | none =>"
  , "      match matchStringLit cs with"
  , "      | some (s, cs', len) =>"
  , "          let p' := advanceN cs p len"
  , "          loop cs' p' ({ kind := .strLit s, pos := p } :: acc)"
  , "      | none =>"
  , "      match matchCharLit cs with"
  , "      | some (ch, cs', len) =>"
  , "          let p' := advanceN cs p len"
  , "          loop cs' p' ({ kind := .charLit ch, pos := p } :: acc)"
  , "      | none =>"
  , "      match matchIdent cs with"
  , "      | some (lex, cs') =>"
  , "          let p' := advanceN cs p lex.length"
  , "          let kind := if reserved.contains lex then BNFC.TokenKind.keyword lex"
  , "                      else BNFC.TokenKind.ident lex"
  , "          loop cs' p' ({ kind := kind, pos := p } :: acc)"
  , "      | none =>"
  , "      match matchSymbol cs with"
  , "      | some (sym, cs') =>"
  , "          let p' := advanceN cs p sym.length"
  , "          loop cs' p' ({ kind := .keyword sym, pos := p } :: acc)"
  , "      | none =>"
  , "          .error { pos := p, message := s!\"unexpected character `{c}`\" }"
  ]

----------------------------------------------------------------------------
-- Helpers
----------------------------------------------------------------------------

leanList :: [String] -> String
leanList xs = "[" ++ intercalateStr ", " (map show xs) ++ "]"

leanList' :: [String] -> String
leanList' xs = "[" ++ intercalateStr ", " xs ++ "]"

intercalateStr :: String -> [String] -> String
intercalateStr _   []     = ""
intercalateStr _   [x]    = x
intercalateStr sep (x:xs) = x ++ sep ++ intercalateStr sep xs
