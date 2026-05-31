{- |
Module      : BNFC.Backend.Lean.CFtoLeanAbs
Description : Generate the Lean 4 abstract-syntax module from a BNFC
              context-free grammar.

The output uses:

  * @inductive ... where@ for each non-list, non-coercion category.
  * @mutual ... end@ to allow categories to refer to each other freely.
  * Token categories defined as @abbrev@ aliases (e.g.
    @abbrev Ident := String@).
  * Built-in literal categories use Lean's native types
    (@Int@, @Float@, @String@, @Char@); user-defined token categories
    become @String@ via @abbrev@.

We do *not* encode position information in the AST in this initial
implementation, matching what the OCaml backend ships by default.
-}

module BNFC.Backend.Lean.CFtoLeanAbs ( cf2Abstract ) where

import BNFC.CF
import BNFC.Backend.Lean.LeanUtil

-- | Generate the @AbsLANG.lean@ module.
cf2Abstract :: String -> CF -> String
cf2Abstract modName cf = unlines $ concat
  [ [ "/-! Abstract syntax produced from a BNFC grammar.  Categories that"
    , "    refer to one another are wrapped in a single `mutual` block."
    , "    Built-in token types are mapped to native Lean types where"
    , "    possible (`Integer → Int`, `Double → Float`, `String → String`,"
    , "    `Char → Char`); user-defined and `Ident`-style tokens become"
    , "    `String`. -/"
    , ""
    , "namespace " ++ modName
    , ""
    ]
  , tokenAbbrevs
  , [ "" | not (null tokenAbbrevs) ]
  , mutualBlock
  , [ ""
    , "end " ++ modName
    ]
  ]
  where
    -- Token-category aliases.
    tokenAbbrevs =
      [ "abbrev " ++ sanitizeLeanUpper t ++ " := String"
      | t <- specialCats cf
      ]

    -- Each entry has the form (Cat, [(Fun, [Cat])]) — non-empty rhs lists only.
    dataCats = filter (not . null . snd) (cf2data cf)

    mutualBlock
      | null dataCats           = []
      | length dataCats == 1    = inductiveDecl (head dataCats)
      | otherwise               = concat
          [ [ "mutual" ]
          , concatMap inductiveDecl dataCats
          , [ "end" ]
          ]

    inductiveDecl :: Data -> [String]
    inductiveDecl (cat, ctors) =
      let typeName = sanitizeLeanUpper (catToStr (normCat cat))
      in concat
         [ [ "inductive " ++ typeName ++ " where" ]
         , map (renderCtor typeName) ctors
         , [ "  deriving Repr" ]
         ]

    renderCtor :: String -> (Fun, [Cat]) -> String
    renderCtor resultType (fun, args) =
      let argTypes = map catToLeanType args
          arrow t  = t ++ " → "
      in case argTypes of
           []  -> "  | " ++ constructorName fun ++ " : " ++ resultType
           ts  -> "  | " ++ constructorName fun ++ " : "
                  ++ concatMap arrow ts ++ resultType
