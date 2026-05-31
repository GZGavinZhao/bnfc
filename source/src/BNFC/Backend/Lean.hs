{- |
Module      : BNFC.Backend.Lean
Description : Top-level Lean 4 backend.

Wires together the AST, lexer, parser, printer and test-driver
generators and emits a runnable Lean 4 project (with a @lakefile.toml@
and pinned toolchain).  The output has no external Lake dependencies:
the runtime parser combinators ship in @ParserRuntime.lean@ alongside
the generated code.
-}

module BNFC.Backend.Lean ( makeLean ) where

import BNFC.Backend.Base
import BNFC.CF
import BNFC.Options ( SharedOptions(..) )

import qualified BNFC.Backend.Common.Makefile as Makefile

import BNFC.Backend.Lean.CFtoLeanAbs     ( cf2Abstract )
import BNFC.Backend.Lean.CFtoLeanLex     ( cf2Lex )
import BNFC.Backend.Lean.CFtoLeanPar     ( cf2Par )
import BNFC.Backend.Lean.CFtoLeanPrinter ( cf2Printer )
import BNFC.Backend.Lean.CFtoLeanRuntime ( runtimeContent )
import BNFC.Backend.Lean.CFtoLeanTest    ( cf2Test )
import BNFC.Backend.Lean.LeanUtil

import BNFC.PrettyPrint ( vcat, text, Doc )

-- | Top-level entrypoint dispatched from @Main.hs@.
makeLean :: SharedOptions -> CF -> Backend
makeLean opts cf = do
  let absMod      = absLeanModule     opts
      lexMod      = lexLeanModule     opts
      parMod      = parLeanModule     opts
      printMod    = printLeanModule   opts
      testMod     = testLeanModule    opts
      runtimeMod  = runtimeLeanModule opts

  mkfile (runtimeLeanFile opts) leanComment $ runtimeContent runtimeMod
  mkfile (absLeanFile     opts) leanComment $ cf2Abstract absMod cf
  mkfile (lexLeanFile     opts) leanComment $ cf2Lex      lexMod   runtimeMod cf
  mkfile (parLeanFile     opts) leanComment $ cf2Par      parMod   absMod lexMod runtimeMod cf
  mkfile (printLeanFile   opts) leanComment $ cf2Printer  printMod absMod cf
  mkfile (testLeanFile    opts) leanComment $ cf2Test     testMod  absMod parMod printMod runtimeMod cf

  -- `lakefile.toml` accepts `#` comments; the `lean-toolchain` file
  -- does NOT accept any comment syntax, so we emit a blank-only stamp.
  mkfile lakeFile      ("# " ++) $ lakefileContent opts
  mkfile leanToolchainFile (const "") leanToolchainContent

  Makefile.mkMakefile (optMake opts) (makefile opts)

----------------------------------------------------------------------------
-- Project files
----------------------------------------------------------------------------

-- | Pin to the most recent Lean 4 release at time of writing.  Users can
--   bump this freely; the generated code uses only stable, long-standing
--   APIs (`Monad`, `String.Pos`, `Except`, `List`, `Char.isAlpha` …) so
--   it should keep working for the foreseeable future.
leanToolchainContent :: String
leanToolchainContent = "leanprover/lean4:v4.30.0\n"

lakefileContent :: SharedOptions -> String
lakefileContent opts = unlines
  [ "name = \"" ++ projectName ++ "\""
  , "defaultTargets = [\"" ++ exeName ++ "\"]"
  , ""
  , "[[lean_lib]]"
  , "name = \"" ++ projectName ++ "\""
  , "roots = [\"" ++ runtimeLeanModule opts ++ "\","
  , "         \"" ++ absLeanModule     opts ++ "\","
  , "         \"" ++ lexLeanModule     opts ++ "\","
  , "         \"" ++ parLeanModule     opts ++ "\","
  , "         \"" ++ printLeanModule   opts ++ "\"]"
  , ""
  , "[[lean_exe]]"
  , "name = \"" ++ exeName ++ "\""
  , "root = \"" ++ testLeanModule opts ++ "\""
  ]
  where
    projectName = lang opts
    exeName = "test" ++ lang opts

----------------------------------------------------------------------------
-- Optional Makefile target.  Defers to `lake build`.
----------------------------------------------------------------------------

makefile :: SharedOptions -> String -> Doc
makefile opts _basename = vcat $ map text
  [ "all: build"
  , ""
  , "build:"
  , "\tlake build"
  , ""
  , "clean:"
  , "\trm -rf .lake build"
  , ""
  , "distclean: clean"
  , "\trm -f " ++ unwords generatedFiles
  ]
  where
    generatedFiles =
      [ runtimeLeanFile opts
      , absLeanFile     opts
      , lexLeanFile     opts
      , parLeanFile     opts
      , printLeanFile   opts
      , testLeanFile    opts
      , lakeFile
      , leanToolchainFile
      ]
