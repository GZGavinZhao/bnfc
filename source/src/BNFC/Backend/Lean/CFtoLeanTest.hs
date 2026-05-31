{- |
Module      : BNFC.Backend.Lean.CFtoLeanTest
Description : Generate the executable test harness in Lean 4.

The driver reads a file or stdin, lexes and parses it via the generated
modules, and prints either the AST (via @repr@) and a re-printed form,
or a parse error message.  It is the analogue of @TestLANG.hs@ from
the Haskell backend.
-}

module BNFC.Backend.Lean.CFtoLeanTest ( cf2Test ) where

import BNFC.CF

cf2Test :: String -> String -> String -> String -> String -> CF -> String
cf2Test _modName absMod parMod printMod _runtimeMod cf = unlines
  [ "import " ++ absMod
  , "import " ++ parMod
  , "import " ++ printMod
  , ""
  , "/-! CLI driver: read a file (or stdin) and run the generated parser. -/"
  , ""
  , "/-- Parse a single input string and report result. -/"
  , "def runOne (input : String) : IO Unit := do"
  , "  match " ++ parMod ++ ".parse" ++ identCat firstE ++ " input with"
  , "  | .ok tree =>"
  , "    IO.println \"\\nParse Successful!\""
  , "    IO.println \"\\n[Linearized tree]\""
  , "    IO.println (" ++ printMod ++ ".printTree tree)"
  , "    IO.println \"\\n[Abstract Syntax]\""
  , "    IO.println (repr tree)"
  , "  | .error msg =>"
  , "    IO.eprintln (\"Parse failed: \" ++ msg)"
  , "    IO.Process.exit 1"
  , ""
  , "/-- Top-level entry point.  Called by Lake when the project is run. -/"
  , "def main (args : List String) : IO UInt32 := do"
  , "  match args with"
  , "  | []    => do"
  , "    let input ← IO.getStdin >>= (·.readToEnd)"
  , "    runOne input"
  , "    return 0"
  , "  | files => do"
  , "    for f in files do"
  , "      IO.println (\"-- \" ++ f)"
  , "      let input ← IO.FS.readFile f"
  , "      runOne input"
  , "    return 0"
  ]
  where
    firstE = firstEntry cf
