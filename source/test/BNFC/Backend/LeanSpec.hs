module BNFC.Backend.LeanSpec where

import BNFC.Backend.Base (execBackend, fileContent, fileName)
import BNFC.CF (CF)
import BNFC.Options
import BNFC.GetCF

import Test.Hspec
import BNFC.Hspec

import BNFC.Backend.Lean -- SUT

calcOptions :: SharedOptions
calcOptions = defaultOptions { lang = "Calc", target = TargetLean }

getCalc :: IO CF
getCalc = parseCF calcOptions TargetLean $ unlines
  [ "EAdd. Exp  ::= Exp \"+\" Exp1  ;"
  , "ESub. Exp  ::= Exp \"-\" Exp1  ;"
  , "EMul. Exp1 ::= Exp1 \"*\" Exp2 ;"
  , "EDiv. Exp1 ::= Exp1 \"/\" Exp2 ;"
  , "EInt. Exp2 ::= Integer ;"
  , "coercions Exp 2 ;"
  ]

spec :: Spec
spec = describe "Lean 4 backend" $ do

  it "creates the AbsCalc.lean file" $ do
    cf <- getCalc
    makeLean calcOptions cf `shouldGenerate` "AbsCalc.lean"

  it "creates the LexCalc.lean file" $ do
    cf <- getCalc
    makeLean calcOptions cf `shouldGenerate` "LexCalc.lean"

  it "creates the ParCalc.lean file" $ do
    cf <- getCalc
    makeLean calcOptions cf `shouldGenerate` "ParCalc.lean"

  it "creates the PrintCalc.lean file" $ do
    cf <- getCalc
    makeLean calcOptions cf `shouldGenerate` "PrintCalc.lean"

  it "creates the TestCalc.lean file" $ do
    cf <- getCalc
    makeLean calcOptions cf `shouldGenerate` "TestCalc.lean"

  it "creates the ParserRuntime.lean file" $ do
    cf <- getCalc
    makeLean calcOptions cf `shouldGenerate` "ParserRuntime.lean"

  it "creates the lakefile.toml file" $ do
    cf <- getCalc
    makeLean calcOptions cf `shouldGenerate` "lakefile.toml"

  it "creates the lean-toolchain file" $ do
    cf <- getCalc
    makeLean calcOptions cf `shouldGenerate` "lean-toolchain"

  it "the generated AST mentions all four constructors" $ do
    cf <- getCalc
    files <- execBackend (makeLean calcOptions cf)
    let absContent = case [fileContent f | f <- files, fileName f == "AbsCalc.lean"] of
          (s:_) -> s
          []    -> ""
    absContent `shouldContain` "EAdd"
    absContent `shouldContain` "ESub"
    absContent `shouldContain` "EMul"
    absContent `shouldContain` "EDiv"
    absContent `shouldContain` "EInt"

  it "the lakefile.toml names the language as the project" $ do
    cf <- getCalc
    files <- execBackend (makeLean calcOptions cf)
    let lake = case [fileContent f | f <- files, fileName f == "lakefile.toml"] of
          (s:_) -> s
          []    -> ""
    lake `shouldContain` "name = \"Calc\""
    lake `shouldContain` "lean_exe"
