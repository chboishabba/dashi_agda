module DASHI.Moonshine.JInvariantElementaryCalculatorShellValidation where

open import DASHI.Core.Prelude

import DASHI.Foundations.ElementarySingleOperator as EML
import DASHI.Foundations.ElementaryCalculator as Calc
import DASHI.Moonshine.JInvariantElementaryCalculatorShellExact as P

qLowersToExpRegression :
  Calc.lowerCalculator P.qCoordinateExpr
  ≡ EML.expE (Calc.lowerCalculator P.twoPiITauExpr)
qLowersToExpRegression = refl

finiteHeadCompilesRegression :
  P.finiteJHeadCompiled ≡ Calc.compileCalculator P.finiteJHeadExpr
finiteHeadCompilesRegression = refl
