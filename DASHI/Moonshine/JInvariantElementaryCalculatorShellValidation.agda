module DASHI.Moonshine.JInvariantElementaryCalculatorShellValidation where

open import DASHI.Core.Prelude

import DASHI.Foundations.ElementaryCalculator as Calc
import DASHI.Moonshine.JInvariantElementaryCalculatorShellExact as P

qLowersToExpRegression :
  Calc.lowerCalculator P.qCoordinateExpr
  ≡ Calc.expE (Calc.lowerCalculator P.twoPiITauExpr)
qLowersToExpRegression = refl

finiteHeadCompilesRegression :
  P.finiteJHeadCompiled ≡ Calc.compileCalculator P.finiteJHeadExpr
finiteHeadCompilesRegression = refl
