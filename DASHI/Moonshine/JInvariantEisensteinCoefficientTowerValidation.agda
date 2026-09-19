module DASHI.Moonshine.JInvariantEisensteinCoefficientTowerValidation where

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -_)

import DASHI.Physics.Closure.TriadicSectorQSeries as QS
import DASHI.Moonshine.JInvariantEisensteinCoefficientTowerExact as P

E4zero : P.e4Coefficient zero ≡ + 1
E4zero = refl

E4one : P.e4Coefficient 1 ≡ + 240
E4one = refl

E4two : P.e4Coefficient 2 ≡ + 2160
E4two = refl

E4three : P.e4Coefficient 3 ≡ + 6720
E4three = refl

E6zero : P.e6Coefficient zero ≡ + 1
E6zero = refl

E6one : P.e6Coefficient 1 ≡ - (+ 504)
E6one = refl

E6two : P.e6Coefficient 2 ≡ - (+ 16632)
E6two = refl

E6three : P.e6Coefficient 3 ≡ - (+ 122976)
E6three = refl

E4towerOne :
  QS.traceCoefficient P.eisensteinCoefficientTower 1 P.e4Sector ≡ + 240
E4towerOne = refl

E6towerOne :
  QS.traceCoefficient P.eisensteinCoefficientTower 1 P.e6Sector ≡ - (+ 504)
E6towerOne = refl

finitePrefixIsNotAnalyticSameObject :
  P.finiteCoefficientTowerEqualsAnalyticEisenstein
    P.canonicalEisensteinCoefficientTowerBoundary
  ≡ false
finitePrefixIsNotAnalyticSameObject = refl

finitePrefixDoesNotCreateConvergence :
  P.finitePrefixCreatesConvergence
    P.canonicalEisensteinCoefficientTowerBoundary
  ≡ false
finitePrefixDoesNotCreateConvergence = refl
