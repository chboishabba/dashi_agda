module DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact where

------------------------------------------------------------------------
-- ROUND311 / INNER MULTIPLIER DIFFERENCE IS NOT A UNIVERSAL DYADIC GAIN
--
-- R310 exposes the exact inner paired factor (lambda_b-lambda_a).  For a
-- helical eigenvalue lambda=sigma*r with sigma in {+1,-1} and r>=0:
--
--   same sign     : lambda_b-lambda_a = sigma (r_b-r_a)
--   opposite sign : lambda_b-lambda_a = +/- (r_b+r_a).
--
-- Therefore the R120 inner commutator gives a genuinely small factor only on
-- a RADIAL-NEAR homochiral subregion.  Dyadic comparability alone does not
-- force |r_b-r_a| small, and the heterochiral factor is a radius sum rather
-- than a null factor.
--
-- This refines the R301 proof-search node into three children before any shell
-- estimate is strengthened globally.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _-_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission

data HelicitySign : Set where
  plus minus : HelicitySign

signedRadius : HelicitySign → ℚ → ℚ
signedRadius plus r = r
signedRadius minus r = - r

innerMultiplierDifference : HelicitySign → HelicitySign → ℚ → ℚ → ℚ
innerMultiplierDifference sa sb ra rb =
  signedRadius sb rb - signedRadius sa ra

samePlusDifference :
  (ra rb : ℚ) →
  innerMultiplierDifference plus plus ra rb ≡ rb - ra
samePlusDifference ra rb = refl

sameMinusDifference :
  (ra rb : ℚ) →
  innerMultiplierDifference minus minus ra rb ≡ -(rb - ra)
sameMinusDifference ra rb = solve (ra ∷ rb ∷ [])

oppositePlusMinusDifference :
  (ra rb : ℚ) →
  innerMultiplierDifference plus minus ra rb ≡ -(rb + ra)
oppositePlusMinusDifference ra rb = solve (ra ∷ rb ∷ [])

oppositeMinusPlusDifference :
  (ra rb : ℚ) →
  innerMultiplierDifference minus plus ra rb ≡ rb + ra
oppositeMinusPlusDifference ra rb = solve (ra ∷ rb ∷ [])

-- Finite witnesses preventing accidental promotion of the multiplier
-- difference to an automatic small factor.
sameSignComparableWitness :
  innerMultiplierDifference plus plus 1 2 ≡ 1
sameSignComparableWitness = refl

oppositeSignNoNullWitness :
  innerMultiplierDifference plus minus 1 1 ≡ -2
oppositeSignNoNullWitness = refl

data InnerNestedRoute : Set where
  homochiralRadialNear : InnerNestedRoute
  homochiralRadialSeparated : InnerNestedRoute
  heterochiralInner : InnerNestedRoute

routeDisposition : InnerNestedRoute → Admission.RouteDisposition
routeDisposition homochiralRadialNear = Admission.admitted
routeDisposition homochiralRadialSeparated = Admission.redirectedReuse
routeDisposition heterochiralInner = Admission.redirectedReuse

round311InnerMultiplierDifferenceExposed : Bool
round311InnerMultiplierDifferenceExposed = true

round311DyadicComparabilityImpliesSmallMultiplierDifference : Bool
round311DyadicComparabilityImpliesSmallMultiplierDifference = false

round311HeterochiralInnerMultiplierIsNullGain : Bool
round311HeterochiralInnerMultiplierIsNullGain = false

round311HomochiralRadialNearRouteAdmitted : Bool
round311HomochiralRadialNearRouteAdmitted = true

round311SeparatedAndHeterochiralNeedAdditionalGeometry : Bool
round311SeparatedAndHeterochiralNeedAdditionalGeometry = true

round311NestedShellEstimateClosed : Bool
round311NestedShellEstimateClosed = false

round311PackageAClosed : Bool
round311PackageAClosed = false

round311ClayPromotion : Bool
round311ClayPromotion = false
