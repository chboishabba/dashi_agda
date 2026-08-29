module DASHI.Physics.Closure.NSTriadKNOppositeHelicityDyadicDecisionRound232Exact where

------------------------------------------------------------------------
-- ROUND232 / OPPOSITE-HELICITY SYMBOL: EXACT ALGEBRAIC DECISION SURFACE
--
-- This file formalises only the division-free algebraic consequences used by
-- the Round232 harmonic-analysis audit.  It does NOT claim that the current
-- weak rational carrier has already welded the physical helical eigenvectors
-- to the angular symbol formula.  That basis/angular weld remains explicit.
--
-- For normalized helical eigenvectors the exploratory calculation gives
--
--   |h_+(p) x h_-(q)|^2 = ((3-c)(1+c))/4,
--   c = p-hat . q-hat.
--
-- We therefore work with the four-times symbol square
--
--   S4(c) = (3-c)(1+c).
--
-- Two exact identities drive the decision:
--
--   S4(-1) = 0,                  (HH anti-parallel null)
--   S4(0)  = 3.                  (order-one FL/CC witness)
--
-- and, using the resonant radial/angular decomposition
--
--   k^2 = gap^2 + 2 rp rq (1+c),
--
--   4 k^2 - 2 rp rq S4(c)
--     = 4 gap^2 + 2 rp rq (1+c)^2.
--
-- Thus once the missing physical basis/angular weld and positivity layer are
-- supplied, the HH estimate is exactly
--
--   |B_+-|^2 <= k^2 / (2 rp rq).
--
-- By contrast c=0 stays order one under arbitrary radial scaling, so neither
-- FL nor CC has a generic pointwise scale gain in the bare mixed-helicity
-- symbol.
--
-- Backward dyadic audit: a 3D comparable-shell Bernstein estimate contributes
-- amplitude exponent 3/2, hence squared exponent 3.  The Leray H1 payment owns
-- squared exponent 2.  The missing squared exponent is 1, i.e. a pointwise
-- symbol amplitude gain of one half derivative.  The c=0 family rules that out
-- pointwise in CC.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

one two three four : ℚ
one = 1ℚ
two = one + one
three = two + one
four = two + two

square : ℚ → ℚ
square x = x * x

fourTimesOppositeHelicitySymbolSquare : ℚ → ℚ
fourTimesOppositeHelicitySymbolSquare c =
  (three - c) * (one + c)

antiParallelCosine : ℚ
antiParallelCosine = 0ℚ - one

orthogonalCosine : ℚ
orthogonalCosine = 0ℚ

antiParallelSymbolVanishes :
  fourTimesOppositeHelicitySymbolSquare antiParallelCosine ≡ 0ℚ
antiParallelSymbolVanishes = solve []

orthogonalSymbolSquareIsThreeQuartersScaled :
  fourTimesOppositeHelicitySymbolSquare orthogonalCosine ≡ three
orthogonalSymbolSquareIsThreeQuartersScaled = solve []

angularGapIdentity :
  (c : ℚ) →
  four * (one + c) - fourTimesOppositeHelicitySymbolSquare c
  ≡ square (one + c)
angularGapIdentity c = solve (c ∷ [])

record ResonantAngularData : Set where
  constructor resonant-angular-data
  field
    radiusP radiusQ outputSquare radialGapSquare cosine : ℚ
    resonantComplement :
      outputSquare
      ≡ radialGapSquare
        + two * radiusP * radiusQ * (one + cosine)

open ResonantAngularData public

hhDivisionFreeEnvelopeIdentity :
  (D : ResonantAngularData) →
  four * outputSquare D
    - two * radiusP D * radiusQ D
        * fourTimesOppositeHelicitySymbolSquare (cosine D)
  ≡
  four * radialGapSquare D
    + two * radiusP D * radiusQ D * square (one + cosine D)
hhDivisionFreeEnvelopeIdentity D
  rewrite resonantComplement D =
  solve
    ( radiusP D ∷ radiusQ D ∷ radialGapSquare D ∷ cosine D ∷ [])

-- Backward exponent bookkeeping for the CC endpoint.
-- Squared generic Bernstein cost: 2^(3m).
-- Squared one-derivative Leray budget: 2^(2m).
-- Therefore the symbol square must supply 2^(-m), equivalently the symbol
-- amplitude must supply 2^(-m/2).

ccGenericSquaredSpatialExponent : ℚ
ccGenericSquaredSpatialExponent = three

leraySquaredDerivativeExponent : ℚ
leraySquaredDerivativeExponent = two

ccMissingSquaredExponent : ℚ
ccMissingSquaredExponent =
  ccGenericSquaredSpatialExponent - leraySquaredDerivativeExponent

ccMissingSquaredExponentIsOne : ccMissingSquaredExponent ≡ one
ccMissingSquaredExponentIsOne = solve []

-- Status / trust boundary.
round232AngularPolynomialAlgebraClosed : Bool
round232AngularPolynomialAlgebraClosed = true

round232HHAntiParallelNullAlgebraClosed : Bool
round232HHAntiParallelNullAlgebraClosed = true

round232HHDivisionFreeEnvelopeIdentityClosed : Bool
round232HHDivisionFreeEnvelopeIdentityClosed = true

round232PhysicalHelicalBasisToAngularFormulaWeldClosed : Bool
round232PhysicalHelicalBasisToAngularFormulaWeldClosed = false

round232FLGenericPointwiseScaleGainExists : Bool
round232FLGenericPointwiseScaleGainExists = false

round232CCGenericPointwiseHalfDerivativeGainExists : Bool
round232CCGenericPointwiseHalfDerivativeGainExists = false

round232PointwiseSymbolRouteClosesPackageA : Bool
round232PointwiseSymbolRouteClosesPackageA = false

round232NextTargetIsSameScaleSummedCancellation : Bool
round232NextTargetIsSameScaleSummedCancellation = true

round232PackageAClosed : Bool
round232PackageAClosed = false

round232ClayPromotion : Bool
round232ClayPromotion = false

round232AngularPolynomialAlgebraClosedIsTrue :
  round232AngularPolynomialAlgebraClosed ≡ true
round232AngularPolynomialAlgebraClosedIsTrue = refl

round232HHAntiParallelNullAlgebraClosedIsTrue :
  round232HHAntiParallelNullAlgebraClosed ≡ true
round232HHAntiParallelNullAlgebraClosedIsTrue = refl

round232PhysicalHelicalBasisToAngularFormulaWeldClosedIsFalse :
  round232PhysicalHelicalBasisToAngularFormulaWeldClosed ≡ false
round232PhysicalHelicalBasisToAngularFormulaWeldClosedIsFalse = refl

round232FLGenericPointwiseScaleGainExistsIsFalse :
  round232FLGenericPointwiseScaleGainExists ≡ false
round232FLGenericPointwiseScaleGainExistsIsFalse = refl

round232CCGenericPointwiseHalfDerivativeGainExistsIsFalse :
  round232CCGenericPointwiseHalfDerivativeGainExists ≡ false
round232CCGenericPointwiseHalfDerivativeGainExistsIsFalse = refl

round232PointwiseSymbolRouteClosesPackageAIsFalse :
  round232PointwiseSymbolRouteClosesPackageA ≡ false
round232PointwiseSymbolRouteClosesPackageAIsFalse = refl

round232NextTargetIsSameScaleSummedCancellationIsTrue :
  round232NextTargetIsSameScaleSummedCancellation ≡ true
round232NextTargetIsSameScaleSummedCancellationIsTrue = refl

round232PackageAClosedIsFalse : round232PackageAClosed ≡ false
round232PackageAClosedIsFalse = refl

round232ClayPromotionIsFalse : round232ClayPromotion ≡ false
round232ClayPromotionIsFalse = refl
