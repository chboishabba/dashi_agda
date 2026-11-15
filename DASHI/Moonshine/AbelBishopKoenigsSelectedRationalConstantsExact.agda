module DASHI.Moonshine.AbelBishopKoenigsSelectedRationalConstantsExact where

------------------------------------------------------------------------
-- SELECTED KOENIGS RATIOS: CORRECTED EXACT RATIONAL ARITHMETIC.
--
-- Original constructive exponential/log sources remain separate.
-- This file proves only rational comparisons; it does not manufacture
-- a Bishop fixed point, logarithm branch or physical contraction.
--
-- Original proposed radius 1/8 with lower norm 2499/2000 yields
-- 1/(2499/2000) > 4/5, so kappa=4/5 was NOT valid there.
-- Use radius 1/10 and the weaker certified norm requirement
-- |p| >= 27/20; then |w| >= 5/4 on the disk and
-- |Log'(w)| <= 4/5 (once the Bishop derivative theorem is paid).
--
-- |p| <= 69/50 and kappa <= 4/5 imply
-- beta <= (69/50) * (4/5)^2 = 552/625 < 1.
-- M2 <= 8/25 and radius <= 1/10 give
-- C <= (69/50)*(8/25)*(1/10)^2 < 7/1000.
--
-- All inequalities are exact rational, not float estimations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _/_; _≤_; _≤ᵇ_; _+_; _-_; _*_)
import Data.Rational.Properties as ℚP
import Data.Nat.Properties as ℕP
import Data.Integer.Base as ℤ using ()
import Data.Rational.Unnormalised as RawQ using (0ℚᵘ; 1ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as RawP
import Real as BishopReal
import RealProperties as BishopP
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Foundations.BishopPolynomialGeometricDominationConvergenceExact as Geometric

centerReal centerImag : ℚ
centerReal = + 31813 / 100000
centerImag = + 133724 / 100000

newtonRadius selectedLogDiskRadius : ℚ
newtonRadius = + 1 / 200
selectedLogDiskRadius = + 1 / 10

selectedModulusLower selectedModulusUpper : ℚ
selectedModulusLower = + 27 / 20
selectedModulusUpper = + 69 / 50

selectedDiskModulusLower : ℚ
selectedDiskModulusLower = + 5 / 4

selectedLogLipschitz : ℚ
selectedLogLipschitz = + 4 / 5

selectedLogSecondRemainder : ℚ
selectedLogSecondRemainder = + 8 / 25

selectedIncrementRatio : ℚ
selectedIncrementRatio = + 552 / 625

selectedIncrementConstantUpper : ℚ
selectedIncrementConstantUpper = + 7 / 1000

zeroQ oneQ : ℚ
zeroQ = + 0 / 1
oneQ = + 1 / 1

selectedDiskModulusLowerExact :
  selectedModulusLower - selectedLogDiskRadius
    ≡ selectedDiskModulusLower
selectedDiskModulusLowerExact = refl

selectedLipschitzReciprocalExact :
  selectedDiskModulusLower * selectedLogLipschitz ≡ oneQ
selectedLipschitzReciprocalExact = refl

selectedSecondRemainderExact :
  (+ 2 / 1) * selectedDiskModulusLower *
    selectedDiskModulusLower * selectedLogSecondRemainder
  ≡ oneQ
selectedSecondRemainderExact = refl

selectedGeometricRatioExact :
  selectedModulusUpper * selectedLogLipschitz *
    selectedLogLipschitz
  ≡ selectedIncrementRatio
selectedGeometricRatioExact = refl

selectedGeometricRatioLessThanOne :
  selectedIncrementRatio ≤ oneQ
selectedGeometricRatioLessThanOne = ℚP.≤ᵇ⇒≤ tt

selectedGeometricRatioStrictWitness :
  selectedIncrementRatio ≤ (+ 9 / 10)
selectedGeometricRatioStrictWitness = ℚP.≤ᵇ⇒≤ tt

selectedIncrementConstantBound :
  selectedModulusUpper * selectedLogSecondRemainder *
    selectedLogDiskRadius * selectedLogDiskRadius
  ≤ selectedIncrementConstantUpper
selectedIncrementConstantBound = ℚP.≤ᵇ⇒≤ tt



------------------------------------------------------------------------
-- The selected rational CENTER has genuine squared-modulus margins.
-- When the Newton disk of radius 1/200 is inhabited on this center,
-- triangle inequalities propagate these to |p| in [27/20,69/50].
------------------------------------------------------------------------

centerNormSquare : ℚ
centerNormSquare =
  centerReal * centerReal + centerImag * centerImag

centerNormSqAboveLowerMargin :
  ((+ 271 / 200) * (+ 271 / 200)) ≤ centerNormSquare
centerNormSqAboveLowerMargin = ℚP.≤ᵇ⇒≤ tt

centerNormSqBelowUpperMargin :
  centerNormSquare ≤ ((+ 11 / 8) * (+ 11 / 8))
centerNormSqBelowUpperMargin = ℚP.≤ᵇ⇒≤ tt

selectedNewtonContractionComparison :
  (+ 7 / 5) ≤ (+ 3 / 2)
selectedNewtonContractionComparison = ℚP.≤ᵇ⇒≤ tt

selectedNewtonSelfMapComparison :
  ((+ 1 / 10000) * (+ 2 / 3)) +
  ((+ 1 / 200) * (+ 1 / 200))
  ≤ newtonRadius
selectedNewtonSelfMapComparison = ℚP.≤ᵇ⇒≤ tt

selectedNewtonCenterInsideLogDisk :
  newtonRadius ≤ selectedLogDiskRadius
selectedNewtonCenterInsideLogDisk = ℚP.≤ᵇ⇒≤ tt


------------------------------------------------------------------------
-- Native BISHOP REAL [0,1) evidence for the selected geometric ratio.
-- This directly fills the EXISTING Step-V/Bishop convergence input.
-- It is not merely the normalized Data.Rational ordering above.
------------------------------------------------------------------------

bishopSelectedKoenigsBeta : BishopReal.ℝ
bishopSelectedKoenigsBeta =
  BishopReal._⋆ (+ 552 / 625)

bishopSelectedKoenigsConstant : BishopReal.ℝ
bishopSelectedKoenigsConstant =
  BishopReal._⋆ (+ 7 / 1000)

bishopSelectedKoenigsBetaNonnegative :
  BishopReal._≤_ BishopReal.0ℝ bishopSelectedKoenigsBeta
bishopSelectedKoenigsBetaNonnegative =
  BishopP.p≤q⇒p⋆≤q⋆
    0ℚᵘ (+ 552 / 625)
    (RawP.nonNegative⁻¹ (+ 552 / 625))

bishopSelectedKoenigsBetaBelowOne :
  BishopReal._<_ bishopSelectedKoenigsBeta BishopReal.1ℝ
bishopSelectedKoenigsBetaBelowOne =
  BishopP.p<q⇒p⋆<q⋆
    (+ 552 / 625) 1ℚᵘ
    (RawQ.*<* (ℤ.+<+ (ℕP.≤ᵇ⇒≤ tt)))

bishopSelectedKoenigsConstantNonnegative :
  BishopReal._≤_ BishopReal.0ℝ bishopSelectedKoenigsConstant
bishopSelectedKoenigsConstantNonnegative =
  BishopP.p≤q⇒p⋆≤q⋆
    0ℚᵘ (+ 7 / 1000)
    (RawP.nonNegative⁻¹ (+ 7 / 1000))

bishopSelectedKoenigsBetaInterval :
  Unit.BishopUnitIntervalRatio bishopSelectedKoenigsBeta
bishopSelectedKoenigsBetaInterval = record
  { Unit.ratioNonnegative = bishopSelectedKoenigsBetaNonnegative
  ; Unit.ratioBelowOne = bishopSelectedKoenigsBetaBelowOne
  }

bishopSelectedKoenigsGeometricInputs :
  Geometric.BishopScaledGeometricInputs
    bishopSelectedKoenigsConstant bishopSelectedKoenigsBeta
bishopSelectedKoenigsGeometricInputs = record
  { Geometric.constantNonnegative = bishopSelectedKoenigsConstantNonnegative
  ; Geometric.ratioInputs = bishopSelectedKoenigsBetaInterval
  }


------------------------------------------------------------------------
-- Native Bishop rational Newton majorant:
-- ||T^(n+1)(p0)-T^n(p0)|| <= (1/15000)*(1/200)^n
-- is the eventual source bound; below we construct ONLY its admissible
-- [0,1) geometric-ratio evidence, not the unproved inequality itself.
------------------------------------------------------------------------

bishopSelectedNewtonRatio : BishopReal.ℝ
bishopSelectedNewtonRatio = BishopReal._⋆ (+ 1 / 200)

bishopSelectedNewtonIncrementConstant : BishopReal.ℝ
bishopSelectedNewtonIncrementConstant =
  BishopReal._⋆ (+ 1 / 15000)

bishopSelectedNewtonRatioNonnegative :
  BishopReal._≤_ BishopReal.0ℝ bishopSelectedNewtonRatio
bishopSelectedNewtonRatioNonnegative =
  BishopP.p≤q⇒p⋆≤q⋆
    0ℚᵘ (+ 1 / 200)
    (RawP.nonNegative⁻¹ (+ 1 / 200))

bishopSelectedNewtonRatioBelowOne :
  BishopReal._<_ bishopSelectedNewtonRatio BishopReal.1ℝ
bishopSelectedNewtonRatioBelowOne =
  BishopP.p<q⇒p⋆<q⋆
    (+ 1 / 200) 1ℚᵘ
    (RawQ.*<* (ℤ.+<+ (ℕP.≤ᵇ⇒≤ tt)))

bishopSelectedNewtonConstantNonnegative :
  BishopReal._≤_ BishopReal.0ℝ bishopSelectedNewtonIncrementConstant
bishopSelectedNewtonConstantNonnegative =
  BishopP.p≤q⇒p⋆≤q⋆
    0ℚᵘ (+ 1 / 15000)
    (RawP.nonNegative⁻¹ (+ 1 / 15000))

bishopSelectedNewtonGeometricInputs :
  Geometric.BishopScaledGeometricInputs
    bishopSelectedNewtonIncrementConstant
    bishopSelectedNewtonRatio
bishopSelectedNewtonGeometricInputs = record
  { Geometric.constantNonnegative =
      bishopSelectedNewtonConstantNonnegative
  ; Geometric.ratioInputs = record
      { Unit.ratioNonnegative = bishopSelectedNewtonRatioNonnegative
      ; Unit.ratioBelowOne = bishopSelectedNewtonRatioBelowOne
      }
  }


------------------------------------------------------------------------
-- ATTACHED P1 NEWTON EXACT FINITE ARITHMETIC. These inequalities are
-- LITERAL rational endpoint facts; their identification with Bishop
-- expC derivative and disk enclosures remains a separate source proof.
------------------------------------------------------------------------

selectedNewtonDerivativeUpper : ℚ
selectedNewtonDerivativeUpper = + 7 / 1500

selectedNewtonDerivativeUpperIsBelowSelectedRatio :
  selectedNewtonDerivativeUpper ≤ (+ 1 / 200)
selectedNewtonDerivativeUpperIsBelowSelectedRatio =
  ℚP.≤ᵇ⇒≤ tt

selectedNewtonDerivativeProductExact :
  (+ 14 / 15) * (+ 1 / 200)
    ≡ selectedNewtonDerivativeUpper
selectedNewtonDerivativeProductExact = refl

selectedNewtonCenterImageUpper : ℚ
selectedNewtonCenterImageUpper = + 1 / 15000

selectedNewtonCenterImageFromResidual :
  (+ 2 / 3) * (+ 1 / 10000)
    ≡ selectedNewtonCenterImageUpper
selectedNewtonCenterImageFromResidual = refl

selectedNewtonDiskImageUpper : ℚ
selectedNewtonDiskImageUpper = + 27 / 300000

selectedNewtonDiskImageUpperExact :
  selectedNewtonDerivativeUpper * newtonRadius
    + selectedNewtonCenterImageUpper
  ≡ selectedNewtonDiskImageUpper
selectedNewtonDiskImageUpperExact = refl

selectedNewtonImageStrictMargin :
  selectedNewtonDiskImageUpper ≤ newtonRadius
selectedNewtonImageStrictMargin = ℚP.≤ᵇ⇒≤ tt

selectedKoenigsTightConstant : ℚ
selectedKoenigsTightConstant = + 552 / 125000

selectedKoenigsTightConstantExact :
  selectedModulusUpper * selectedLogSecondRemainder
    * selectedLogDiskRadius * selectedLogDiskRadius
  ≡ selectedKoenigsTightConstant
selectedKoenigsTightConstantExact = refl

selectedKoenigsTightConstantBelowMajorant :
  selectedKoenigsTightConstant ≤ selectedIncrementConstantUpper
selectedKoenigsTightConstantBelowMajorant = ℚP.≤ᵇ⇒≤ tt


------------------------------------------------------------------------
-- NEXT SOURCE SINE GATE: RATIONAL TWO-TERM ALTERNATING ENVELOPE.
-- At y0=133724/100000, 0 < y0^2/6 < 1/3 and
--  y0-y0^3/6 > 1/2.
--
-- These are exact Data.Rational inequalities. The Bishop sine lower
-- bound sin_B(y0)>=y0-y0^3/6 still requires reusing the original
-- concrete factorial-term identification and proving decreasing
-- magnitudes at this y0 (the old half-radius lemma does NOT apply).
------------------------------------------------------------------------

selectedSineSuccessorRatio : ℚ
selectedSineSuccessorRatio =
  centerImag * centerImag * (+ 1 / 6)

selectedSineCubicLowerRational : ℚ
selectedSineCubicLowerRational =
  centerImag -
    ((centerImag * centerImag) * centerImag * (+ 1 / 6))

selectedSineSuccessorBelowOneThird :
  selectedSineSuccessorRatio ≤ (+ 1 / 3)
selectedSineSuccessorBelowOneThird = ℚP.≤ᵇ⇒≤ tt

selectedSineCubicLowerAboveHalf :
  (+ 1 / 2) ≤ selectedSineCubicLowerRational
selectedSineCubicLowerAboveHalf = ℚP.≤ᵇ⇒≤ tt

selectedSineCubicLowerPositive :
  zeroQ ≤ selectedSineCubicLowerRational
selectedSineCubicLowerPositive = ℚP.≤ᵇ⇒≤ tt


------------------------------------------------------------------------
-- STRONGER LOG TAIL FROM THE ORIGINAL POWER-SERIES COEFFICIENTS.
--
-- For |p| >= 27/20 and |t| <= 1/10, the local relative radius is
-- |u|=|t/p| <= 2/27.  Pure coefficient comparison gives
--
--   |log(1+u)-u| <= |u|^2/[2(1-|u|)]
--               <= (8/27)|t|^2.
--
-- This uses only the finite positive geometric tail plus the actual
-- Bishop log-series limit: no Lagrange integral or derivative source.
-- The comparisons BELOW are fully rational; transporting the bound to
-- the original componentwise Bishop complex logarithm remains open.
------------------------------------------------------------------------

selectedRelativeLogRadius : ℚ
selectedRelativeLogRadius = + 2 / 27

selectedRelativeRadiusExact :
  selectedLogDiskRadius * (+ 20 / 27)
    ≡ selectedRelativeLogRadius
selectedRelativeRadiusExact = refl

selectedRelativeRadiusBelowOne :
  selectedRelativeLogRadius ≤ (+ 1 / 1)
selectedRelativeRadiusBelowOne = ℚP.≤ᵇ⇒≤ tt

selectedLogSecondRemainderFromSeries : ℚ
selectedLogSecondRemainderFromSeries = + 8 / 27

selectedLogSecondRemainderSeriesExact :
  (+ 2 / 1) * selectedModulusLower *
    selectedDiskModulusLower *
    selectedLogSecondRemainderFromSeries
  ≡ (+ 1 / 1)
selectedLogSecondRemainderSeriesExact = refl

selectedLogSeriesRemainderImprovesIntegral :
  selectedLogSecondRemainderFromSeries ≤ selectedLogSecondRemainder
selectedLogSeriesRemainderImprovesIntegral = ℚP.≤ᵇ⇒≤ tt

selectedLogSeriesIncrementConstant : ℚ
selectedLogSeriesIncrementConstant = + 23 / 5625

selectedLogSeriesIncrementConstantExact :
  selectedModulusUpper * selectedLogSecondRemainderFromSeries *
    selectedLogDiskRadius * selectedLogDiskRadius
  ≡ selectedLogSeriesIncrementConstant
selectedLogSeriesIncrementConstantExact = refl

selectedLogSeriesIncrementBelowMajorant :
  selectedLogSeriesIncrementConstant ≤ selectedIncrementConstantUpper
selectedLogSeriesIncrementBelowMajorant = ℚP.≤ᵇ⇒≤ tt

selectedNewtonTotalDisplacementBound : ℚ
selectedNewtonTotalDisplacementBound = + 1 / 14930

selectedNewtonTotalDisplacementExact :
  selectedNewtonCenterImageUpper * (+ 1500 / 1493)
    ≡ selectedNewtonTotalDisplacementBound
selectedNewtonTotalDisplacementExact = refl


------------------------------------------------------------------------
-- ACTUAL NEWTON LIMIT COORDINATE MARGIN TARGETS.
--
-- From the genuine Bishop total Newton displacement bound
-- |p-p0| <= 1/14930, each coordinate admits <= 1/14930.
-- The following entirely rational squares then prove
--  (27/20)^2 < |p|^2 < (69/50)^2
-- by Bishop coordinate order and nonnegative square monotonicity.
--
-- The missing limit-level Cauchy distance/coordinate comparison
-- remains a separate theorem, not supplied by these endpoint checks.
------------------------------------------------------------------------

newtonCoordinateLowerReal newtonCoordinateLowerImag : ℚ
newtonCoordinateLowerReal =
  centerReal - selectedNewtonTotalDisplacementBound
newtonCoordinateLowerImag =
  centerImag - selectedNewtonTotalDisplacementBound

newtonCoordinateUpperReal newtonCoordinateUpperImag : ℚ
newtonCoordinateUpperReal =
  centerReal + selectedNewtonTotalDisplacementBound
newtonCoordinateUpperImag =
  centerImag + selectedNewtonTotalDisplacementBound

newtonCoordinateLowerNormSquare : ℚ
newtonCoordinateLowerNormSquare =
  (newtonCoordinateLowerReal * newtonCoordinateLowerReal)
  + (newtonCoordinateLowerImag * newtonCoordinateLowerImag)

newtonCoordinateUpperNormSquare : ℚ
newtonCoordinateUpperNormSquare =
  (newtonCoordinateUpperReal * newtonCoordinateUpperReal)
  + (newtonCoordinateUpperImag * newtonCoordinateUpperImag)

selectedNewtonLimitLowerMarginFromCoordinates :
  (selectedModulusLower * selectedModulusLower)
    ≤ newtonCoordinateLowerNormSquare
selectedNewtonLimitLowerMarginFromCoordinates =
  ℚP.≤ᵇ⇒≤ tt

selectedNewtonLimitUpperMarginFromCoordinates :
  newtonCoordinateUpperNormSquare
    ≤ (selectedModulusUpper * selectedModulusUpper)
selectedNewtonLimitUpperMarginFromCoordinates =
  ℚP.≤ᵇ⇒≤ tt
