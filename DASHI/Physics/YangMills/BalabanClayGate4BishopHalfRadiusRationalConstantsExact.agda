module DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRationalConstantsExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([])
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 1ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact rational constants for the Bishop sine/cosine estimates on |x|<=1/2.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- Master's thesis, University of Canterbury (2022).
-- arXiv:2205.08354. No DOI recorded.
--
-- Since x^2 <= 1/4, the successive absolute series-term ratios satisfy the
-- fixed targets
--
--   sine:   (1/4)/6 = 1/24,
--   cosine: (1/4)/2 = 1/8.
--
-- The elementary sine lower envelope at theta/2 additionally uses
--
--   1 - (1/4)/24 = 95/96.
--
-- The order comparisons x^2<=1/4 and the alternating-tail theorem remain
-- constructive-real obligations; the rational normalization is closed here.
------------------------------------------------------------------------

quarter six two twentyFour : ℚ
quarter = + 1 / 4
six = + 6 / 1
two = + 2 / 1
twentyFour = + 24 / 1

oneTwentyFourth oneEighth ninetyFiveNinetySix : ℚ
oneTwentyFourth = + 1 / 24
oneEighth = + 1 / 8
ninetyFiveNinetySix = + 95 / 96

sineSuccessiveRatioNormalization :
  quarter / six ≡ oneTwentyFourth
sineSuccessiveRatioNormalization = ℚRing.solve []

cosineSuccessiveRatioNormalization :
  quarter / two ≡ oneEighth
cosineSuccessiveRatioNormalization = ℚRing.solve []

normalizedSineDenominatorLowerConstant :
  1ℚ - (quarter / twentyFour) ≡ ninetyFiveNinetySix
normalizedSineDenominatorLowerConstant = ℚRing.solve []

record HalfRadiusSeriesOrderInputs
    (Real : Set) : Set₁ where
  field
    embedRational : ℚ → Real
    absolute square : Real → Real
    LessEqual : Real → Real → Set

    x : Real
    xInsideHalfBall :
      LessEqual (absolute x) (embedRational (+ 1 / 2))
    squareInsideQuarter :
      LessEqual (square x) (embedRational quarter)

    sineTermRatioBelowTwentyFourth : Set
    sineTermRatioBelowTwentyFourthEvidence :
      sineTermRatioBelowTwentyFourth

    cosineTermRatioBelowEighth : Set
    cosineTermRatioBelowEighthEvidence :
      cosineTermRatioBelowEighth

open HalfRadiusSeriesOrderInputs public

bishopHalfRadiusRationalNormalizationLevel : ProofLevel
bishopHalfRadiusRationalNormalizationLevel = machineChecked

bishopHalfRadiusSeriesOrderInputsLevel : ProofLevel
bishopHalfRadiusSeriesOrderInputsLevel = conditional
