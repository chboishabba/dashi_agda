module DASHI.Cognition.PNF.OrientedZeroExpectedResidualRateExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

------------------------------------------------------------------------
-- EXPECTED CONDITIONAL RESIDUAL RATE
--
-- The local least widths over scalar {-1,0,+1} are 0,1,0 bits.  Therefore the
-- expected additional PNF residual rate under any scalar probability law is
-- exactly the probability mass of the scalar-zero fibre.
------------------------------------------------------------------------

record ScalarProbability : Set where
  constructor scalarProbability
  field
    negativeMass zeroMass positiveMass : ℚ
    negativeNonnegative : 0ℚ ≤ negativeMass
    zeroNonnegative : 0ℚ ≤ zeroMass
    positiveNonnegative : 0ℚ ≤ positiveMass
    normalized : negativeMass + zeroMass + positiveMass ≡ 1ℚ

open ScalarProbability public

expectedAdaptiveResidualBits : ScalarProbability → ℚ
expectedAdaptiveResidualBits law =
  negativeMass law * 0ℚ
  + zeroMass law * 1ℚ
  + positiveMass law * 0ℚ

expectedAdaptiveResidualBitsEqualZeroMass :
  (law : ScalarProbability) →
  expectedAdaptiveResidualBits law ≡ zeroMass law
expectedAdaptiveResidualBitsEqualZeroMass law = solve-∀

------------------------------------------------------------------------
-- A uniform standalone Wave4 code spends two bits regardless of scalar fibre.
-- We record the conditional saving symbolically rather than assuming a specific
-- distribution: adaptive expected rate is zeroMass, standalone rate is 2.
------------------------------------------------------------------------

standaloneWave4Bits : ℚ
standaloneWave4Bits = 1ℚ + 1ℚ

record AdaptiveRateIdentity (law : ScalarProbability) : Set where
  constructor adaptiveRateIdentity
  field
    adaptiveExpected : ℚ
    standaloneFixed : ℚ
    adaptiveIsZeroMass : adaptiveExpected ≡ zeroMass law
    standaloneIsTwo : standaloneFixed ≡ standaloneWave4Bits

canonicalAdaptiveRateIdentity :
  (law : ScalarProbability) → AdaptiveRateIdentity law
canonicalAdaptiveRateIdentity law =
  adaptiveRateIdentity
    (expectedAdaptiveResidualBits law)
    standaloneWave4Bits
    (expectedAdaptiveResidualBitsEqualZeroMass law)
    refl

------------------------------------------------------------------------
-- This is conditional coding relative to the retained scalar projection.  It
-- does not compare total end-to-end code length unless the scalar carrier's own
-- representation cost is also included in the objective.
------------------------------------------------------------------------
