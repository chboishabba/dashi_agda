module DASHI.Physics.YangMills.BalabanRegular240EncodedFourOrbitSumExact where

-- Source-preserving connector: existing exact rational finite orbit theorem
-- and the new proof-insensitive full-240 support × F4 half-root encoding.
--
-- NOT a re-proof of the 64/96/64/16 reduction.
-- NOT the currently unpaid Bałaban literal scalar integrand certificate.
-- This is a genuine typed same-contribution weld, not four unrelated
-- representative values or a new 240-term manual certificate.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _/_)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Action
import DASHI.Physics.YangMills.BalabanClayT4HypercubicRepresentativeSumExact as Existing
import DASHI.Physics.YangMills.BalabanRegular240SupportHalfExact as Encoded
import DASHI.Physics.YangMills.BalabanRegular240PointwisePermutationModuleExact as Coeff

-- Any original rational box contribution has a canonical
-- proof-insensitive interpretation on the proof-carrying regular carrier.
sourceCoefficients :
  (contribution : Grid.GridCell4 → ℚ) →
  Coeff.OriginalCoefficients ℚ
sourceCoefficients contribution = record
  { Coeff.value = λ c → contribution (Encoded.original c)
  ; Coeff.proofInsensitive = λ x y eq → cong contribution eq
  }

-- Use the *actual source* encoded rational observable, rather than a
-- separately asserted target-side function with no source provenance.
encodedContribution :
  (contribution : Grid.GridCell4 → ℚ) →
  Encoded.SupportHalf240 → ℚ
encodedContribution contribution p =
  Coeff.encodedValue (Coeff.encodeCoefficients
    (sourceCoefficients contribution)) p

-- The encoded contribution is definitionally the original contribution
-- evaluated on the uniquely reconstructed original cell.
encodedContributionIsOriginal :
  (contribution : Grid.GridCell4 → ℚ)
  (p : Encoded.SupportHalf240) →
  encodedContribution contribution p ≡
  contribution (Encoded.original (Encoded.decode240 p))
encodedContributionIsOriginal contribution p = refl

-- Conversely encoding a selected original cell does not change its
-- literal *rational* box contribution, even when its witness for
-- positive outer degree is an arbitrary Nat equality proof.
regularContributionRoundTrip :
  (contribution : Grid.GridCell4 → ℚ)
  (cell : Encoded.Regular240) →
  encodedContribution contribution (Encoded.encode240 cell) ≡
  contribution (Encoded.original cell)
regularContributionRoundTrip contribution cell =
  Coeff.originalCoefficientRoundTrip
    (sourceCoefficients contribution) cell

-- Generator-invariance is exactly the original proof obligation.
-- The new F4-half-root geometry does not invent or discharge it.
record OriginalRationalOrbitAdmission
  (contribution : Grid.GridCell4 → ℚ) : Set where
  field
    sourceGeneratorInvariant :
      Action.GeneratorInvariantRationalContribution contribution
open OriginalRationalOrbitAdmission public

-- Existing theorem consumes ORIGINAL generated 240-cell list and the
-- SAME source contribution. The new encoded geometry transports that
-- contribution without changing any of its four representative values.
encodedSourceInvariantFourRepresentativeSum :
  (contribution : Grid.GridCell4 → ℚ)
  (admitted : OriginalRationalOrbitAdmission contribution) →
  Sums.sumRational Grid.regularGridCells contribution
  ≡ (+ 64 / 1) * contribution Orbit.oneOuterRepresentative
    + (+ 96 / 1) * contribution Orbit.twoOuterRepresentative
    + (+ 64 / 1) * contribution Orbit.threeOuterRepresentative
    + (+ 16 / 1) * contribution Orbit.fourOuterRepresentative
encodedSourceInvariantFourRepresentativeSum contribution admitted =
  Existing.regularInvariantSumIsFourRepresentatives
    (sourceGeneratorInvariant admitted)

-- The primary P0 physical leaf remains: the actual selected
-- LiteralScalarIntegrandExpression has to provide seven
-- source-derived generator equalities and box-trig environment
-- compatibility. A rational contribution can be supplied only after
-- validated analytic interval/physical source admission.
