module DASHI.Physics.YangMills.BalabanCMP109EncodedPhysicalSymmetryWeldExact where

-- SAME-source compositional P0 weld. Reuses CMP109 Section 5 Eq.
-- (5.6) adjacent coordinate permutations and Eq. (5.7) reflections
-- *after source-specific scalar projection*.
--
-- The physical theorem has two real open leaves:
-- (1) identify the literal Wilson/ghost/Haar scalar from the blocked
--    vacuum-polarisation tensor to instantiate Source symmetry;
-- (2) prove box-trigonometric environment covariance for actual
--    recursively evaluated diagram expression.
--
-- NO generic set-equality fields are promoted to physical evidence.
-- Original four-orbit rational sum is reused, not re-proved.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _/_)

import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Action
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Orbit
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanCMP109VacuumPolarizationHypercubicSourceSymmetryExact as Source
import DASHI.Physics.YangMills.BalabanRegular240SupportHalfExact as Encoded
import DASHI.Physics.YangMills.BalabanRegular240EncodedFourOrbitSumExact as SumWeld

-- A single source-owned, post-projection CMP109 Euclidean symmetry
-- supplies all seven exact rational generator equalities.
cmp109ScalarBuildsEncodedOrbitAdmission :
  (contribution : Grid.GridCell4 → ℚ) →
  Source.CMP109ScalarEuclideanSymmetry contribution →
  SumWeld.OriginalRationalOrbitAdmission contribution
cmp109ScalarBuildsEncodedOrbitAdmission contribution source = record
  { sourceGeneratorInvariant = Source.asGeneratorInvariant source }

-- This same original source scalar is B4-invariant on the independent
-- 15-support-mask × 16-half-sign regular 240-cell representation.
cmp109ScalarEncodedIndependentB4 :
  (contribution : Grid.GridCell4 → ℚ) →
  (symmetry : Source.CMP109ScalarEuclideanSymmetry contribution) →
  (g : Action.HypercubicGenerator) (p : Encoded.SupportHalf240) →
  SumWeld.encodedContribution contribution (Encoded.actIndependent240 g p) ≡
  SumWeld.encodedContribution contribution p
cmp109ScalarEncodedIndependentB4 contribution symmetry g p =
  SumWeld.encodedIndependentB4Invariant
    contribution (Source.asGeneratorInvariant symmetry) g p

-- No new four representatives or proxies: invoke the EXACT
-- previous rational finite summation theorem on original generated cells.
cmp109ScalarGivesExactFourOrbitSum :
  (contribution : Grid.GridCell4 → ℚ) →
  (symmetry : Source.CMP109ScalarEuclideanSymmetry contribution) →
  Sums.sumRational Grid.regularGridCells contribution
  ≡ (+ 64 / 1) * contribution Orbit.oneOuterRepresentative
    + (+ 96 / 1) * contribution Orbit.twoOuterRepresentative
    + (+ 64 / 1) * contribution Orbit.threeOuterRepresentative
    + (+ 16 / 1) * contribution Orbit.fourOuterRepresentative
cmp109ScalarGivesExactFourOrbitSum contribution symmetry =
  SumWeld.encodedSourceInvariantFourRepresentativeSum
    contribution
    (cmp109ScalarBuildsEncodedOrbitAdmission contribution symmetry)

-- Boundaries:
--   Source.CMP109ScalarEuclideanSymmetry is required as a proof for
--   the ACTUAL source-projected rational scalar, not assumed universal.
--   This does NOT instantiate
--   Cert.LiteralRegularIntegrandB4GeneratorCertificate scalarData,
--   Eval.LiteralGeneratedBoxEvaluator or the underlying YM physical
--   continuum / OS Hamiltonian / spectral mass-gap gates.
