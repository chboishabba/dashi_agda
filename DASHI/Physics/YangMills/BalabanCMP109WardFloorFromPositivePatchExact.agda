{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109WardFloorFromPositivePatchExact where

------------------------------------------------------------------------
-- ROW A GAUSSIAN PRODUCER: ONE PATCH LOWER INEQUALITY -> FIXED WARD FLOOR
--
-- Existing source-facing code already proves that for a literal CMP109 Gaussian
-- positive patch with nonnegative complement,
--
--   lowerContribution(patch) <= globalGaussianLower.
--
-- The Lean cross-prover lane has fixed the desired Gaussian floor at
--
--   b_Ward = 1 / 8388608.
--
-- Therefore the entire numerical Gaussian-floor weld reduces to one exact
-- statement about the SAME configured Brillouin box:
--
--   b_Ward <= lowerContribution(patch).
--
-- This module proves the composition.  No separate global integral estimate is
-- needed once the patch enclosure and complement sign are source-identified.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral
import DASHI.Physics.YangMills.BalabanCMP109GaussianPositivePatchCorrectionExact as Patch
import DASHI.Physics.YangMills.BalabanYM4RowAWardFloorCanonicalGateExact as Ward

record WardCertifiedCMP109GaussianPatch : Set₁ where
  field
    literalPatch : Patch.CMP109LiteralGaussianPositivePatch
    wardFloorBelowPatchContribution :
      Ward.wardGaussianFloor
      ≤ Integral.lowerContribution (Patch.patch literalPatch)

open WardCertifiedCMP109GaussianPatch public

wardFloorBelowGlobalGaussianLower :
  (dataSet : WardCertifiedCMP109GaussianPatch) →
  Ward.wardGaussianFloor
  ≤ Integral.boxLowerSum
      (Patch.patch (literalPatch dataSet)
        Agda.Builtin.List.∷ Patch.complement (literalPatch dataSet))
wardFloorBelowGlobalGaussianLower dataSet =
  ℚP.≤-trans
    (wardFloorBelowPatchContribution dataSet)
    (Patch.globalGaussianLowerFromOnePatch (literalPatch dataSet))

rowAWardFloorFromLiteralPatchLevel : ProofLevel
rowAWardFloorFromLiteralPatchLevel = machineChecked

-- Physical/source frontier after this adapter is exact and scalar:
--
-- 1. construct the literal CMP109/CMP99 W/Q/R mixed component on one configured
--    positive-volume box;
-- 2. prove the box enclosure's `lowerContribution` is at least 1/8388608;
-- 3. prove the complement lower sum is nonnegative (already a field of the
--    literal-patch carrier).
--
-- The passage from that one local box inequality to the global Gaussian floor is
-- theorem-owned here.
literalCMP109WardPatchLowerInequalityLevel : ProofLevel
literalCMP109WardPatchLowerInequalityLevel = conditional
