{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109WardFloorToBetaJetExact where

------------------------------------------------------------------------
-- ROW A GAUSSIAN PRODUCER: POSITIVE PATCH -> CMP109 MIXED-JET BETA FLOOR
--
-- Existing exact owners now provide both sides of the source weld:
--
--   * one literal positive Gaussian patch gives the fixed Ward floor
--         b_Ward <= global Gaussian lower sum;
--
--   * CMP109 (5.36)--(5.41) identifies beta with the negative mixed second
--     coefficient of the off-diagonal polarization two-jet.
--
-- Therefore the final Gaussian assembly only needs the literal integral
-- comparison saying that the configured Gaussian lower sum is below that SAME
-- mixed-jet beta coefficient.  This file proves the transitive composition.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral
import DASHI.Physics.YangMills.BalabanCMP109MixedDerivativeBetaExtractionExact as Jet
import DASHI.Physics.YangMills.BalabanCMP109WardFloorFromPositivePatchExact as PatchFloor
import DASHI.Physics.YangMills.BalabanCMP109GaussianPositivePatchCorrectionExact as Patch
import DASHI.Physics.YangMills.BalabanYM4RowAWardFloorCanonicalGateExact as Ward

record CMP109GaussianPatchToBetaJet : Set₁ where
  field
    patchData : PatchFloor.WardCertifiedCMP109GaussianPatch
    jetData : Jet.CMP109OffDiagonalSecondJetData

    -- Literal same-object bridge: the configured Gaussian integral represented
    -- by the patch cover is a lower bound for the SAME off-diagonal mixed beta
    -- coefficient extracted from CMP109 Sect. 5.
    globalGaussianLowerBelowBeta :
      Integral.boxLowerSum
        (Patch.patch (PatchFloor.literalPatch patchData)
          Agda.Builtin.List.∷
          Patch.complement (PatchFloor.literalPatch patchData))
      ≤ Jet.beta jetData

open CMP109GaussianPatchToBetaJet public

wardFloorBelowCMP109Beta :
  (dataSet : CMP109GaussianPatchToBetaJet) →
  Ward.wardGaussianFloor ≤ Jet.beta (jetData dataSet)
wardFloorBelowCMP109Beta dataSet =
  ℚP.≤-trans
    (PatchFloor.wardFloorBelowGlobalGaussianLower (patchData dataSet))
    (globalGaussianLowerBelowBeta dataSet)

rowAWardFloorToCMP109BetaJetLevel : ProofLevel
rowAWardFloorToCMP109BetaJetLevel = machineChecked

-- Physical source seam: prove the configured box cover is an enclosure of the
-- literal constrained-Gaussian mixed two-jet appearing in CMP109's polarization
-- coefficient.  The positivity/floor passage itself is now theorem-owned.
literalCMP109GaussianIntegralToMixedJetIdentificationLevel : ProofLevel
literalCMP109GaussianIntegralToMixedJetIdentificationLevel = conditional
