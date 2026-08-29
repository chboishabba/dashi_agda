{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109WardFloorToBetaJetExact where

------------------------------------------------------------------------
-- ROW A GAUSSIAN PRODUCER: POSITIVE PATCH -> CMP109 MIXED-JET BETA FLOOR
------------------------------------------------------------------------

open import Agda.Builtin.List using (_∷_)
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

    globalGaussianLowerBelowBeta :
      Integral.boxLowerSum
        (Patch.patch (PatchFloor.literalPatch patchData)
          ∷ Patch.complement (PatchFloor.literalPatch patchData))
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

literalCMP109GaussianIntegralToMixedJetIdentificationLevel : ProofLevel
literalCMP109GaussianIntegralToMixedJetIdentificationLevel = conditional
