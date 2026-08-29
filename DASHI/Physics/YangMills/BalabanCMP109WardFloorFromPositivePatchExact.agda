{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109WardFloorFromPositivePatchExact where

------------------------------------------------------------------------
-- ROW A GAUSSIAN PRODUCER: ONE PATCH LOWER INEQUALITY -> FIXED WARD FLOOR
------------------------------------------------------------------------

open import Agda.Builtin.List using (_∷_)
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
        ∷ Patch.complement (literalPatch dataSet))
wardFloorBelowGlobalGaussianLower dataSet =
  ℚP.≤-trans
    (wardFloorBelowPatchContribution dataSet)
    (Patch.globalGaussianLowerFromOnePatch (literalPatch dataSet))

rowAWardFloorFromLiteralPatchLevel : ProofLevel
rowAWardFloorFromLiteralPatchLevel = machineChecked

literalCMP109WardPatchLowerInequalityLevel : ProofLevel
literalCMP109WardPatchLowerInequalityLevel = conditional
