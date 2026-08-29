{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109PositivePatchFloorRound104Exact where

------------------------------------------------------------------------
-- ROUND104 A1: A POSITIVE PATCH MUST CARRY AN ACTUAL POSITIVE LOWER NUMBER
--
-- The older source-facing patch record documented `patchLowerPositive : Set`.
-- That is not evidence that its rational lower contribution is positive.  This
-- strict wrapper keeps the existing normalized-trace/source-coordinate work but
-- requires the numerical proposition itself:
--
--       0 < lowerContribution(patch).
--
-- Together with the already-proved nonnegative complement inequality this gives
-- an actual positive rational lower bound for the complete Gaussian trace.  Thus
-- once the source patch is constructed, positivity of the Gaussian floor is no
-- longer an additional theorem.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral
import DASHI.Physics.YangMills.BalabanCMP109GaussianPositivePatchCorrectionExact as Patch

record StrictCMP109GaussianPositivePatch : Set₁ where
  field
    sourcePatch : Patch.CMP109LiteralGaussianPositivePatch

    -- Evidence-bearing replacement for the old documentation-only Set field.
    patchLowerStrictlyPositive :
      0ℚ < Integral.lowerContribution (Patch.patch sourcePatch)

open StrictCMP109GaussianPositivePatch public

globalGaussianLower : StrictCMP109GaussianPositivePatch → ℚ
globalGaussianLower dataSet =
  Integral.boxLowerSum
    (Patch.patch (sourcePatch dataSet) ∷ Patch.complement (sourcePatch dataSet))
  where
    open import Agda.Builtin.List using (_∷_)

globalGaussianLowerPositive :
  (dataSet : StrictCMP109GaussianPositivePatch) →
  0ℚ < globalGaussianLower dataSet
globalGaussianLowerPositive dataSet =
  ℚP.<-≤-trans
    (patchLowerStrictlyPositive dataSet)
    (Patch.globalGaussianLowerFromOnePatch (sourcePatch dataSet))

-- The lower endpoint itself is now a reusable floor, not just a proof label.
gaussianFloor : StrictCMP109GaussianPositivePatch → ℚ
gaussianFloor = globalGaussianLower

gaussianFloorPositive :
  (dataSet : StrictCMP109GaussianPositivePatch) →
  0ℚ < gaussianFloor dataSet
gaussianFloorPositive = globalGaussianLowerPositive

positivePatchToStrictGaussianFloorLevel : ProofLevel
positivePatchToStrictGaussianFloorLevel = machineChecked

-- Remaining physics is exactly the literal positive patch construction: W+Q+R
-- must be the constrained CMP109 Gaussian first variation, and the selected box
-- must be part of that same normalized trace.  Once its rational lower endpoint
-- is proved positive, this module supplies b_->0 automatically.
literalStrictCMP109GaussianPatchInstantiationLevel : ProofLevel
literalStrictCMP109GaussianPatchInstantiationLevel = conditional
