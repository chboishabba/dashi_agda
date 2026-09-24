module DASHI.Physics.Closure.NSWholeSpaceR3PhysicalKernelProjectedQWeldExact where

------------------------------------------------------------------------
-- A / PHYSICAL RESOLVENT KERNEL -> OFF-DIAGONAL PROJECTED GRAM q-BOUND
--
-- IMPORTANT CORRECTION
-- --------------------
-- The R290-style Gram is signed.  It must NOT be forced through a record that
-- assumes Gram nonnegativity merely because the diagonal special case is a
-- norm-square.
--
-- The canonical continuous object is therefore a same-output PAIR of projected
-- cells.  Its scalar is
--
--   g_{alpha beta} = 2 Re <P_xi N_alpha , P_xi N_beta>,
--
-- and the existing Hermitian-Young/Leray theorem proves directly
--
--   g_{alpha beta} <= |xi|^2 M_{alpha beta}.
--
-- This is the exact signed upper estimate needed by the saturation branch.
-- No |g| observer and no Gram-positive hypothesis are introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSTriadKNEuclideanCanonicalProjectedGramPairExact as Pair

record PhysicalKernelProjectedGramWeld
    {S : Canonical.CanonicalNSSemantics}
    {trajectory : Physical.EuclideanFourierTrajectory S}
    (kernel : Physical.EuclideanPhysicalResolventKernel trajectory)
    (point : Heat.PuncturedEuclideanFrequency)
    (I : Euclidean.EuclideanInteraction) : Set₁ where
  constructor physical-kernel-projected-gram-weld
  field
    projectedPair :
      Pair.CanonicalProjectedGramPair trajectory point

    gramScalarIsProjectedPairGram :
      BishopReal._≃_
        (Physical.gramScalar kernel I)
        (Pair.pairGram projectedPair)

open PhysicalKernelProjectedGramWeld public

kernelProjectedGramOutputQBound :
  ∀ {S trajectory kernel point I} →
  (weld :
    PhysicalKernelProjectedGramWeld
      {S} {trajectory} kernel point I) →
  BishopReal._≤_
    (Physical.gramScalar kernel I)
    (BishopReal._*_
      (Heat.frequencyNormSquared (Heat.frequency point))
      (Pair.pairMajorant (projectedPair weld)))
kernelProjectedGramOutputQBound weld =
  BishopP.≤-respˡ-≃
    (gramScalarIsProjectedPairGram weld)
    (Pair.pairGramOutputQBound (projectedPair weld))

kernelProjectedGramMajorantNonnegative :
  ∀ {S trajectory kernel point I} →
  (weld :
    PhysicalKernelProjectedGramWeld
      {S} {trajectory} kernel point I) →
  BishopReal.NonNegative
    (Pair.pairMajorant (projectedPair weld))
kernelProjectedGramMajorantNonnegative weld =
  Pair.pairMajorantNonnegative (projectedPair weld)

kernelGramQEstimateDerivedFromSameObjectWeld : Bool
kernelGramQEstimateDerivedFromSameObjectWeld = true

kernelGramPositivityRequired : Bool
kernelGramPositivityRequired = false

kernelGramAbsoluteValueIntroduced : Bool
kernelGramAbsoluteValueIntroduced = false

offDiagonalProjectedGramSupported : Bool
offDiagonalProjectedGramSupported = true

clayPromotion : Bool
clayPromotion = false

kernelGramQEstimateDerivedFromSameObjectWeldIsTrue :
  kernelGramQEstimateDerivedFromSameObjectWeld ≡ true
kernelGramQEstimateDerivedFromSameObjectWeldIsTrue = refl

kernelGramPositivityRequiredIsFalse :
  kernelGramPositivityRequired ≡ false
kernelGramPositivityRequiredIsFalse = refl

kernelGramAbsoluteValueIntroducedIsFalse :
  kernelGramAbsoluteValueIntroduced ≡ false
kernelGramAbsoluteValueIntroducedIsFalse = refl

offDiagonalProjectedGramSupportedIsTrue :
  offDiagonalProjectedGramSupported ≡ true
offDiagonalProjectedGramSupportedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
