module DASHI.Physics.Closure.NSClayFacingAPhysicalSameObjectCutExact where

------------------------------------------------------------------------
-- CLAY-FACING A / ACTIVE PHYSICAL SAME-OBJECT CUT
--
-- Do not make standard measure theory the research problem.
--
-- The near-origin scalar/Gram estimate is already theorem-bearing in
-- NSWholeSpacePhysicalKernelSaturationOriginExact.  The active A work is to
-- identify the ACTUAL Euclidean NS resolvent kernel with that theorem's
-- physical cells and to connect its majorant to the finite-energy convolution
-- currency.  At high output frequency the scale-relative resolvent curvature
-- is already proved; again the remaining work is the physical identification.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal

import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSWholeSpacePhysicalKernelSaturationOriginExact as Origin
import DASHI.Physics.Closure.NSTriadKNEuclideanCenteredResolventScaleRelativeExact as High

data APhysicalResidual : Set where
  identifyKernelProjectedGram : APhysicalResidual
  identifyKernelSaturationCoefficient : APhysicalResidual
  identifyPhysicalStateMajorantWithFiniteEnergyConvolution : APhysicalResidual
  identifyHighFrequencyPhysicalEnvelope : APhysicalResidual
  noPhysicalResidual : APhysicalResidual

record PhysicalNearOriginSameObjectData
    {S : Canonical.CanonicalNSSemantics}
    {trajectory : Physical.EuclideanFourierTrajectory S}
    (kernel : Physical.EuclideanPhysicalResolventKernel trajectory)
    (fluid : Heat.PositiveViscosity) : Set₁ where
  field
    pointFor :
      Euclidean.EuclideanInteraction →
      Heat.PuncturedEuclideanFrequency

    saturationWeld :
      (I : Euclidean.EuclideanInteraction) →
      Origin.PhysicalKernelSaturationOriginWeld
        kernel fluid (pointFor I) I

open PhysicalNearOriginSameObjectData public

nearOriginPhysicalBound :
  ∀ {S trajectory kernel fluid} →
  (D : PhysicalNearOriginSameObjectData
    {S} {trajectory} kernel fluid) →
  (I : Euclidean.EuclideanInteraction) →
  BishopReal._≤_
    (Physical.physicalCenteredResolventCorrection kernel I)
    (BishopReal._*_
      (DASHI.Physics.Closure.NSWholeSpaceProjectedSaturationOriginBoundExact.viscosityInverse
        (Origin.saturationCell (saturationWeld D I)))
      (DASHI.Physics.Closure.NSWholeSpaceProjectedSaturationOriginBoundExact.majorant
        (Origin.saturationCell (saturationWeld D I))))
nearOriginPhysicalBound D I =
  Origin.physicalKernelSaturationOriginBound (saturationWeld D I)

------------------------------------------------------------------------
-- High-frequency physical identification.
------------------------------------------------------------------------

record PhysicalHighFrequencyEnvelopeData : Set₁ where
  field
    outputHeatRate : ℚ
    shellHeatFloor : ℚ

    scaleFloor : High.EuclideanOutputScaleFloor

    outputHeatRateMeaning :
      High.outputHeatRate scaleFloor ≡ outputHeatRate

    shellHeatFloorMeaning :
      High.shellHeatFloor scaleFloor ≡ shellHeatFloor

open PhysicalHighFrequencyEnvelopeData public

highFrequencyCurvatureBound :
  (D : PhysicalHighFrequencyEnvelopeData) →
  DASHI.Physics.Closure.NSTriadKNCenteredResolventSecondOrderEnvelopeExact.resolventTransportCurvature
    (outputHeatRate D)
  ≤ High.scaleRelativeCurvature (shellHeatFloor D)
highFrequencyCurvatureBound D
  rewrite sym (outputHeatRateMeaning D)
        | sym (shellHeatFloorMeaning D) =
  High.shellRelativeCurvatureBound (scaleFloor D)

------------------------------------------------------------------------
-- Clay-facing trust split.
------------------------------------------------------------------------

aNearOriginAnalyticEstimateClosed : Bool
aNearOriginAnalyticEstimateClosed = true

aHighFrequencyCurvatureEstimateClosed : Bool
aHighFrequencyCurvatureEstimateClosed = true

aStandardFubiniYoungTailTheoremsAreNovelResearch : Bool
aStandardFubiniYoungTailTheoremsAreNovelResearch = false

aActualKernelSameObjectInstantiationClosedHere : Bool
aActualKernelSameObjectInstantiationClosedHere = false

aFiniteEnergyMajorantIdentificationClosedHere : Bool
aFiniteEnergyMajorantIdentificationClosedHere = false

currentAPhysicalResidual : APhysicalResidual
currentAPhysicalResidual = identifyKernelProjectedGram

aNearOriginAnalyticEstimateClosedIsTrue :
  aNearOriginAnalyticEstimateClosed ≡ true
aNearOriginAnalyticEstimateClosedIsTrue = refl

aHighFrequencyCurvatureEstimateClosedIsTrue :
  aHighFrequencyCurvatureEstimateClosed ≡ true
aHighFrequencyCurvatureEstimateClosedIsTrue = refl

aStandardFubiniYoungTailTheoremsAreNovelResearchIsFalse :
  aStandardFubiniYoungTailTheoremsAreNovelResearch ≡ false
aStandardFubiniYoungTailTheoremsAreNovelResearchIsFalse = refl
