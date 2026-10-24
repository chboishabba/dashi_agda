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
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (sym)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSWholeSpacePhysicalKernelSaturationOriginExact as Origin
import DASHI.Physics.Closure.NSWholeSpaceProjectedSaturationOriginBoundExact as SaturationBound
import DASHI.Physics.Closure.NSTriadKNCenteredResolventSecondOrderEnvelopeExact as Envelope
import DASHI.Physics.Closure.NSTriadKNEuclideanCenteredResolventScaleRelativeExact as High
import DASHI.Physics.Closure.NSTriadKNMurrayBishopGalerkinCoordinateSemanticsRound34Exact as BishopQ

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
      (SaturationBound.viscosityInverse
        (Origin.saturationCell (saturationWeld D I)))
      (SaturationBound.majorant
        (Origin.saturationCell (saturationWeld D I))))
nearOriginPhysicalBound D I =
  Origin.physicalKernelSaturationOriginBound (saturationWeld D I)

------------------------------------------------------------------------
-- ALL-REAL A1 HEAT FLOOR: constructive rational interpolation.
--
-- The legacy HighFrequencyEnvelopeData below requires a rational
-- `outputHeatRate` whose Bishop embedding EQUALS ν|xi|². This cannot
-- inhabit arbitrary physical real frequencies or arbitrary positive
-- real viscosity (consider ν=sqrt(2), xi=(1,0,0)). Do NOT infer a
-- universal same-object weld from it.
--
-- The correct all-real bridge is a positive rational STRICT LOWER
-- bound for the actual, same-frequency viscous heat rate. Murray/
-- Bishop constructive rational density already gives this without
-- classical choice or a global lattice gap. The remaining real
-- resolvent comparison and physical kernel identification are still
-- mathematical obligations; this theorem only pays the floor
-- existence step, with the original physical viscosity and frequency.
------------------------------------------------------------------------

physicalViscousHeatAdmitsPositiveRationalFloor :
  (fluid : Heat.PositiveViscosity) →
  (point : Heat.PuncturedEuclideanFrequency) →
  Σ BishopReal.ℝ
    (λ lower →
      BishopReal._<_ BishopReal.0ℝ lower ×
      BishopReal._<_ lower
        (Heat.viscousHeatRate fluid (Heat.frequency point)))
physicalViscousHeatAdmitsPositiveRationalFloor fluid point
  with BishopP.fast-density-of-ℚ
    BishopReal.0ℝ
    (Heat.viscousHeatRate fluid (Heat.frequency point))
    (Heat.viscousHeatRatePositive fluid point)
... | rational , lowerPositive , lowerBelowHeat =
  BishopReal._⋆ rational , lowerPositive , lowerBelowHeat

------------------------------------------------------------------------
-- High-frequency physical identification.
------------------------------------------------------------------------

record PhysicalHighFrequencyEnvelopeData
    {S : Canonical.CanonicalNSSemantics}
    {trajectory : Physical.EuclideanFourierTrajectory S}
    (kernel : Physical.EuclideanPhysicalResolventKernel trajectory)
    (fluid : Heat.PositiveViscosity) : Set₁ where
  field
    outputInteraction : Euclidean.EuclideanInteraction
    physicalOutputPoint : Heat.PuncturedEuclideanFrequency

    -- The high-frequency estimate is attached to an interaction which is
    -- literally realized by the same physical kernel.  This prevents a
    -- scale-floor certificate for an unrelated rational carrier from
    -- inhabiting the Clay-facing A1 seam.
    kernelCellUsesOutputInteraction :
      Physical.interaction (Physical.cell kernel outputInteraction)
      ≡ outputInteraction

    outputFrequencyIsPhysicalXi :
      Heat.frequency physicalOutputPoint ≡
      Euclidean.xi outputInteraction

    outputHeatRate : ℚ
    shellHeatFloor : ℚ

    scaleFloor : High.EuclideanOutputScaleFloor

    outputHeatRateMeaning :
      High.outputHeatRate scaleFloor ≡ outputHeatRate

    shellHeatFloorMeaning :
      High.shellHeatFloor scaleFloor ≡ shellHeatFloor

    -- Same-object bridge: the rational curvature parameter is not free.
    -- Its canonical Bishop embedding is exactly the physical viscous heat
    -- rate ν|xi|² at the output frequency of the same interaction.
    physicalOutputHeatRateMeaning :
      BishopReal._≃_
        (BishopQ.bishopRationalEmbed outputHeatRate)
        (Heat.viscousHeatRate fluid
          (Heat.frequency physicalOutputPoint))

open PhysicalHighFrequencyEnvelopeData public

highFrequencyCurvatureBound :
  ∀ {S trajectory kernel fluid} →
  (D : PhysicalHighFrequencyEnvelopeData
    {S} {trajectory} kernel fluid) →
  Envelope.resolventTransportCurvature
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

aHighFrequencyPhysicalHeatSameObjectRequired : Bool
aHighFrequencyPhysicalHeatSameObjectRequired = true

aHighFrequencyPhysicalHeatSameObjectRequiredIsTrue :
  aHighFrequencyPhysicalHeatSameObjectRequired ≡ true
aHighFrequencyPhysicalHeatSameObjectRequiredIsTrue = refl


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
