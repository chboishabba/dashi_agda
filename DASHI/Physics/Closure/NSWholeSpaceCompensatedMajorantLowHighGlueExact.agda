module DASHI.Physics.Closure.NSWholeSpaceCompensatedMajorantLowHighGlueExact where

------------------------------------------------------------------------
-- WHOLE-SPACE A / LOW-HIGH INTEGRABILITY GLUE
--
-- The continuous lane has two qualitatively different regions:
--
--   low output frequency: singular resolvent curvature must be cancelled by
--                         the physical output factors before integration;
--   high output frequency: ordinary decay / dissipation majorants apply.
--
-- The remaining global integrability theorem must not reintroduce the naked
-- low-frequency singularity.  This owner states and proves the exact gluing
-- principle: if the physical majorant is pointwise the sum of already
-- integrable low and high pieces, the global majorant is integrable.
--
-- This is independent of periodic B and uses no lattice unit gap.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanLebesgueSignedAggregationExact as Lebesgue

record AdditiveIntegrabilityAuthority
    {dataSet : Euclidean.EuclideanSignedFluxData}
    (base : Lebesgue.EuclideanLebesgueIntegralAuthority dataSet) : Set₁ where
  field
    integrableAdd :
      {f g : Euclidean.EuclideanInteraction → BishopReal.ℝ} →
      Lebesgue.Integrable base f →
      Lebesgue.Integrable base g →
      Lebesgue.Integrable base
        (λ I → BishopReal._+_ (f I) (g I))

    integrableRespectsPointwise :
      {f g : Euclidean.EuclideanInteraction → BishopReal.ℝ} →
      ((I : Euclidean.EuclideanInteraction) → f I ≡ g I) →
      Lebesgue.Integrable base f →
      Lebesgue.Integrable base g

open AdditiveIntegrabilityAuthority public

record PhysicalLowHighMajorant
    {dataSet : Euclidean.EuclideanSignedFluxData}
    (base : Lebesgue.EuclideanLebesgueIntegralAuthority dataSet) : Set₁ where
  field
    globalMajorant :
      Euclidean.EuclideanInteraction → BishopReal.ℝ
    lowMajorant :
      Euclidean.EuclideanInteraction → BishopReal.ℝ
    highMajorant :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    lowIntegrable :
      Lebesgue.Integrable base lowMajorant
    highIntegrable :
      Lebesgue.Integrable base highMajorant

    globalSplitsLowHigh :
      (I : Euclidean.EuclideanInteraction) →
      globalMajorant I
      ≡ BishopReal._+_ (lowMajorant I) (highMajorant I)

open PhysicalLowHighMajorant public

globalPhysicalMajorantIntegrable :
  ∀ {dataSet base} →
  AdditiveIntegrabilityAuthority base →
  (M : PhysicalLowHighMajorant {dataSet} base) →
  Lebesgue.Integrable base (globalMajorant M)
globalPhysicalMajorantIntegrable authority M =
  integrableRespectsPointwise authority
    (globalSplitsLowHigh M)
    (integrableAdd authority
      (lowIntegrable M)
      (highIntegrable M))

------------------------------------------------------------------------
-- Frontier.
------------------------------------------------------------------------

lowHighIntegrabilityGlueClosed : Bool
lowHighIntegrabilityGlueClosed = true

lowFrequencyNakedResolventIntegrated : Bool
lowFrequencyNakedResolventIntegrated = false

physicalLowMajorantConstructedHere : Bool
physicalLowMajorantConstructedHere = false

physicalHighMajorantConstructedHere : Bool
physicalHighMajorantConstructedHere = false

globalPhysicalMajorantIntegrabilityReducedToTwoRegions : Bool
globalPhysicalMajorantIntegrabilityReducedToTwoRegions = true

clayPromotion : Bool
clayPromotion = false

lowHighIntegrabilityGlueClosedIsTrue :
  lowHighIntegrabilityGlueClosed ≡ true
lowHighIntegrabilityGlueClosedIsTrue = refl

globalPhysicalMajorantIntegrabilityReducedToTwoRegionsIsTrue :
  globalPhysicalMajorantIntegrabilityReducedToTwoRegions ≡ true
globalPhysicalMajorantIntegrabilityReducedToTwoRegionsIsTrue = refl
