module DASHI.Governance.MedicalCannabisHistoricalMeaningBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Governance.HistoricalEventMeaningProvenanceBidiExact as Historical
import DASHI.Governance.MedicalCannabisContaminantSemanticEpistemicExact as Cannabis

------------------------------------------------------------------------
-- EXISTING MEANING/PROVENANCE BOUNDARY x CONTAMINANT INTERPRETATION
--
-- HistoricalEventMeaningProvenanceBidiExact already establishes the generic
-- nonfactorability pattern: a shared physical surface does not reconstruct
-- cause, actor meaning, official classification or later interpretation.
-- The medical-cannabis fixture is an application of the same structural rule
-- to product-safety / governance / political-economy interpretation.
------------------------------------------------------------------------

historicalMeaningBoundary : Historical.HistoricalEventMeaningBoundary
historicalMeaningBoundary = Historical.canonicalHistoricalEventMeaningBoundary

cannabisMeaningBoundary : Cannabis.MedicalCannabisSemanticEpistemicBoundary
cannabisMeaningBoundary = Cannabis.canonicalMedicalCannabisSemanticEpistemicBoundary

record MedicalCannabisHistoricalMeaningBridgeBoundary : Set where
  constructor medicalCannabisHistoricalMeaningBridgeBoundary
  field
    physicalSurfaceAndSystemMeaningRemainSeparated : Bool
    physicalSurfaceAndSystemMeaningRemainSeparatedIsTrue :
      physicalSurfaceAndSystemMeaningRemainSeparated ≡ true
    existingHistoricalMeaningOwnerIsReused : Bool
    existingHistoricalMeaningOwnerIsReusedIsTrue :
      existingHistoricalMeaningOwnerIsReused ≡ true
    contaminationObservationDoesNotCollapseGovernanceAndPoliticalEconomy : Bool
    contaminationObservationDoesNotCollapseGovernanceAndPoliticalEconomyIsTrue :
      contaminationObservationDoesNotCollapseGovernanceAndPoliticalEconomy ≡ true

canonicalMedicalCannabisHistoricalMeaningBridgeBoundary :
  MedicalCannabisHistoricalMeaningBridgeBoundary
canonicalMedicalCannabisHistoricalMeaningBridgeBoundary =
  medicalCannabisHistoricalMeaningBridgeBoundary
    true refl
    true refl
    true refl
