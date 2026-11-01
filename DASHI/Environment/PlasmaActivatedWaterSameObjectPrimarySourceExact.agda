module DASHI.Environment.PlasmaActivatedWaterSameObjectPrimarySourceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificWorkAttributionExact as Attribution

------------------------------------------------------------------------
-- SAME-OBJECT PAW PRIMARY SOURCE
--
-- Primary source owns only the reported reactor / chemistry / plant experiment.
-- DASHI owns any cross-domain same-object weld built from it.
------------------------------------------------------------------------

record PAWSameObjectPrimarySource : Set where
  constructor paw-same-object-primary-source
  field
    authors : String
    title : String
    venue : String
    year : Nat
    identifier : String
    reactorProductionReference : String
    chemistryMeasurementReference : String
    plantApplicationReference : String
    rootOrPlantResponseReference : String
    longHorizonOutcomeReference : String
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open PAWSameObjectPrimarySource public

kizerArabidopsisPAW2025 : PAWSameObjectPrimarySource
kizerArabidopsisPAW2025 = paw-same-object-primary-source
  "Jonathan Kizer; Conner Robinson; Ta'Kia Lucas; Steven Shannon; Ricardo Hernández; Katharina Stapelmann; Marcela Rojas-Pierce"
  "Non-thermal plasma activated water is an effective nitrogen fertilizer alternative for Arabidopsis thaliana"
  "PLOS ONE 20(9): e0327091"
  2025
  "DOI 10.1371/journal.pone.0327091; NCBI BioProject PRJNA1268561"
  "Atmospheric RF glow-discharge plasma; delivered power 250 W; air over circulating or stagnant deionized water; treatment conditions varied by target chemistry."
  "Each production step and final mixed PAW were measured for nitrate, nitrite, hydrogen peroxide and ammonium by colorimetric assays; final PAW was neutralized before plant use."
  "Arabidopsis seedlings and soil-grown plants received the same declared PAW chemistries or nitrate/H2O2-matched controls; soil-grown plants received weekly PAW or nitrate as the declared N source with other nutrients supplied separately."
  "Root morphology, ROS/hormone response and root/shoot transcriptomes were measured; N-response genes were among the observed differential-expression coordinates."
  "Soil-grown plants were treated for five weeks and harvested for rosette area plus shoot/root fresh or dry biomass and root:shoot allocation metrics."
  "One primary study spans PAW generation, chemistry measurement, application and plant response under declared Arabidopsis laboratory/controlled-growth conditions. It is a strong same-study carrier across these stages."
  "Does not directly measure isotopic fertilizer-N recovery, instantaneous root N flux, lifecycle emissions, field transport, aquaponic safety, universal fertilizer equivalence, or commercial recommendation."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

record PAWSameObjectSourceBoundary : Set where
  constructor paw-same-object-source-boundary
  field
    reactorChemistryApplicationAndOutcomeShareOnePublicationCarrier : Bool
    sourceOwnsOnlyReportedExperiment : Bool
    dashiOwnsCrossDomainWeld : Bool
    growthEqualityDoesNotMeanIsotopicNUptakeEquality : Bool
    laboratoryCarrierDoesNotMeanFieldTransport : Bool
    sourceAutomaticallyPaysRecommendation : Bool

canonicalPAWSameObjectSourceBoundary : PAWSameObjectSourceBoundary
canonicalPAWSameObjectSourceBoundary =
  paw-same-object-source-boundary true true true true true false
