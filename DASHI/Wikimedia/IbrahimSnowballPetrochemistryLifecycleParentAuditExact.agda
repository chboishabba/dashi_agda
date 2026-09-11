module DASHI.Wikimedia.IbrahimSnowballPetrochemistryLifecycleParentAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Chemistry.SaltPetroleumIndustrialChemistryNetworkExact as Industry
import DASHI.Biology.DeepTimeCarbonBiosphereFossilFuelBidiExact as DeepTime

------------------------------------------------------------------------
-- PETROCHEMISTRY PARENT AUDIT
--
-- Quotient result: existing owners already supply the two necessary carriers:
--   (1) geological/biological carbon history -> fossil reservoir -> extraction
--       -> combustion -> atmosphere/ocean;
--   (2) process-specific industrial material transformations from hydrocarbon
--       feed through steam cracking/refining and downstream products.
--
-- The surviving seam is stage identity, not a missing petrochemistry ontology.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim petrochemistry lifecycle parent audit"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create feedstock genealogy, process equivalence, emissions attribution or lifecycle causation")

petrochemistryQid : Identity.ExternalIdentityDemand
petrochemistryQid = mkQid "petrochemistry" "Q493630"

petroleumQid : Identity.ExternalIdentityDemand
petroleumQid = mkQid "petroleum" "Q22656"

steamCrackingQid : Identity.ExternalIdentityDemand
steamCrackingQid = mkQid "steam cracking" "Q2335334"

crackingQid : Identity.ExternalIdentityDemand
crackingQid = mkQid "cracking (chemistry)" "Q212749"

petrochemistryDewey : Dewey.DeweyCoordinate
petrochemistryDewey = Dewey.mkUnresolvedDewey
  "petrochemistry"
  "no exact inspected DDC value promoted; chemistry/chemical-engineering shelf placement remains navigation only"

steamCrackingReviewSource : Attribution.AttributedSource
steamCrackingReviewSource = Attribution.mkDOISource
  "Zahra Gholami; Fatemeh Gholami; Zdeněk Tišler; Mohammadtaghi Vakili"
  "A Review on the Production of Light Olefins Using Steam Cracking of Hydrocarbons"
  "Energies 14(23), 8190"
  "2021"
  "10.3390/en14238190"
  "https://doi.org/10.3390/en14238190"
  Attribution.academicArticleSource
  "review of hydrocarbon steam cracking to light olefins and operating parameters; supports process-stage calibration, not a unique lifecycle/emissions attribution"
  Attribution.publicAttribution

thermalCrackingReviewSource : Attribution.AttributedSource
thermalCrackingReviewSource = Attribution.mkDOISource
  "S. M. Sadrameli"
  "Thermal/catalytic cracking of hydrocarbons for the production of olefins: A state-of-the-art review I: Thermal cracking review"
  "Fuel 140, 102-115"
  "2015"
  "10.1016/j.fuel.2014.09.034"
  "https://doi.org/10.1016/j.fuel.2014.09.034"
  Attribution.academicArticleSource
  "review of hydrocarbon thermal/steam cracking for olefin production; process evidence only"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Same broad petroleum label cannot recover lifecycle stage.
------------------------------------------------------------------------

data PetroleumStageCase : Set where
  petroleumInGeologicalReservoir
  petroleumAsExtractedFeedstock
  petroleumAsPetrochemicalInput
  petroleumCarbonAfterCombustion : PetroleumStageCase

data PetroleumSurface : Set where samePetroleumLabel : PetroleumSurface
data LifecycleStage : Set where
  geologicalReservoirStage extractedFeedStage industrialInputStage surfaceCarbonReturnStage : LifecycleStage

petroleumSurface : PetroleumStageCase → PetroleumSurface
petroleumSurface _ = samePetroleumLabel

lifecycleStage : PetroleumStageCase → LifecycleStage
lifecycleStage petroleumInGeologicalReservoir = geologicalReservoirStage
lifecycleStage petroleumAsExtractedFeedstock = extractedFeedStage
lifecycleStage petroleumAsPetrochemicalInput = industrialInputStage
lifecycleStage petroleumCarbonAfterCombustion = surfaceCarbonReturnStage

petroleumStageDefect : INF.NonFactorabilityWitness petroleumSurface lifecycleStage
petroleumStageDefect = INF.nonFactorabilityWitness
  petroleumInGeologicalReservoir petroleumAsExtractedFeedstock refl (λ ())

petroleumLabelCannotFactorLifecycleStage :
  INF.FactorsThrough petroleumSurface lifecycleStage → ⊥
petroleumLabelCannotFactorLifecycleStage =
  INF.witnessRulesOutEveryFlatFactorisation petroleumStageDefect

------------------------------------------------------------------------
-- Thin lifecycle correspondence: references existing owners, no new chemistry.
------------------------------------------------------------------------

record PetrochemicalLifecycleReceipt : Set where
  constructor petrochemical-lifecycle-receipt
  field
    deepTimeFormationCarrier : String
    extractionToIndustrialFeedCarrier : String
    industrialTransformationCarrier : String
    downstreamMaterialCarrier : String
    oxidationCombustionCarrier : String
    atmosphereOceanReturnCarrier : String
    sourceProvenanceRetained : Bool
    processSpecificityRetained : Bool
    emissionsNeedSeparateQuantitativeReceipt : Bool
open PetrochemicalLifecycleReceipt public

canonicalPetrochemicalLifecycleReceipt : PetrochemicalLifecycleReceipt
canonicalPetrochemicalLifecycleReceipt = petrochemical-lifecycle-receipt
  "DeepTimeCarbonBiosphereFossilFuelBidiExact: organic matter -> burial/maturation -> fossil carbon reservoir"
  "extraction changes lifecycle stage; a concrete refinery/petrochemical application supplies feed identity"
  "SaltPetroleumIndustrialChemistryNetworkExact.IndustrialTransformationEdge"
  "product-specific material lineage remains separate; same product need not recover unique upstream history"
  "DeepTimeCarbonBiosphereFossilFuelBidiExact.industrialCombustion"
  "DeepTimeCarbonBiosphereFossilFuelBidiExact.atmosphericOceanReturn"
  true true true

industryBoundary : Industry.SaltPetroleumIndustrialChemistryBoundary
industryBoundary = Industry.canonicalSaltPetroleumIndustrialChemistryBoundary

deepTimeBoundary : DeepTime.DeepTimeCarbonBiosphereFossilFuelBoundary
deepTimeBoundary = DeepTime.canonicalDeepTimeCarbonBiosphereFossilFuelBoundary

------------------------------------------------------------------------
-- Parent audit conclusion.
------------------------------------------------------------------------

data GenericPetrochemistryParentNeeded : Set where
data PetroleumLabelCreatesLifecycle : Set where
data SteamCrackingEqualsAllPetrochemistry : Set where
data ProcessReceiptCreatesEmissionQuantity : Set where

petroleumLabelDoesNotCreateLifecycle : PetroleumLabelCreatesLifecycle → ⊥
petroleumLabelDoesNotCreateLifecycle ()

steamCrackingDoesNotEqualAllPetrochemistry : SteamCrackingEqualsAllPetrochemistry → ⊥
steamCrackingDoesNotEqualAllPetrochemistry ()

processReceiptDoesNotCreateEmissionQuantity : ProcessReceiptCreatesEmissionQuantity → ⊥
processReceiptDoesNotCreateEmissionQuantity ()

record PetrochemistryParentAuditBoundary : Set where
  constructor petrochemistry-parent-audit-boundary
  field
    qidsAttached : Bool
    deweyNavigationOnly : Bool
    doiSourceRolesRetained : Bool
    deepTimeCarrierAlreadyExists : Bool
    industrialTransformationCarrierAlreadyExists : Bool
    lifecycleStageSeparationAdded : Bool
    newParallelPetrochemistryOntologyNeeded : Bool
    remainingWorkConsumerSpecific : Bool
open PetrochemistryParentAuditBoundary public

canonicalPetrochemistryParentAuditBoundary : PetrochemistryParentAuditBoundary
canonicalPetrochemistryParentAuditBoundary = petrochemistry-parent-audit-boundary
  true true true true true true false true
