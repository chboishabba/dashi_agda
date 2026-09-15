module DASHI.Wikimedia.IbrahimCannabisContaminantToxicantAssayParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisTerpeneCommercialSampleQuantitativeAssayExact as Assay
import DASHI.Wikimedia.IbrahimCannabisWishartSampleAliquotIdentityParetoExact as Sample
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- CANNABIS CONTAMINANT / TOXICANT ASSAY PARETO OWNER
--
-- "Poison" is not used as a synonym for every detected exogenous compound.
-- This owner separates contaminant identity, measured concentration, method
-- performance, regulatory threshold, route/exposure and toxicological effect.
--
-- detected != above LOQ != above regulatory threshold != hazardous exposure
-- != demonstrated toxicity.
------------------------------------------------------------------------

data ContaminantClass : Set where
  pesticideResidue
  toxicMetalOrTraceElement
  microbialOrMycotoxin
  processingOrCombustionProduct
  unknownExogenous : ContaminantClass

record AnalyticalUncertaintyReceipt : Set where
  constructor analytical-uncertainty-receipt
  field
    analyteClass : ContaminantClass
    platform : String
    calibrationRange : String
    precisionReference : String
    accuracyOrRecoveryReference : String
    lodReference : String
    loqReference : String
    technicalReplicateReference : String
    uncertaintyPaid : Bool
open AnalyticalUncertaintyReceipt public

wishartPesticideMethodUncertainty : AnalyticalUncertaintyReceipt
wishartPesticideMethodUncertainty = analytical-uncertainty-receipt
  pesticideResidue
  "targeted RPLC-API-MS/MS pesticide assay"
  "0.1 to 500 ng/mL calibration curves"
  "chromatographic assay CV <= 10%"
  "reported accuracy 80-120%"
  "source-specific detection limits retained in supporting information"
  "most screened pesticides were below the in-house LOQ; exact per-analyte LOQ retained in Table S7/supporting information"
  "same six commercial samples; technical assay replication belongs to the Wishart analytical programme"
  true

wishartCannabinoidMethodUncertainty : AnalyticalUncertaintyReceipt
wishartCannabinoidMethodUncertainty = analytical-uncertainty-receipt
  unknownExogenous
  "targeted LC-MS/MS cannabinoid assay; included here only as a method-performance comparator"
  "assay-specific calibration retained in Wishart supporting information"
  "reported intra- and inter-day precision about 20% CV"
  "reported spike recovery 80-120%"
  "assay-specific LOD retained externally"
  "assay-specific LOQ retained externally"
  "three technical replicates per named commercial sample"
  true

------------------------------------------------------------------------
-- Wishart primary contaminant observations.
------------------------------------------------------------------------

record ContaminantScreenReceipt : Set where
  constructor contaminant-screen-receipt
  field
    source : String
    sampleCarrier : String
    contaminantClass : ContaminantClass
    screenBreadth : String
    detectedReference : String
    quantifiedReference : String
    regulatoryComparatorReference : String
    methodUncertaintyReference : String
    sameObjectSamplePaid : Bool
    concentrationPaid : Bool
    regulatoryExceedancePaid : Bool
    toxicExposurePaid : Bool
open ContaminantScreenReceipt public

wishartPesticideScreen : ContaminantScreenReceipt
wishartPesticideScreen = contaminant-screen-receipt
  "Wishart et al. 2024, Chemical Composition of Commercial Cannabis, DOI 10.1021/acs.jafc.3c06616; experimental Table S7"
  "same six named commercial dry-flower samples used by the broader metabolomics programme"
  pesticideResidue
  "71 pesticides targeted"
  "14 of 71 were quantifiable across the panel; 3-6 pesticides quantified per cultivar"
  "ethoprophos, malathion, mevinphos and MGK-264 among low-abundance detections; methoprene was the most abundant pesticide in Alien Dawg"
  "paper states benzovindiflupyr, metalaxyl and methoprene in Alien Dawg exceeded the Health Canada LOQ comparator used by the authors; this is not automatically a toxicological exposure threshold"
  "CV <= 10%, accuracy 80-120%, 0.1-500 ng/mL calibration; per-analyte LOQ belongs to Table S7/supporting information"
  true true true false

wishartMetalScreen : ContaminantScreenReceipt
wishartMetalScreen = contaminant-screen-receipt
  "Wishart et al. 2024, DOI 10.1021/acs.jafc.3c06616; ICP-MS Table S9/Table 6"
  "same six commercial samples"
  toxicMetalOrTraceElement
  "ICP-MS platform capable of detecting 41 elements; 16 metal ions quantified in the reported cannabis panel"
  "no arsenic or lead detected; only minute thallium at ng/g scale was quantified; cesium quantified in one cultivar"
  "reported average thallium 5.4 +/- 3.5 ng/g; other quantified trace/essential elements retain their own units and source rows"
  "authors state measured metal concentrations were within reported ranges; route-specific inhalation toxicology remains a separate consumer"
  "ICP-MS method/validation belongs to Wishart supporting information"
  true true false false

------------------------------------------------------------------------
-- Toxicology / exposure admission.
------------------------------------------------------------------------

record ToxicExposureAdmission : Set where
  constructor toxic-exposure-admission
  field
    contaminantIdentityReference : String
    measuredConcentrationReference : String
    uncertaintyReference : String
    productMassReference : String
    preparationOrCombustionReference : String
    transferEfficiencyReference : String
    inhaledOrIngestedDoseReference : String
    bodyMassOrTargetPopulationReference : String
    regulatoryOrToxicologyThresholdReference : String
    concentrationPaid : Bool
    routeDosePaid : Bool
    toxicologicalConclusionPaid : Bool
open ToxicExposureAdmission public

currentToxicExposureResidual : ToxicExposureAdmission
currentToxicExposureResidual = toxic-exposure-admission
  "Wishart pesticide/metal identity surfaces are source-paid for their measured samples"
  "source-paid concentration or detection status where explicitly reported"
  "method precision/accuracy/LOQ must travel with each analyte claim"
  "unpaid product amount for a consumer exposure event"
  "unpaid smoking/vaporisation/extraction/ingestion transformation"
  "unpaid analyte-specific transfer into smoke/aerosol/dose"
  "unpaid absorbed dose"
  "unpaid body-mass/vulnerability coordinate"
  "unpaid toxicological threshold appropriate to analyte and route"
  true false false

------------------------------------------------------------------------
-- Social-source lane: @fadedfarmer is not silently reconstructed.
------------------------------------------------------------------------

record SocialSourceAdmission : Set where
  constructor social-source-admission
  field
    handle : String
    platform : String
    exactPostOrMediaReference : String
    captureTimestampReference : String
    authorIdentityReference : String
    claimReference : String
    originalMediaReference : String
    externalCorroborationReference : String
    exactPostPaid : Bool
    authorIdentityPaid : Bool
    claimPaid : Bool
    promotesToScientificEvidence : Bool
open SocialSourceAdmission public

fadedFarmerResidual : SocialSourceAdmission
fadedFarmerResidual = social-source-admission
  "@fadedfarmer"
  "Instagram / social account recalled by user; public search also finds a FadedFarmer grow-diary identity, but same-person identity is not promoted"
  "unresolved: no exact Instagram post/media object located in the current repo or current acquisition"
  "unresolved"
  "unresolved: handle alone is insufficient to bind a legal/person identity or cross-platform account"
  "unresolved: no specific contaminant/pesticide/toxicant claim is reconstructed from memory"
  "unresolved"
  "unresolved"
  false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DetectionCreatesPoisoning : Set where
data AboveLOQCreatesToxicExposure : Set where
data RegulatoryExceedanceCreatesClinicalHarm : Set where
data SocialPostCreatesScientificAuthority : Set where
data HandleCreatesSamePersonAcrossPlatforms : Set where

detectionDoesNotCreatePoisoning : DetectionCreatesPoisoning → ⊥
detectionDoesNotCreatePoisoning ()

aboveLOQDoesNotCreateToxicExposure : AboveLOQCreatesToxicExposure → ⊥
aboveLOQDoesNotCreateToxicExposure ()

regulatoryExceedanceDoesNotCreateClinicalHarm : RegulatoryExceedanceCreatesClinicalHarm → ⊥
regulatoryExceedanceDoesNotCreateClinicalHarm ()

socialPostDoesNotCreateScientificAuthority : SocialPostCreatesScientificAuthority → ⊥
socialPostDoesNotCreateScientificAuthority ()

handleDoesNotCreateSamePersonAcrossPlatforms : HandleCreatesSamePersonAcrossPlatforms → ⊥
handleDoesNotCreateSamePersonAcrossPlatforms ()

------------------------------------------------------------------------
-- Investigative Pareto order.
------------------------------------------------------------------------

data ContaminantParetoTarget : Set where
  acquireWishartTableS7
  acquireWishartTableS9Validation
  bindContaminantPubChemIdentity
  recoverFadedFarmerExactPost
  comparePublicClaimToPrimaryEvidence
  routeSpecificExposure
  clinicalToxicity : ContaminantParetoTarget

record ContaminantParetoStep : Set where
  constructor contaminant-pareto-step
  field
    priority : Nat
    target : ContaminantParetoTarget
    action : String
    pays : String
    dominatedUntil : String
open ContaminantParetoStep public

pareto0 : ContaminantParetoStep
pareto0 = contaminant-pareto-step
  0 acquireWishartTableS7
  "recover the exact pesticide rows, per-cultivar concentrations, per-analyte LOQs and validation details from Wishart supporting Table S7"
  "same-sample contaminant concentration plus measurement uncertainty"
  "none"

pareto1 : ContaminantParetoStep
pareto1 = contaminant-pareto-step
  1 acquireWishartTableS9Validation
  "recover exact per-cultivar ICP-MS metal rows and method validation rather than relying only on six-sample averages"
  "sample-indexed metal composition and uncertainty"
  "none"

pareto2 : ContaminantParetoStep
pareto2 = contaminant-pareto-step
  2 bindContaminantPubChemIdentity
  "join each measured pesticide/metal chemical identity to authoritative registry coordinates without confusing CDB identifiers with PubChem CIDs"
  "molecule/element identity closure"
  "exact analyte names required"

pareto3 : ContaminantParetoStep
pareto3 = contaminant-pareto-step
  3 recoverFadedFarmerExactPost
  "locate the exact @fadedfarmer Instagram post/media snapshot, timestamp, account state and concrete claim before ingesting it"
  "source-bounded social claim object"
  "do not reconstruct claims from remembered gist"

pareto4 : ContaminantParetoStep
pareto4 = contaminant-pareto-step
  4 comparePublicClaimToPrimaryEvidence
  "factor any recovered social claim through exact primary contaminant measurements, regulations and toxicology instead of treating popularity as evidence"
  "claim-specific corroboration or counterexample"
  "exact post and exact scientific/regulatory objects required"

pareto5 : ContaminantParetoStep
pareto5 = contaminant-pareto-step
  5 routeSpecificExposure
  "model analyte transfer through smoking, vaporisation, extraction or ingestion only after concentration and route are paid"
  "dose/exposure admission"
  "concentration alone is insufficient"

pareto9 : ContaminantParetoStep
pareto9 = contaminant-pareto-step
  9 clinicalToxicity
  "make no poisoning/clinical-harm conclusion without analyte-specific dose, route, threshold and population receipts"
  "toxicological conclusion"
  "dominated by concentration and exposure work"

------------------------------------------------------------------------
-- Time-indexed evidence.
------------------------------------------------------------------------

data ContaminantTime : Set where
  wishartPublication2024
  userRecalledSocialLane
  currentDashi : ContaminantTime

data ContaminantInterpretation : Set where
  contaminantsDetectedInCommercialSamples
  methodUncertaintyMustTravel
  fadedFarmerExactClaimAcquired
  measuredResidueEqualsPoisoning : ContaminantInterpretation

data ContaminantSummary : Set where contaminantEvidenceIsRouteIndexed : ContaminantSummary

ContaminantCompatible : ContaminantTime → ContaminantInterpretation → Set
ContaminantCompatible wishartPublication2024 contaminantsDetectedInCommercialSamples = ⊤
ContaminantCompatible wishartPublication2024 methodUncertaintyMustTravel = ⊤
ContaminantCompatible wishartPublication2024 fadedFarmerExactClaimAcquired = ⊥
ContaminantCompatible wishartPublication2024 measuredResidueEqualsPoisoning = ⊥
ContaminantCompatible userRecalledSocialLane contaminantsDetectedInCommercialSamples = ⊤
ContaminantCompatible userRecalledSocialLane methodUncertaintyMustTravel = ⊤
ContaminantCompatible userRecalledSocialLane fadedFarmerExactClaimAcquired = ⊥
ContaminantCompatible userRecalledSocialLane measuredResidueEqualsPoisoning = ⊥
ContaminantCompatible currentDashi contaminantsDetectedInCommercialSamples = ⊤
ContaminantCompatible currentDashi methodUncertaintyMustTravel = ⊤
ContaminantCompatible currentDashi fadedFarmerExactClaimAcquired = ⊥
ContaminantCompatible currentDashi measuredResidueEqualsPoisoning = ⊥

contaminantTemporalSystem : Temporal.TemporalEvidenceSystem
contaminantTemporalSystem = record
  { Time = ContaminantTime
  ; Interpretation = ContaminantInterpretation
  ; Compatible = ContaminantCompatible
  ; Summary = ContaminantSummary
  ; summarize = λ _ → contaminantEvidenceIsRouteIndexed
  ; timeReference = λ
      { wishartPublication2024 → "Wishart et al. 2024 DOI 10.1021/acs.jafc.3c06616"
      ; userRecalledSocialLane → "user recalls prior @fadedfarmer Instagram ingestion; no durable exact post object located yet"
      ; currentDashi → "current DASHI contaminant/toxicant Pareto frontier"
      }
  }

currentContaminantFibre : Temporal.EvidenceFibre contaminantTemporalSystem currentDashi
currentContaminantFibre = Temporal.liveInterpretationAt methodUncertaintyMustTravel tt

record CannabisContaminantBoundary : Set where
  constructor cannabis-contaminant-boundary
  field
    detectionIsNotPoisoning : Bool
    loqIsNotToxicityThreshold : Bool
    measurementUncertaintyRetained : Bool
    sampleIdentityRetained : Bool
    socialClaimRequiresExactPost : Bool
    routeSpecificExposureRequired : Bool
open CannabisContaminantBoundary public

canonicalCannabisContaminantBoundary : CannabisContaminantBoundary
canonicalCannabisContaminantBoundary =
  cannabis-contaminant-boundary true true true true true true
