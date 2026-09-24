module DASHI.Biology.Agriculture.AcaciaSenegalBNFLESCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Environment.LESResearchCrossPollinationExact as LES
import DASHI.Environment.AcaciaSenegalDrylandWaterCarbonExact as Dryland
import DASHI.Environment.AcaciaSenegalDrylandTaskFactorisationExact as DrylandTask
import DASHI.Biology.Agriculture.AcaciaSenegalRhizobialBNFSourceAtlasExact as AcaciaSources
import DASHI.Biology.Agriculture.BNFQualifiedInterventionModelExact as BNF
import DASHI.Biology.Agriculture.LegumeNodulationSituatedProteinBridgeExact as Nodulation
import DASHI.Biology.Protein.NitrogenaseSituatedProteinWitnessExact as Nitrogenase

------------------------------------------------------------------------
-- ACACIA BNF <-> DRYLAND LES CROSS-POLLINATION
--
-- The 2018 Sudan water/carbon study did not measure BNF.  We therefore retain
-- it as an independent source surface and join it only at the DASHI observer
-- layer with separately attributed Acacia/Senegalia BNF sources.
------------------------------------------------------------------------

abakerDrylandDOI : String
abakerDrylandDOI = Dryland.primaryStudyDOI

acaciaBNFAttributionAtlas : Attribution.AttributedSourceAtlas
acaciaBNFAttributionAtlas = AcaciaSources.acaciaAttributedAtlas

------------------------------------------------------------------------
-- Provenance-retaining joined coordinate family.
------------------------------------------------------------------------

data AcaciaBNFLESCoordinate : Set where
  soilOrganicCarbon : AcaciaBNFLESCoordinate
  hydraulicCapacity : AcaciaBNFLESCoordinate
  realisedSoilMoisture : AcaciaBNFLESCoordinate
  runoff : AcaciaBNFLESCoordinate
  infiltration : AcaciaBNFLESCoordinate
  evapotranspiration : AcaciaBNFLESCoordinate
  drainage : AcaciaBNFLESCoordinate
  rainfallSiteAge : AcaciaBNFLESCoordinate
  rhizobialPartner : AcaciaBNFLESCoordinate
  nodulationState : AcaciaBNFLESCoordinate
  nitrogenaseSituatedState : AcaciaBNFLESCoordinate
  fixedNEvidence : AcaciaBNFLESCoordinate
  soilMineralNEvidence : AcaciaBNFLESCoordinate
  sourceEvidenceRole : AcaciaBNFLESCoordinate

record AcaciaBNFLESJoinedObserver : Set where
  constructor acacia-bnf-les-joined-observer
  field
    drylandWaterCarbonOwner : String
    acaciaBNFSourceOwner : String
    nitrogenaseProteinOwner : String
    nodulationOwner : String
    bnfConsumerOwner : String
    retainedCoordinates : List AcaciaBNFLESCoordinate
    waterCarbonSourceDOI : String
    bnfSourceAtlas : Attribution.AttributedSourceAtlas
    sourceFusionCreatesSameStudy : Bool
    sourceFusionCreatesSameStudyIsFalse : sourceFusionCreatesSameStudy ≡ false
open AcaciaBNFLESJoinedObserver public

canonicalJoinedObserver : AcaciaBNFLESJoinedObserver
canonicalJoinedObserver = acacia-bnf-les-joined-observer
  "DASHI.Environment.AcaciaSenegalDrylandWaterCarbonExact"
  "DASHI.Biology.Agriculture.AcaciaSenegalRhizobialBNFSourceAtlasExact"
  "DASHI.Biology.Protein.NitrogenaseSituatedProteinWitnessExact"
  "DASHI.Biology.Agriculture.LegumeNodulationSituatedProteinBridgeExact"
  "DASHI.Biology.Agriculture.BNFQualifiedInterventionModelExact"
  (soilOrganicCarbon ∷ hydraulicCapacity ∷ realisedSoilMoisture ∷ runoff ∷ infiltration ∷ evapotranspiration ∷ drainage ∷ rainfallSiteAge ∷ rhizobialPartner ∷ nodulationState ∷ nitrogenaseSituatedState ∷ fixedNEvidence ∷ soilMineralNEvidence ∷ sourceEvidenceRole ∷ [])
  Dryland.primaryStudyDOI
  AcaciaSources.acaciaAttributedAtlas
  false refl

------------------------------------------------------------------------
-- Typed joined observation.
--
-- This is deliberately polymorphic in its BNF state: #980 supplies a concrete
-- DrylandWaterCarbonState, while no single Acacia BNF paper supplies a complete
-- ecosystem BNF state.  The bridge can therefore retain a separately sourced
-- BNF state without fabricating a same-study empirical object.
------------------------------------------------------------------------

record AcaciaBNFLESObservation (BNFState : Set) : Set where
  constructor acacia-bnf-les-observation
  field
    waterCarbonState : Dryland.DrylandWaterCarbonState
    bnfState : BNFState
    rhizobialPartnerReading : String
    nodulationReading : String
    nitrogenaseSituatedReading : String
    fixedNEvidenceReading : String
    soilNReading : String
    waterCarbonSourceReading : String
    bnfSourceReading : String
    evidenceRoleReading : String
    sameStudyEmpiricalObject : Bool
    sameStudyEmpiricalObjectIsFalse : sameStudyEmpiricalObject ≡ false
open AcaciaBNFLESObservation public

observationTypeRetainsConcreteDrylandState : Set → Set
observationTypeRetainsConcreteDrylandState = AcaciaBNFLESObservation

------------------------------------------------------------------------
-- Reuse of canonical BNF / LES owners.
------------------------------------------------------------------------

drylandWeldReused : Dryland.AcaciaLESWeld
drylandWeldReused = Dryland.canonicalAcaciaLESWeld

drylandTaskBoundaryReused : DrylandTask.TaskFactorisationBridgeBoundary
drylandTaskBoundaryReused = DrylandTask.canonicalTaskFactorisationBridgeBoundary

nitrogenaseBoundaryReused : Nitrogenase.NitrogenaseSituatedBoundary
nitrogenaseBoundaryReused = Nitrogenase.canonicalNitrogenaseBoundary

nodulationBoundaryReused : Nodulation.NodulationBoundary
nodulationBoundaryReused = Nodulation.canonicalNodulationBoundary

bnfEcologicalConsumerRequiresHydrology :
  BNF.requiredFor BNF.predictEcologicalResponse BNF.hydrologyAdequacy ≡ true
bnfEcologicalConsumerRequiresHydrology = refl

------------------------------------------------------------------------
-- Finite DASHI collision family.
--
-- These worlds are synthetic information-loss witnesses calibrated by the
-- source-bounded distinctions above. They are NOT additional Acacia field
-- observations and carry no empirical frequency, causal effect size or policy
-- recommendation.
------------------------------------------------------------------------

data AcaciaBNFWorld : Set where
  sameTreeNoduleInactive : AcaciaBNFWorld
  sameTreeNoduleActive : AcaciaBNFWorld
  activeFixationLowRetainedSoilN : AcaciaBNFWorld
  activeFixationHighRetainedSoilN : AcaciaBNFWorld
  fixedNHydrologySuitable : AcaciaBNFWorld
  fixedNHydrologyUnsuitable : AcaciaBNFWorld

data SoilNTask : Set where
  soilNOutcomeTask : SoilNTask

data FixedNTask : Set where
  fixedNFluxTask : FixedNTask

data RestorationTask : Set where
  restorationDecisionTask : RestorationTask

treeIdentityOnly : AcaciaBNFWorld → Bool
treeIdentityOnly _ = true

nodulePresenceOnly : AcaciaBNFWorld → Bool
nodulePresenceOnly sameTreeNoduleInactive = true
nodulePresenceOnly sameTreeNoduleActive = true
nodulePresenceOnly activeFixationLowRetainedSoilN = true
nodulePresenceOnly activeFixationHighRetainedSoilN = true
nodulePresenceOnly fixedNHydrologySuitable = true
nodulePresenceOnly fixedNHydrologyUnsuitable = true

rhizobialIdentityOnly : AcaciaBNFWorld → Bool
rhizobialIdentityOnly _ = true

fixedNMetricOnly : AcaciaBNFWorld → Bool
fixedNMetricOnly sameTreeNoduleInactive = false
fixedNMetricOnly sameTreeNoduleActive = true
fixedNMetricOnly activeFixationLowRetainedSoilN = true
fixedNMetricOnly activeFixationHighRetainedSoilN = true
fixedNMetricOnly fixedNHydrologySuitable = true
fixedNMetricOnly fixedNHydrologyUnsuitable = true

soilNOutcome : SoilNTask → AcaciaBNFWorld → Bool
soilNOutcome soilNOutcomeTask sameTreeNoduleInactive = false
soilNOutcome soilNOutcomeTask sameTreeNoduleActive = true
soilNOutcome soilNOutcomeTask activeFixationLowRetainedSoilN = false
soilNOutcome soilNOutcomeTask activeFixationHighRetainedSoilN = true
soilNOutcome soilNOutcomeTask fixedNHydrologySuitable = true
soilNOutcome soilNOutcomeTask fixedNHydrologyUnsuitable = true

fixedNOutcome : FixedNTask → AcaciaBNFWorld → Bool
fixedNOutcome fixedNFluxTask sameTreeNoduleInactive = false
fixedNOutcome fixedNFluxTask sameTreeNoduleActive = true
fixedNOutcome fixedNFluxTask activeFixationLowRetainedSoilN = true
fixedNOutcome fixedNFluxTask activeFixationHighRetainedSoilN = true
fixedNOutcome fixedNFluxTask fixedNHydrologySuitable = true
fixedNOutcome fixedNFluxTask fixedNHydrologyUnsuitable = true

restorationDecision : RestorationTask → AcaciaBNFWorld → Bool
restorationDecision restorationDecisionTask sameTreeNoduleInactive = false
restorationDecision restorationDecisionTask sameTreeNoduleActive = false
restorationDecision restorationDecisionTask activeFixationLowRetainedSoilN = false
restorationDecision restorationDecisionTask activeFixationHighRetainedSoilN = false
restorationDecision restorationDecisionTask fixedNHydrologySuitable = true
restorationDecision restorationDecisionTask fixedNHydrologyUnsuitable = false

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

treeIdentityNotTaskSufficientForSoilN :
  LES.TaskFactorisation treeIdentityOnly soilNOutcome → ⊥
treeIdentityNotTaskSufficientForSoilN factor =
  falseNotTrue
    (LES.sameRepresentationSameTaskOutput
      factor soilNOutcomeTask
      {sameTreeNoduleInactive} {sameTreeNoduleActive} refl)

nodulePresenceNotTaskSufficientForSoilN :
  LES.TaskFactorisation nodulePresenceOnly soilNOutcome → ⊥
nodulePresenceNotTaskSufficientForSoilN factor =
  falseNotTrue
    (LES.sameRepresentationSameTaskOutput
      factor soilNOutcomeTask
      {activeFixationLowRetainedSoilN} {activeFixationHighRetainedSoilN} refl)

rhizobialIdentityNotTaskSufficientForFixedN :
  LES.TaskFactorisation rhizobialIdentityOnly fixedNOutcome → ⊥
rhizobialIdentityNotTaskSufficientForFixedN factor =
  falseNotTrue
    (LES.sameRepresentationSameTaskOutput
      factor fixedNFluxTask
      {sameTreeNoduleInactive} {sameTreeNoduleActive} refl)

fixedNMetricNotTaskSufficientForRestoration :
  LES.TaskFactorisation fixedNMetricOnly restorationDecision → ⊥
fixedNMetricNotTaskSufficientForRestoration factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor restorationDecisionTask
      {fixedNHydrologySuitable} {fixedNHydrologyUnsuitable} refl)

------------------------------------------------------------------------
-- Consumer / authority boundary.
------------------------------------------------------------------------

record AcaciaBNFLESBoundary : Set where
  constructor acacia-bnf-les-boundary
  field
    reusesAcaciaWaterCarbonOwner : Bool
    reusesBNFQualifiedInterventionOwner : Bool
    reusesSituatedNitrogenaseOwner : Bool
    reusesNodulationBridge : Bool
    typedJoinedObservationRetained : Bool
    treeIdentityAloneAdequateForSoilN : Bool
    nodulePresenceAloneAdequateForSoilN : Bool
    rhizobialIdentityAloneAdequateForFixedN : Bool
    fixedNMetricAloneAdequateForRestoration : Bool
    abakerStudyMeasuredBNF : Bool
    sourceJoinCreatesSingleStudy : Bool
    fixedNFluxImpliesPlantAssimilation : Bool
    plantAssimilationImpliesEcosystemSoilNOutcome : Bool
    soilNOutcomeImpliesDeploymentAuthority : Bool
    hydrologyRemainsIndependentConsumerCoordinate : Bool
    sourceProvenanceRetained : Bool
    syntheticCollisionIsFieldObservation : Bool
open AcaciaBNFLESBoundary public

canonicalAcaciaBNFLESBoundary : AcaciaBNFLESBoundary
canonicalAcaciaBNFLESBoundary = acacia-bnf-les-boundary
  true true true true true
  false false false false false false false false false
  true true false

reusesMergedWaterCarbonOwner :
  reusesAcaciaWaterCarbonOwner canonicalAcaciaBNFLESBoundary ≡ true
reusesMergedWaterCarbonOwner = refl

reusesExistingBNFQualifiedModel :
  reusesBNFQualifiedInterventionOwner canonicalAcaciaBNFLESBoundary ≡ true
reusesExistingBNFQualifiedModel = refl

reusesSituatedNitrogenase :
  reusesSituatedNitrogenaseOwner canonicalAcaciaBNFLESBoundary ≡ true
reusesSituatedNitrogenase = refl

reusesNodulation :
  reusesNodulationBridge canonicalAcaciaBNFLESBoundary ≡ true
reusesNodulation = refl

typedJoinedObservationIsRetained :
  typedJoinedObservationRetained canonicalAcaciaBNFLESBoundary ≡ true
typedJoinedObservationIsRetained = refl

attributionRule : String
attributionRule =
  "Abaker/Berninger/Starr DOI 10.1016/j.jaridenv.2017.12.004 remains the source owner for the merged dryland water-carbon observations only. Acacia/Senegalia BNF papers retain their own DOI/PMID-attributed propositions through AcaciaSenegalRhizobialBNFSourceAtlasExact and LegumeNodulationSituatedProteinBridgeExact. DASHI owns only the joined observer, typed cross-owner observation carrier, TaskFactorisation collisions and no-promotion boundaries; joining sources does not manufacture a same-study empirical record or deployment authority."
