module DASHI.Biology.Agriculture.AcaciaSenegalSymbiosisEnvironmentalEnablementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Environment.LESResearchCrossPollinationExact as LES
import DASHI.Environment.AcaciaSenegalDrylandWaterCarbonExact as Dryland
import DASHI.Biology.Agriculture.LegumeNodulationSituatedProteinBridgeExact as Nodulation
import DASHI.Biology.Agriculture.AcaciaSenegalBNFEdaphicLESExact as Edaphic
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Chemistry

------------------------------------------------------------------------
-- ACACIA / RHIZOBIUM ENVIRONMENTAL ENABLEMENT FIBRE
--
-- This owner refines requirements around the existing nitrogenase
-- `reactionEnablement` debt. It does NOT mark that global stage closed.
------------------------------------------------------------------------

rasanen2004DOI : String
rasanen2004DOI = "10.1023/B:PLSO.0000030181.03575.e1"

fall2011DOI : String
fall2011DOI = "10.1007/s13199-011-0128-0"

rasanenSaijetsJokinenLindstrom2004 : Attribution.AttributedSource
rasanenSaijetsJokinenLindstrom2004 = Attribution.mkDOISource
  "Leena A. Rasanen; Salla Saijets; Kari Jokinen; Kristina Lindstrom"
  "Evaluation of the roles of two compatible solutes, glycine betaine and trehalose, for the Acacia senegal-Sinorhizobium symbiosis exposed to drought stress"
  "Plant and Soil 260(1-2):237-251"
  "2004"
  rasanen2004DOI
  "https://doi.org/10.1023/B:PLSO.0000030181.03575.e1"
  Attribution.academicArticleSource
  "Primary controlled drought-stress study of Acacia senegal seedlings inoculated with Sinorhizobium arboris; supports environment-sensitive infection/nodulation development, not a universal field hydrology or whole-plant nitrogen-balance theorem."
  Attribution.publicAttribution

fallEtAl2011 : Attribution.AttributedSource
fallEtAl2011 = Attribution.mkDOISource
  "Dioumacor Fall; Mohamed Ourarhi; Mustapha Missbah El Idrissi; Niokhor Bakhoum; Alzouma Mayaki Zoubeirou; Hanaa Abdelmoumen; Diegane Diouf"
  "The efficiency and competitiveness of three Mesorhizobium sp. strains nodulating Acacia senegal (L.) Willd. under water deficiency conditions in the greenhouse"
  "Symbiosis 54(2):87-94"
  "2011"
  fall2011DOI
  "https://doi.org/10.1007/s13199-011-0128-0"
  Attribution.academicArticleSource
  "Primary greenhouse source comparing selected Acacia-senegal-nodulating Mesorhizobium strains under water-deficiency context. It supports strain-by-environment retention, not field deployment authority or a universal drought-tolerance ranking."
  Attribution.publicAttribution

heatStressSource : Nodulation.NodulationSource
heatStressSource = Nodulation.rasanen1999

edaphicContextSource : Attribution.AttributedSource
edaphicContextSource = Edaphic.isaacEtAl2011

drylandWaterCarbonDOI : String
drylandWaterCarbonDOI = Dryland.primaryStudyDOI

------------------------------------------------------------------------
-- Source-bounded environmental readings.
------------------------------------------------------------------------

record EnvironmentalEnablementReading : Set where
  constructor environmental-enablement-reading
  field
    heatCanBlockInfectionOrNodulationWithRhizobiaPresent : Bool
    postStressRecoveryCanOccur : Bool
    droughtChangesSymbiosisDevelopment : Bool
    waterDeficiencyRetainsStrainEfficiencyContext : Bool
    soilPAndTreeAgeRemainFixationContext : Bool
    bulkSoilWaterIsNotNoduleMicroenvironmentMeasurement : Bool
open EnvironmentalEnablementReading public

canonicalEnvironmentalReading : EnvironmentalEnablementReading
canonicalEnvironmentalReading = environmental-enablement-reading
  true true true true true true

------------------------------------------------------------------------
-- Finite DASHI information-loss witnesses.
--
-- These worlds are synthetic. The cited sources own only the environmental
-- sensitivity premises; DASHI owns the factorisation counterexamples.
------------------------------------------------------------------------

data EnablementWorld : Set where
  permissiveEnvironment : EnablementWorld
  heatBlockedEnvironment : EnablementWorld
  droughtBlockedEnvironment : EnablementWorld

data SymbiosisTask : Set where
  successfulSymbiosisTask : SymbiosisTask

data HostIdentity : Set where
  acaciaSenegalHost : HostIdentity

data RhizobialIdentity : Set where
  acaciaCompatibleRhizobium : RhizobialIdentity

hostIdentity : EnablementWorld → HostIdentity
hostIdentity _ = acaciaSenegalHost

rhizobialIdentity : EnablementWorld → RhizobialIdentity
rhizobialIdentity _ = acaciaCompatibleRhizobium

successfulSymbiosis : SymbiosisTask → EnablementWorld → Bool
successfulSymbiosis successfulSymbiosisTask permissiveEnvironment = true
successfulSymbiosis successfulSymbiosisTask heatBlockedEnvironment = false
successfulSymbiosis successfulSymbiosisTask droughtBlockedEnvironment = false

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

rhizobialIdentityNotTaskSufficient :
  LES.TaskFactorisation rhizobialIdentity successfulSymbiosis → ⊥
rhizobialIdentityNotTaskSufficient factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor successfulSymbiosisTask
      {permissiveEnvironment} {heatBlockedEnvironment} refl)

hostIdentityNotTaskSufficient :
  LES.TaskFactorisation hostIdentity successfulSymbiosis → ⊥
hostIdentityNotTaskSufficient factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor successfulSymbiosisTask
      {permissiveEnvironment} {droughtBlockedEnvironment} refl)

-- Same selected strain token, different water context. This is a synthetic
-- information-loss witness calibrated by the drought/water-deficiency sources,
-- not a claim that either paper published this Boolean model.
data StrainWaterWorld : Set where
  selectedStrainPermissive : StrainWaterWorld
  selectedStrainWaterDeficient : StrainWaterWorld

data StrainTask : Set where
  strainRealisedEfficiencyTask : StrainTask

data SelectedStrain : Set where
  selectedAcaciaRhizobialStrain : SelectedStrain

strainIdentityOnly : StrainWaterWorld → SelectedStrain
strainIdentityOnly _ = selectedAcaciaRhizobialStrain

strainRealisedEfficiency : StrainTask → StrainWaterWorld → Bool
strainRealisedEfficiency strainRealisedEfficiencyTask selectedStrainPermissive = true
strainRealisedEfficiency strainRealisedEfficiencyTask selectedStrainWaterDeficient = false

strainIdentityNotTaskSufficientUnderWaterContext :
  LES.TaskFactorisation strainIdentityOnly strainRealisedEfficiency → ⊥
strainIdentityNotTaskSufficientUnderWaterContext factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor strainRealisedEfficiencyTask
      {selectedStrainPermissive} {selectedStrainWaterDeficient} refl)

------------------------------------------------------------------------
-- Repair surface.
------------------------------------------------------------------------

record EnvironmentalEnablementRepair : Set where
  constructor environmental-enablement-repair
  field
    hostIdentityRetained : Bool
    rhizobialIdentityRetained : Bool
    strainIdentityRetained : Bool
    rootTemperatureRetained : Bool
    droughtWaterStatusRetained : Bool
    soilPhosphorusRetained : Bool
    nitrogenAvailabilityRegimeRetained : Bool
    treeAgeRetained : Bool
    infectionStageRetained : Bool
    nodulationStageRetained : Bool
    bulkSoilWaterRetainedSeparately : Bool
    noduleRootMicroenvironmentRetainedSeparately : Bool
    greenhouseVsFieldRoleRetained : Bool
    observerMethodRetained : Bool
    sourceIdentityRetained : Bool
open EnvironmentalEnablementRepair public

canonicalEnvironmentalEnablementRepair : EnvironmentalEnablementRepair
canonicalEnvironmentalEnablementRepair = environmental-enablement-repair
  true true true true true true true true true true true true true true true

------------------------------------------------------------------------
-- Existing nitrogenase ladder remains authoritative.
------------------------------------------------------------------------

reactionEnablementRemainsOpen :
  Chemistry.stageClosed Chemistry.reactionEnablement ≡ false
reactionEnablementRemainsOpen = Chemistry.reactionEnablementStillOpen

record EnvironmentalEnablementBoundary : Set where
  constructor environmental-enablement-boundary
  field
    rhizobialIdentityAloneAdequate : Bool
    hostIdentityAloneAdequate : Bool
    rhizobialStrainIdentityAloneAdequateUnderWaterDeficiency : Bool
    rhizobialPresenceCreatesNodulation : Bool
    soilPAloneDeterminesEnablement : Bool
    bulkSoilMoistureEqualsNoduleMicroenvironment : Bool
    heatRecoveryCreatesUniversalTolerance : Bool
    droughtStudyCreatesFieldWaterBalance : Bool
    greenhouseWaterDeficiencyCreatesFieldDeploymentAuthority : Bool
    environmentalContextConstrainsEnablement : Bool
    reactionEnablementGloballyClosedByThisOwner : Bool
    reactionEnablementPaysPlantAssimilation : Bool
    existingNodulationOwnerReused : Bool
    existingEdaphicOwnerReused : Bool
    drylandMoistureOwnerReusedWithoutSourceFusion : Bool
    syntheticWorldsAreFieldObservations : Bool
open EnvironmentalEnablementBoundary public

canonicalEnvironmentalEnablementBoundary : EnvironmentalEnablementBoundary
canonicalEnvironmentalEnablementBoundary = environmental-enablement-boundary
  false false false false false false false false false
  true false false true true true false

attributionRule : String
attributionRule =
  "Rasanen & Lindstrom 1999 (DOI 10.1111/j.1574-6941.1999.tb00561.x) owns its Acacia-rhizobium heat-stress propositions. Rasanen, Saijets, Jokinen & Lindstrom 2004 (DOI 10.1023/B:PLSO.0000030181.03575.e1) owns its controlled Acacia-Sinorhizobium drought-stress propositions. Fall et al. 2011 (DOI 10.1007/s13199-011-0128-0) owns its greenhouse Mesorhizobium strain/water-deficiency propositions. Isaac et al. 2011 sources retain ownership of their age/P/N-regime fixation contexts. Abaker/Berninger/Starr hydrology DOI 10.1016/j.jaridenv.2017.12.004 remains a distinct bulk-water measurement object. DASHI owns only the environment-indexed TaskFactorisation collisions, repair surface and no-promotion boundary; this owner does not close canonical reaction enablement, plant assimilation or deployment authority."
