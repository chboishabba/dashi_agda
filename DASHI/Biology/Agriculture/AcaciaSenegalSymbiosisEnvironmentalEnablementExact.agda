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
-- ACACIA / SINORHIZOBIUM ENVIRONMENTAL ENABLEMENT FIBRE
--
-- This owner pays only an information/requirement seam around the existing
-- nitrogenase `reactionEnablement` debt.  It does NOT promote that global stage
-- to closed.  Heat, drought, phosphorus/age, bulk water balance and nodule/root
-- microenvironment remain independent situated coordinates.
--
-- Existing Acacia heat-stress source reused from Nodulation:
-- Rasanen & Lindstrom (1999), FEMS Microbiology Ecology 28(1):63-74.
-- DOI 10.1111/j.1574-6941.1999.tb00561.x.
--
-- New drought-stress source:
-- Rasanen, Saijets, Jokinen & Lindstrom (2004), Plant and Soil 260:237-251.
-- DOI 10.1023/B:PLSO.0000030181.03575.e1.
--
-- Edaphic donor reused from AcaciaSenegalBNFEdaphicLESExact:
-- Isaac et al. (2011), DOI 10.1016/j.foreco.2010.11.011.
------------------------------------------------------------------------

rasanen2004DOI : String
rasanen2004DOI = "10.1023/B:PLSO.0000030181.03575.e1"

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
    soilPAndTreeAgeRemainFixationContext : Bool
    bulkSoilWaterIsNotNoduleMicroenvironmentMeasurement : Bool
open EnvironmentalEnablementReading public

canonicalEnvironmentalReading : EnvironmentalEnablementReading
canonicalEnvironmentalReading = environmental-enablement-reading
  true true true true true

------------------------------------------------------------------------
-- Finite DASHI information-loss witness.
--
-- These worlds are synthetic.  The cited sources own only the empirical premise
-- that environmental state matters to the Acacia-rhizobium symbiosis. DASHI
-- owns the factorisation counterexample below.
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
  acaciaCompatibleSinorhizobium : RhizobialIdentity

hostIdentity : EnablementWorld → HostIdentity
hostIdentity _ = acaciaSenegalHost

rhizobialIdentity : EnablementWorld → RhizobialIdentity
rhizobialIdentity _ = acaciaCompatibleSinorhizobium

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

------------------------------------------------------------------------
-- Repair surface.
------------------------------------------------------------------------

record EnvironmentalEnablementRepair : Set where
  constructor environmental-enablement-repair
  field
    hostIdentityRetained : Bool
    rhizobialIdentityRetained : Bool
    rootTemperatureRetained : Bool
    droughtWaterStatusRetained : Bool
    soilPhosphorusRetained : Bool
    treeAgeRetained : Bool
    infectionStageRetained : Bool
    nodulationStageRetained : Bool
    bulkSoilWaterRetainedSeparately : Bool
    noduleRootMicroenvironmentRetainedSeparately : Bool
    observerMethodRetained : Bool
    sourceIdentityRetained : Bool
open EnvironmentalEnablementRepair public

canonicalEnvironmentalEnablementRepair : EnvironmentalEnablementRepair
canonicalEnvironmentalEnablementRepair = environmental-enablement-repair
  true true true true true true true true true true true true

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
    rhizobialPresenceCreatesNodulation : Bool
    soilPAloneDeterminesEnablement : Bool
    bulkSoilMoistureEqualsNoduleMicroenvironment : Bool
    heatRecoveryCreatesUniversalTolerance : Bool
    droughtStudyCreatesFieldWaterBalance : Bool
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
  false false false false false false false true false false true true true false

attributionRule : String
attributionRule =
  "Rasanen & Lindstrom 1999 (DOI 10.1111/j.1574-6941.1999.tb00561.x) owns its Acacia-Sinorhizobium heat-stress propositions. Rasanen, Saijets, Jokinen & Lindstrom 2004 (DOI 10.1023/B:PLSO.0000030181.03575.e1) owns its controlled drought-stress propositions. Isaac et al. 2011 (DOI 10.1016/j.foreco.2010.11.011) retains ownership of the age/P fixation context. Abaker/Berninger/Starr hydrology DOI 10.1016/j.jaridenv.2017.12.004 remains a distinct bulk-water measurement object. DASHI owns only the environment-indexed TaskFactorisation collisions, repair surface and no-promotion boundary; this owner does not close the canonical reaction-enablement stage or any plant-assimilation stage."
