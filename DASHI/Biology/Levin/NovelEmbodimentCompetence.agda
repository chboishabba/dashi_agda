module DASHI.Biology.Levin.NovelEmbodimentCompetence where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.SyntheticLivingAgentBoundary as Synthetic
import DASHI.Biology.Levin.ProblemSpaceAgency as ProblemSpace
import DASHI.Biology.Levin.SubstrateIndependentAgency as Agency

------------------------------------------------------------------------
-- Competence expressed after a novel body plan or sensorimotor remapping.

record EmbodimentRemapping : Set where
  field
    inheritedMaterial       : Bool
    novelGeometry           : Bool
    novelSensorPlacement    : Bool
    novelActuatorCoupling   : Bool
    noTaskSpecificTraining  : Bool
    noTaskSpecificSelection : Bool

record NovelCompetenceWitness : Set where
  field
    remapping             : EmbodimentRemapping
    reproducibleBehaviour : Bool
    taskPerformanceAboveControl : Bool
    perturbationSensitive : Bool
    alternativePathUsed   : Bool
    mechanismUnresolved   : Bool
    interpretation        : String

record NovelEmbodimentBiologyAdapter : Set where
  field
    syntheticBoundary : Synthetic.SyntheticLivingAgentBoundary
    problemSpace      : ProblemSpace.ProblemSpaceAgencyBoundary
    agencyBoundary    : Agency.SubstrateIndependentAgencyBoundary
    competenceNeedsExperiment : Bool
    noveltyNeedsHistoricalAudit : Bool
    welfareStatusRemainsSeparate : Bool

NovelBodyImpliesNovelMind : Bool
NovelBodyImpliesNovelMind = false

ImmediateCompetenceImpliesNoInheritedCapacity : Bool
ImmediateCompetenceImpliesNoInheritedCapacity = false

NovelSensorimotorUseImpliesConsciousAccess : Bool
NovelSensorimotorUseImpliesConsciousAccess = false
