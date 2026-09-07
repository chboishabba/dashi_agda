module DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact where

------------------------------------------------------------------------
-- CLIMATE DUTY ROUTE SEARCH
--
-- This file does NOT assert that the Commonwealth presently owes a negligence
-- duty to every person in Australia for climate-attributed injury or death.
-- It represents that candidate claim precisely enough to ask where the current
-- authority graph blocks, weighs against, or leaves open the route.
--
-- Primary calibration:
--   Pabai v Commonwealth of Australia (No 2) [2025] FCA 796.
--   Federal Court appeal file VID1479/2025 is procedural material only unless a
--   later judgment is separately entered into the atlas.
--
-- Negligence lineage calibration:
--   Donoghue v Stevenson [1932] AC 562.
--
-- The candidate-class/harm formulation and route-search records below are DASHI
-- synthetic queries, not propositions attributed to Wigney J or Donoghue.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge
import DASHI.Cognition.PNF.SensibLawPabaiRecognitionRemedyGapExact as Pabai

------------------------------------------------------------------------
-- Candidate duty coordinates.
------------------------------------------------------------------------

data CandidatePlaintiffClass : Set where
  personsPresentInAustralia : CandidatePlaintiffClass
  pleadedTorresStraitApplicantClass : CandidatePlaintiffClass
  otherPreciselyDefinedClass : CandidatePlaintiffClass


data CandidateHarm : Set where
  climateAttributedPhysicalInjury : CandidateHarm
  climateAttributedDeath : CandidateHarm
  culturalOrRelationalLoss : CandidateHarm
  propertyLoss : CandidateHarm
  otherSpecifiedHarm : CandidateHarm


data DutyIssue : Set where
  reasonableForeseeability : DutyIssue
  knowledge : DutyIssue
  control : DutyIssue
  vulnerability : DutyIssue
  assumptionOfResponsibility : DutyIssue
  plaintiffClassDeterminacy : DutyIssue
  harmTypeDeterminacy : DutyIssue
  temporalScope : DutyIssue
  causation : DutyIssue
  scopeOfDuty : DutyIssue
  statutoryCoherence : DutyIssue
  coreGovernmentPolicy : DutyIssue
  institutionalCompetence : DutyIssue
  publicAuthorityFunction : DutyIssue
  compensability : DutyIssue


record CandidateClimateDuty : Set where
  constructor candidate-climate-duty
  field
    defendant : String
    plaintiffs : CandidatePlaintiffClass
    harm : CandidateHarm
    allegedRisk : String
    assertedDuty : String
    currentlyEstablishedByThisModule : Bool
    currentlyEstablishedByThisModuleIsFalse :
      currentlyEstablishedByThisModule ≡ false

open CandidateClimateDuty public

australiaPhysicalInjuryCandidate : CandidateClimateDuty
australiaPhysicalInjuryCandidate = candidate-climate-duty
  "Commonwealth of Australia"
  personsPresentInAustralia
  climateAttributedPhysicalInjury
  "anthropogenic climate risk"
  "candidate duty concerning reasonably foreseeable climate-attributed physical injury to persons present in Australia"
  false refl

australiaDeathCandidate : CandidateClimateDuty
australiaDeathCandidate = candidate-climate-duty
  "Commonwealth of Australia"
  personsPresentInAustralia
  climateAttributedDeath
  "anthropogenic climate risk"
  "candidate duty concerning reasonably foreseeable climate-attributed death to persons present in Australia"
  false refl

------------------------------------------------------------------------
-- Each issue must retain whether it is a hard blocker, a factor, an evidential
-- requirement, or unresolved. 'Policy' is never an opaque terminal node.
------------------------------------------------------------------------

data IssueState : Set where
  satisfied : IssueState
  weighsForDuty : IssueState
  weighsAgainstDuty : IssueState
  hardBlock : IssueState
  disputed : IssueState
  untested : IssueState
  notApplicable : IssueState


record DutyIssueReceipt : Set where
  constructor duty-issue-receipt
  field
    issue : DutyIssue
    state : IssueState
    proposition : String
    authority : Edge.SourceIdentity
    gateForce : Edge.GateForce
    directSourceSupport : Bool
    reasoningNeedsReopen : Bool

open DutyIssueReceipt public

------------------------------------------------------------------------
-- Minimal-cut / decompositional queries.
------------------------------------------------------------------------

record DutyRouteCut : Set where
  constructor duty-route-cut
  field
    candidate : CandidateClimateDuty
    firstBlockingIssue : DutyIssue
    blockingRule : String
    authority : Edge.SourceIdentity
    categoricalAsCurrentlyStated : Bool
    narrowerPredicateSearchRequired : Bool
    removalWouldRequireLegislation : Bool
    removalCouldBeCommonLawDevelopment : Bool
    statusClaimIsSourceBacked : Bool

open DutyRouteCut public

record ApparentWeldReopenQuery : Set where
  constructor apparent-weld-reopen-query
  field
    apparentRule : String
    candidateNarrowerRule : String
    controllingAuthority : Edge.SourceIdentity
    sourceActuallyEntailsBroadRule : Bool
    sourceActuallyEntailsBroadRuleChecked : Bool
    resultPromoted : Bool
    resultPromotedIsFalse : resultPromoted ≡ false

open ApparentWeldReopenQuery public

corePolicyReopenQuery : ApparentWeldReopenQuery
corePolicyReopenQuery = apparent-weld-reopen-query
  "core government policy -> no negligence duty"
  "specified policy function + identified institutional/statutory predicates -> factor or blocker against the posited duty"
  Edge.pabaiAuthority
  false
  false
  false refl

------------------------------------------------------------------------
-- Search firewalls.
------------------------------------------------------------------------

data LargeClassIsIndeterminateByDefinition : Set where
data PhysicalInjuryAutomaticallyCreatesDuty : Set where
data ClimateScienceFindingAutomaticallyCreatesDuty : Set where
data PabaiNoDutyClosesEveryPossibleClimateDuty : Set where
data ExistingNoDutyMeansLegislationIsLogicallyNecessaryForEveryReformulation : Set where

australianPopulationSizeDoesNotDefineIndeterminacy :
  LargeClassIsIndeterminateByDefinition → ⊥
australianPopulationSizeDoesNotDefineIndeterminacy ()

physicalInjuryDoesNotAutomaticallyCreateDuty : PhysicalInjuryAutomaticallyCreatesDuty → ⊥
physicalInjuryDoesNotAutomaticallyCreateDuty ()

scienceDoesNotAutomaticallyCreatePrivateDuty :
  ClimateScienceFindingAutomaticallyCreatesDuty → ⊥
scienceDoesNotAutomaticallyCreatePrivateDuty ()

pabaiDoesNotCloseEveryReformulatedDutyByDefinition :
  PabaiNoDutyClosesEveryPossibleClimateDuty → ⊥
pabaiDoesNotCloseEveryReformulatedDutyByDefinition ()

legislationNecessityMustBeProvedForSpecificRoute :
  ExistingNoDutyMeansLegislationIsLogicallyNecessaryForEveryReformulation → ⊥
legislationNecessityMustBeProvedForSpecificRoute ()

------------------------------------------------------------------------
-- Existing Pabai owner remains the negative calibration: serious recognised
-- harm does not itself determine negligence remedy.
------------------------------------------------------------------------

pabaiNegativeCalibration :
  Pabai.FactRecognitionImpliesRemedy → ⊥
pabaiNegativeCalibration = Pabai.factRecognitionDoesNotCreateRemedy
