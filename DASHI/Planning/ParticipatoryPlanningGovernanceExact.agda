module DASHI.Planning.ParticipatoryPlanningGovernanceExact where

open import DASHI.Core.Prelude

import DASHI.Core.EpistemicInquiryGovernance as Inquiry
import DASHI.Governance.ContestedAmbientAuthorityHyperformalismExact as Ambient
import DASHI.Governance.OppositionInterfaceAntiDomesticationExact as Opposition

------------------------------------------------------------------------
-- PARTICIPATORY PLANNING GOVERNANCE
--
-- Planning consultation is decomposed using the already-merged epistemic
-- governance and opposition anti-domestication owners.  Expression, access,
-- contestability, co-decision, governing authority and meta-rule authority are
-- therefore not collapsed into one participation bit.
------------------------------------------------------------------------

data PlanningParticipant : Set where
  planningAuthority affectedResident exteriorCommunity : PlanningParticipant

data PlanningDatum : Set where
  consultationSubmission : PlanningDatum

planningVoice : Inquiry.VoiceContribution PlanningParticipant PlanningDatum
planningVoice =
  Inquiry.voiceContribution
    affectedResident
    consultationSubmission
    "affected resident contributes a planning consultation submission"

------------------------------------------------------------------------
-- A compact planning-stage vocabulary.  These labels are intentionally not
-- ordered by an automatic promotion relation.
------------------------------------------------------------------------

data ParticipationStage : Set where
  informedStage
  respondentStage
  contestingStage
  coDecidingStage
  governingStage : ParticipationStage

stageLevel : ParticipationStage → Inquiry.AuthorityLevel
stageLevel informedStage = Inquiry.informed
stageLevel respondentStage = Inquiry.respondent
stageLevel contestingStage = Inquiry.contesting
stageLevel coDecidingStage = Inquiry.coDeciding
stageLevel governingStage = Inquiry.governing

consultedIsNotDefinitionallyGoverning :
  stageLevel respondentStage ≡ stageLevel governingStage → ⊥
consultedIsNotDefinitionallyGoverning ()

contestingIsNotDefinitionallyCoDeciding :
  stageLevel contestingStage ≡ stageLevel coDecidingStage → ⊥
contestingIsNotDefinitionallyCoDeciding ()

coDecidingIsNotDefinitionallyGoverning :
  stageLevel coDecidingStage ≡ stageLevel governingStage → ⊥
coDecidingIsNotDefinitionallyGoverning ()

------------------------------------------------------------------------
-- Existing generic no-promotion theorems transported into planning language.
------------------------------------------------------------------------

accessDoesNotAutomaticallyCreatePlanningAuthority :
  Inquiry.AccessImpliesAuthorityPermission → ⊥
accessDoesNotAutomaticallyCreatePlanningAuthority =
  Inquiry.accessCannotAutomaticallyPromoteToAuthority

exerciseDoesNotAutomaticallyCreatePlanningEffect :
  Inquiry.ExerciseImpliesEffectPermission → ⊥
exerciseDoesNotAutomaticallyCreatePlanningEffect =
  Inquiry.exerciseCannotAutomaticallyPromoteToEffect

expressionDoesNotAutomaticallyCreatePlanningAuthority :
  Inquiry.ExpressionImpliesAuthorityPermission → ⊥
expressionDoesNotAutomaticallyCreatePlanningAuthority =
  Inquiry.expressionCannotAutomaticallyPromoteToAuthority

admittedObjectionDoesNotAutomaticallyAlterAdmissionRule :
  Opposition.CanAlterAdmissionRule Opposition.recognisedOpposition → ⊥
admittedObjectionDoesNotAutomaticallyAlterAdmissionRule =
  Opposition.recognisedOppositionCannotAutomaticallyAlterRule

planningConsultationDoesNotExhaustExteriorOpposition :
  Ambient.LeftExhaustive Opposition.oppositionAdministrativeInterface → ⊥
planningConsultationDoesNotExhaustExteriorOpposition =
  Opposition.oppositionInterfaceIsNotExhaustive

------------------------------------------------------------------------
-- Positive certificate: realised constitutive agency requires authority,
-- practical access and contestability together.  Exercise/effect remain
-- additional obligations in the source owner.
------------------------------------------------------------------------

record PlanningConstitutiveAgency
    {Agent : Set}
    (governance : Inquiry.LayeredEpistemicGovernance Agent)
    (agent : Agent)
    (coordinate : Inquiry.InquiryCoordinate) : Set where
  constructor planningConstitutiveAgency
  field
    realisedAgency :
      Inquiry.RealisedConstitutiveAgency governance agent coordinate

open PlanningConstitutiveAgency public

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ParticipatoryPlanningBoundary : Set where
  constructor participatoryPlanningBoundary
  field
    consultationEqualsConstitutiveAuthority : Bool
    contestabilityEqualsCoDecision : Bool
    coDecisionEqualsGoverningAuthority : Bool
    admittedOppositionEqualsMetaRuleAuthority : Bool
    visibleParticipationExhaustsExteriorCommunity : Bool

canonicalParticipatoryPlanningBoundary : ParticipatoryPlanningBoundary
canonicalParticipatoryPlanningBoundary =
  participatoryPlanningBoundary false false false false false
