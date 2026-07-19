module DASHI.Governance.RelationalFlowGateAlgebra where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Set)

------------------------------------------------------------------------
-- Typed gate algebra for the current relational-flow lane.
--
-- These are logical interfaces, not factual findings. Concrete applications
-- must provide evidence for their premises in domain-specific modules.

data GateStatus : Set where
  gateOpen : GateStatus
  gateBlocked : GateStatus
  gateUnknown : GateStatus

record GateDeprivationLaw
    (Eligible Assessment FinalOutcome : Set) : Set₁ where
  field
    eligible : Eligible
    assessmentBlocked : Assessment → Set
    finalOutcomeUnknown : FinalOutcome → Set
    gateHarm : Set
    blockedAssessmentYieldsGateHarm :
      (a : Assessment) → assessmentBlocked a → gateHarm

record PresenceImpairmentSeparation
    (Presence Impairment : Set) : Set₁ where
  field
    presenceDoesNotEntailImpairment : Presence → Impairment → Set
    impairmentRequiresIndependentEvidence : Impairment → Set

record MissionRepairContinuity
    (Mission Asset Subsidy TaxPrivilege Legitimacy Repair : Set) : Set₁ where
  field
    missionContinues : Mission
    assetContinues : Asset
    subsidyContinues : Subsidy
    taxPrivilegeContinues : TaxPrivilege
    legitimacyContinues : Legitimacy
    repairContinuityRequired : Repair

record NoSurvivorAsCastration
    (SurvivorFeedback MissionThreat : Set) : Set₁ where
  field
    survivorFeedback : SurvivorFeedback
    missionThreatProjectionBlocked : MissionThreat → Set

record NoHumanPollutantPromotion
    (HumanGroup PollutantSign : Set) : Set₁ where
  field
    humanGroup : HumanGroup
    pollutantSign : PollutantSign
    promotionBlocked : Set

record SystemFivePeopleLaw
    (People Feedback GovernanceUpdate : Set) : Set₁ where
  field
    people : People
    feedback : Feedback
    update : GovernanceUpdate
    feedbackReachesUpdate : Set

record RelationalFlowGateBundle : Set₁ where
  field
    Eligible Assessment FinalOutcome : Set
    Presence Impairment : Set
    Mission Asset Subsidy TaxPrivilege Legitimacy Repair : Set
    SurvivorFeedback MissionThreat : Set
    HumanGroup PollutantSign : Set
    People Feedback GovernanceUpdate : Set

    gateDeprivation :
      GateDeprivationLaw Eligible Assessment FinalOutcome

    presenceImpairment :
      PresenceImpairmentSeparation Presence Impairment

    missionRepair :
      MissionRepairContinuity
        Mission Asset Subsidy TaxPrivilege Legitimacy Repair

    survivorNotCastration :
      NoSurvivorAsCastration SurvivorFeedback MissionThreat

    humanNotPollutant :
      NoHumanPollutantPromotion HumanGroup PollutantSign

    systemFivePeople :
      SystemFivePeopleLaw People Feedback GovernanceUpdate

open RelationalFlowGateBundle public

------------------------------------------------------------------------
-- Non-collapse witnesses.

data DistinctCoordinates (A B : Set) : Set where
  coordinatesKeptDistinct : DistinctCoordinates A B

presenceAndImpairmentKeptDistinct :
  {P I : Set} → DistinctCoordinates P I
presenceAndImpairmentKeptDistinct =
  coordinatesKeptDistinct

missionAndRepairKeptDistinct :
  {M R : Set} → DistinctCoordinates M R
missionAndRepairKeptDistinct =
  coordinatesKeptDistinct

humanAndPollutantKeptDistinct :
  {H P : Set} → DistinctCoordinates H P
humanAndPollutantKeptDistinct =
  coordinatesKeptDistinct
