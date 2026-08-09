module DASHI.Reasoning.DevelopmentalExplanationWithdrawalExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection
import DASHI.Reasoning.DevelopmentalAttunementPNFBridge as Developmental
import DASHI.Reasoning.RelationalStateCore as Core

------------------------------------------------------------------------
-- Explanation / impact / repair separation.
--
-- Candidate mechanisms may explain why a caregiver response was difficult to
-- inhibit.  They do not inhabit the impact or repair coordinates and no
-- constructor in this module converts explanation into exemption.
------------------------------------------------------------------------

data CandidateMechanism : Set where
  rapidAssociation executiveInhibitionFailure workingMemoryPreservation : CandidateMechanism
  solutionImpulse stressDisorganisation learnedConversationHabit : CandidateMechanism
  unknownMechanism : CandidateMechanism

record CausalExplanation : Set where
  constructor causalExplanation
  field
    actor : Core.Participant
    behaviour : Developmental.ResponseSignal
    mechanism : CandidateMechanism
    evidenceLabel : String
    candidateOnly : Bool

open CausalExplanation public

record ExperiencedImpact : Set where
  constructor experiencedImpact
  field
    affected : Core.Participant
    impactLabel : String
    lossOfThread : Bool
    withdrawalRisk : Bool
    impactReceipt : String

open ExperiencedImpact public

record RepairObligation : Set where
  constructor repairObligation
  field
    returnConversationalFloor : Bool
    acknowledgeDisplacement : Bool
    preserveOpenContribution : Bool
    permitPauseWithoutErasure : Bool
    changedExpectationRequired : Bool
    repairReceipt : String

open RepairObligation public

record ExplanationImpactRepairSeparation : Set where
  constructor explanationImpactRepairSeparation
  field
    explanation : CausalExplanation
    impact : ExperiencedImpact
    repair : RepairObligation
    coordinatesKeptDistinct : Bool
    explanationDoesNotDeleteImpact : Bool
    explanationDoesNotDeleteRepair : Bool
    separationReceipt : String

-- Constructorless forbidden promotions: there is no proof term witnessing
-- that a candidate explanation automatically erases impact or repair.
data ExplanationErasesImpact : Set where

data ExplanationErasesRepair : Set where

explanationErasesImpactImpossible : ExplanationErasesImpact → ⊥
explanationErasesImpactImpossible ()

explanationErasesRepairImpossible : ExplanationErasesRepair → ⊥
explanationErasesRepairImpossible ()

------------------------------------------------------------------------
-- Context-sensitive speech / withdrawal selection.
--
-- Withdrawal is neither globally promoted nor globally pathologised.  The
-- existing exact portfolio comparator shows that continuing is preferable
-- after attuned repair, while protective withdrawal is preferable when
-- repeated displacement makes continuation carry sufficiently high burden.
------------------------------------------------------------------------

continueAfterAttunedRepair : Selection.BranchMetric
continueAfterAttunedRepair = Selection.branchMetric
  "continue-speaking-after-attuned-repair"
  0
  (Selection.attractorDrift Selection.towardAttractor 4)
  1
  1
  0
  2
  true
  "high expected uptake, low servicing cost and preserved repair channel"

continueAfterRepeatedDisplacement : Selection.BranchMetric
continueAfterRepeatedDisplacement = Selection.branchMetric
  "continue-speaking-after-repeated-displacement"
  0
  (Selection.attractorDrift Selection.towardAttractor 3)
  1
  4
  4
  1
  true
  "possible informational value remains, but reconstruction and diversion burden are high"

protectiveWithdrawal : Selection.BranchMetric
protectiveWithdrawal = Selection.branchMetric
  "protective-withdrawal"
  1
  (Selection.attractorDrift Selection.neutralDrift 0)
  0
  1
  0
  1
  true
  "bounded pause preserves capacity without claiming the original rupture is repaired"

attunedContinuePortfolio : Selection.BranchPortfolio
attunedContinuePortfolio = Selection.branchPortfolio
  "attuned-continue"
  (continueAfterAttunedRepair ∷ [])
  []
  10
  "continuation after the floor is returned and the contribution remains open"

repeatedDisplacementContinuePortfolio : Selection.BranchPortfolio
repeatedDisplacementContinuePortfolio = Selection.branchPortfolio
  "repeated-displacement-continue"
  (continueAfterRepeatedDisplacement ∷ [])
  []
  10
  "continuation under repeated reconstruction and diversion cost"

protectiveWithdrawalPortfolio : Selection.BranchPortfolio
protectiveWithdrawalPortfolio = Selection.branchPortfolio
  "protective-withdrawal"
  (protectiveWithdrawal ∷ [])
  []
  10
  "capacity-preserving pause"

attunedContinuationBeatsWithdrawal :
  Selection.StrictlyPreferred
    attunedContinuePortfolio
    protectiveWithdrawalPortfolio
attunedContinuationBeatsWithdrawal = Selection.strictlyPreferred 4 refl

withdrawalBeatsRepeatedDisplacementContinuation :
  Selection.StrictlyPreferred
    protectiveWithdrawalPortfolio
    repeatedDisplacementContinuePortfolio
withdrawalBeatsRepeatedDisplacementContinuation =
  Selection.strictlyPreferred 2 refl

attunedContinueWithinCapacity :
  Selection.WithinCapacity attunedContinuePortfolio
attunedContinueWithinCapacity = Selection.withinCapacity 9 refl

repeatedContinueWithinCapacity :
  Selection.WithinCapacity repeatedDisplacementContinuePortfolio
repeatedContinueWithinCapacity = Selection.withinCapacity 6 refl

withdrawalWithinCapacity :
  Selection.WithinCapacity protectiveWithdrawalPortfolio
withdrawalWithinCapacity = Selection.withinCapacity 9 refl

record ContextSensitiveWithdrawalLaw : Set where
  field
    continuationPreferredAfterRepair :
      Selection.StrictlyPreferred
        attunedContinuePortfolio
        protectiveWithdrawalPortfolio
    withdrawalPreferredUnderRepeatedDisplacement :
      Selection.StrictlyPreferred
        protectiveWithdrawalPortfolio
        repeatedDisplacementContinuePortfolio
    allComparedBranchesServiceable :
      Selection.WithinCapacity attunedContinuePortfolio
      × Selection.WithinCapacity repeatedDisplacementContinuePortfolio
      × Selection.WithinCapacity protectiveWithdrawalPortfolio

canonicalContextSensitiveWithdrawalLaw : ContextSensitiveWithdrawalLaw
canonicalContextSensitiveWithdrawalLaw = record
  { continuationPreferredAfterRepair = attunedContinuationBeatsWithdrawal
  ; withdrawalPreferredUnderRepeatedDisplacement =
      withdrawalBeatsRepeatedDisplacementContinuation
  ; allComparedBranchesServiceable =
      attunedContinueWithinCapacity ,
      repeatedContinueWithinCapacity ,
      withdrawalWithinCapacity
  }

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record ExplanationWithdrawalAuthorityBoundary : Set where
  field
    adhdCandidateMechanismDiagnosesCaregiver : Bool
    explanationMakesImpactUnreasonable : Bool
    explanationRemovesRepairRequirement : Bool
    withdrawalIsAlwaysOptimal : Bool
    withdrawalIsAlwaysPathological : Bool
    finiteWeightsAreEmpiricallyCalibrated : Bool
    boundaryNote : String

canonicalExplanationWithdrawalAuthorityBoundary :
  ExplanationWithdrawalAuthorityBoundary
canonicalExplanationWithdrawalAuthorityBoundary = record
  { adhdCandidateMechanismDiagnosesCaregiver = false
  ; explanationMakesImpactUnreasonable = false
  ; explanationRemovesRepairRequirement = false
  ; withdrawalIsAlwaysOptimal = false
  ; withdrawalIsAlwaysPathological = false
  ; finiteWeightsAreEmpiricallyCalibrated = false
  ; boundaryNote =
      "Candidate inhibition or association mechanisms are separate from impact and repair. Exact finite portfolios prove context sensitivity only; their weights are structural witnesses, not calibrated clinical utilities."
  }
