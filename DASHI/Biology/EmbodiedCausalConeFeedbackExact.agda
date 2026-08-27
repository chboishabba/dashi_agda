module DASHI.Biology.EmbodiedCausalConeFeedbackExact where

open import DASHI.Core.Prelude

import DASHI.Biology.EmbodiedOptionConeInteroceptionExact as Body
import DASHI.Biology.ObserverRelativeReachableSubfabricExact as Subfabric

------------------------------------------------------------------------
-- FULL EMBODIED CAUSAL-CONE FEEDBACK
--
-- Behaviour may change the world/base, while regulation/inference may move
-- vertically inside one world fibre.  History can deform transition gates and
-- barriers without deleting the underlying carrier.
------------------------------------------------------------------------

data WorldState : Set where
  constrainedWorld openedWorld : WorldState

data InternalRegime : Set where
  regulatedInternal mobilisedInternal : InternalRegime

data HistoryState : Set where
  ordinaryHistory learnedThreatHistory : HistoryState

record EmbodiedSystemState : Set where
  constructor embodiedSystemState
  field
    world : WorldState
    internal : InternalRegime
    history : HistoryState

open EmbodiedSystemState public

mobilisedConstrained : EmbodiedSystemState
mobilisedConstrained =
  embodiedSystemState constrainedWorld mobilisedInternal learnedThreatHistory

regulatedConstrained : EmbodiedSystemState
regulatedConstrained =
  embodiedSystemState constrainedWorld regulatedInternal learnedThreatHistory

data Action : Set where
  leaveAction seekHelpAction freezeAction restAction : Action

act : Action → EmbodiedSystemState → EmbodiedSystemState
act leaveAction state =
  embodiedSystemState openedWorld (internal state) (history state)
act seekHelpAction state =
  embodiedSystemState openedWorld regulatedInternal (history state)
act freezeAction state = state
act restAction state =
  embodiedSystemState (world state) regulatedInternal (history state)

regulate : EmbodiedSystemState → EmbodiedSystemState
regulate state =
  embodiedSystemState (world state) regulatedInternal (history state)

verticalRegulationPreservesWorld :
  (state : EmbodiedSystemState) →
  world (regulate state) ≡ world state
verticalRegulationPreservesWorld state = refl

horizontalLeaveChangesWorld :
  world (act leaveAction mobilisedConstrained)
  ≡ world mobilisedConstrained → ⊥
horizontalLeaveChangesWorld ()

seekHelpCanChangeWorldAndInternal :
  act seekHelpAction mobilisedConstrained
  ≡ mobilisedConstrained → ⊥
seekHelpCanChangeWorldAndInternal ()

------------------------------------------------------------------------
-- Literal reachability over whole embodied states.
------------------------------------------------------------------------

data Step : EmbodiedSystemState → EmbodiedSystemState → Set where
  regulationStep : Step mobilisedConstrained regulatedConstrained
  leaveStep :
    Step mobilisedConstrained
      (embodiedSystemState openedWorld mobilisedInternal learnedThreatHistory)
  helpStep :
    Step mobilisedConstrained
      (embodiedSystemState openedWorld regulatedInternal learnedThreatHistory)

data Reach : EmbodiedSystemState → EmbodiedSystemState → Set where
  reachRefl : ∀ {x} → Reach x x
  reachStep : ∀ {x y} → Step x y → Reach x y
  reachCompose : ∀ {x y z} → Reach x y → Reach y z → Reach x z

regulatedFutureReachable : Reach mobilisedConstrained regulatedConstrained
regulatedFutureReachable = reachStep regulationStep

------------------------------------------------------------------------
-- History-dependent deformation of transition law.
------------------------------------------------------------------------

data TransitionLaw : Set where
  baselineLaw learnedThreatLaw : TransitionLaw

data CandidateTransition : Set where
  approachSafety defensiveWithdrawal : CandidateTransition

gate : TransitionLaw → CandidateTransition → Bool
gate baselineLaw approachSafety = true
gate baselineLaw defensiveWithdrawal = true
gate learnedThreatLaw approachSafety = false
gate learnedThreatLaw defensiveWithdrawal = true

barrier : TransitionLaw → CandidateTransition → Nat
barrier baselineLaw approachSafety = 1
barrier baselineLaw defensiveWithdrawal = 1
barrier learnedThreatLaw approachSafety = 3
barrier learnedThreatLaw defensiveWithdrawal = 1

historyDeformationCanCloseApproachWithoutDeletingTransition :
  gate baselineLaw approachSafety ≡ gate learnedThreatLaw approachSafety → ⊥
historyDeformationCanCloseApproachWithoutDeletingTransition ()

barrierAlsoChanges :
  barrier baselineLaw approachSafety ≡ barrier learnedThreatLaw approachSafety → ⊥
barrierAlsoChanges ()

------------------------------------------------------------------------
-- Felt-state fibre: one coarse report can contain distinct fine body/history
-- trajectories.
------------------------------------------------------------------------

data CoarseFeelingReport : Set where tenseReport settledReport : CoarseFeelingReport

record FineFeltCarrier : Set where
  constructor fineFeltCarrier
  field
    coarseReport : CoarseFeelingReport
    body : Body.BodyState
    prior : Body.InteroceptivePrior
    historyCarrier : HistoryState

open FineFeltCarrier public

tenseRegulated : FineFeltCarrier
tenseRegulated =
  fineFeltCarrier
    tenseReport Body.regulatedBody Body.threatPrior ordinaryHistory

tenseMobilised : FineFeltCarrier
tenseMobilised =
  fineFeltCarrier
    tenseReport Body.mobilisedBody Body.threatPrior learnedThreatHistory

sameFeelingReport :
  coarseReport tenseRegulated ≡ coarseReport tenseMobilised
sameFeelingReport = refl

sameReportDoesNotRecoverFineCarrier :
  tenseRegulated ≡ tenseMobilised → ⊥
sameReportDoesNotRecoverFineCarrier ()

recoveryPreservesHistoryCarrier :
  history (regulate mobilisedConstrained) ≡ history mobilisedConstrained
recoveryPreservesHistoryCarrier = refl

record EmbodiedCausalConeBoundary : Set where
  constructor embodiedCausalConeBoundary
  field
    allDynamicsAreVertical : Bool
    actionOnlyChangesInternalState : Bool
    traumaIsStoredAsOnePoint : Bool
    transitionDeformationDeletesCarrier : Bool
    feelingReportEqualsPhysiology : Bool
    wholeStateReachabilityIsExplicit : Bool

canonicalEmbodiedCausalConeBoundary : EmbodiedCausalConeBoundary
canonicalEmbodiedCausalConeBoundary =
  embodiedCausalConeBoundary false false false false false true
