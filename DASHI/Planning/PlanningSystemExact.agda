module DASHI.Planning.PlanningSystemExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- ABSTRACT PLANNING
--
-- A plan is not identified with one action or one realised future.  It is a
-- predicate on histories from an initial situated state: an admissible future
-- cone.  Proposal, approval, implementation and observation remain distinct.
------------------------------------------------------------------------

record PlanningSystem : Set₁ where
  field
    State       : Set
    Time        : Set
    Action      : Set
    Constraint  : Set
    Observation : Set

    step        : State → Action → State → Set
    applies     : Constraint → State → Time → Set
    observe     : State → Observation

open PlanningSystem public

History : PlanningSystem → Set
History system = Time system → State system

record PlanAt (system : PlanningSystem) (initial : State system) : Set₁ where
  field
    admits : History system → Set
    startsAtInitial :
      (history : History system) → admits history →
      (time : Time system) → Set

open PlanAt public

-- `startsAtInitial` is intentionally left abstract at this level because a
-- generic planning system need not designate a canonical initial time.  A
-- concrete time model can instantiate it with equality at t₀.

data PlanningStage : Set where
  proposed admissible approved implemented observed : PlanningStage

proposalIsNotApproval : proposed ≡ approved → ⊥
proposalIsNotApproval ()

approvalIsNotImplementation : approved ≡ implemented → ⊥
approvalIsNotImplementation ()

implementationIsNotObservation : implemented ≡ observed → ⊥
implementationIsNotObservation ()

record StagedPlanningDecision : Set₁ where
  field
    Proposal       : Set
    AdmissiblePlan : Set
    ApprovedPlan   : Set
    Implementation : Set
    Outcome        : Set

    admit      : Proposal → AdmissiblePlan
    approve    : AdmissiblePlan → ApprovedPlan
    implement  : ApprovedPlan → Implementation
    observeOut : Implementation → Outcome

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record PlanningSystemBoundary : Set where
  constructor planningSystemBoundary
  field
    planIsIdentifiedWithSingleAction : Bool
    planIsIdentifiedWithSingleActionIsFalse :
      planIsIdentifiedWithSingleAction ≡ false

    approvalIsIdentifiedWithImplementation : Bool
    approvalIsIdentifiedWithImplementationIsFalse :
      approvalIsIdentifiedWithImplementation ≡ false

planningSystemBoundaryExact : PlanningSystemBoundary
planningSystemBoundaryExact =
  planningSystemBoundary false refl false refl
