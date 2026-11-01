{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.DreamFlowSprintConstitutionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)
open import DASHI.Cognition.PNF.ComplexityArithmetic using (_≤ᶜ_)

------------------------------------------------------------------------
-- FORMAL MODEL: O, R, C, S, L, P, G, F
--
-- O  organization / accountable operating context
-- R  requirement/RFP contract that defines the requested outcome
-- C  code/executable implementation under review
-- S  runtime/semantic state
-- L  lattice/fibre structure in which state and residuals live
-- P  proposed transition/change
-- G  governance/risk/authority context
-- F  gap function measuring remaining distance to the accepted target
--
-- The types remain generic: this is a sprint/process constitution rather than
-- another semantic compiler.  Runtime specializations must instantiate these
-- fields with the existing PNF/delta authority.
------------------------------------------------------------------------

record ZKPModel
    (Organization Requirement Code State Lattice Proposal Governance : Set) : Set₁ where
  constructor zkpModel
  field
    O : Organization
    R : Requirement
    C : Code
    S : State
    L : Lattice
    P : Proposal
    G : Governance
    F : State → Proposal → Nat

open ZKPModel public

------------------------------------------------------------------------
-- Constraints, invariants, preconditions, transition, postconditions.
------------------------------------------------------------------------

record SprintSemantics
    (Organization Requirement Code State Lattice Proposal Governance : Set) : Set₁ where
  field
    constraint :
      Organization → Requirement → Governance → Code → Proposal → Set
    invariant : Lattice → State → Set
    precondition :
      Organization → Requirement → Governance → Lattice → Proposal → State → Set
    transition : Code → Proposal → State → State
    postcondition :
      Organization → Requirement → Governance → Lattice →
      Proposal → State → State → Set

open SprintSemantics public

record CertifiedTransition
    {Organization Requirement Code State Lattice Proposal Governance : Set}
    (model : ZKPModel Organization Requirement Code State Lattice Proposal Governance)
    (semantics : SprintSemantics Organization Requirement Code State Lattice Proposal Governance) : Set₁ where
  field
    constraintSatisfied :
      constraint semantics (O model) (R model) (G model) (C model) (P model)
    invariantBefore : invariant semantics (L model) (S model)
    preconditionSatisfied :
      precondition semantics
        (O model) (R model) (G model) (L model) (P model) (S model)

    nextState : State
    transitionExact :
      nextState ≡ transition semantics (C model) (P model) (S model)

    invariantAfter : invariant semantics (L model) nextState
    postconditionSatisfied :
      postcondition semantics
        (O model) (R model) (G model) (L model)
        (P model) (S model) nextState

    gapNonIncreasing :
      F model nextState (P model) ≤ᶜ F model (S model) (P model)

open CertifiedTransition public

------------------------------------------------------------------------
-- Acceptance is stronger than “the change ran”.  The proposal is accepted only
-- when all semantic/process obligations hold and its declared gap is closed.
------------------------------------------------------------------------

record AcceptedTransition
    {Organization Requirement Code State Lattice Proposal Governance : Set}
    {model : ZKPModel Organization Requirement Code State Lattice Proposal Governance}
    {semantics : SprintSemantics Organization Requirement Code State Lattice Proposal Governance}
    (certified : CertifiedTransition model semantics) : Set₁ where
  field
    gapClosed : F model (nextState certified) (P model) ≡ zero

open AcceptedTransition public

------------------------------------------------------------------------
-- Work/performance acceptance is deliberately separate from semantic acceptance.
------------------------------------------------------------------------

record PhysicalAcceptance : Set where
  constructor physicalAcceptance
  field
    referenceWork : Nat
    candidateWork : Nat
    referenceBoundaryCrossings : Nat
    candidateBoundaryCrossings : Nat
    workNoWorse : candidateWork ≤ᶜ referenceWork
    boundaryNoWorse : candidateBoundaryCrossings ≤ᶜ referenceBoundaryCrossings

open PhysicalAcceptance public

record SprintAcceptance
    {Organization Requirement Code State Lattice Proposal Governance : Set}
    {model : ZKPModel Organization Requirement Code State Lattice Proposal Governance}
    {semantics : SprintSemantics Organization Requirement Code State Lattice Proposal Governance}
    (certified : CertifiedTransition model semantics) : Set₁ where
  field
    semanticAcceptance : AcceptedTransition certified
    physicalAcceptance : PhysicalAcceptance

open SprintAcceptance public

------------------------------------------------------------------------
-- Fail-closed boundaries.
------------------------------------------------------------------------

data RuntimeSpeedCanReplaceConstraintProof : Set where

data RuntimeSpeedCanReplaceInvariantProof : Set where

data RuntimeSpeedCanReplacePreconditionProof : Set where

data RuntimeSpeedCanReplacePostconditionProof : Set where

data GapReductionCanReplaceGapClosureAtAcceptance : Set where

speedCannotReplaceConstraint : RuntimeSpeedCanReplaceConstraintProof → ⊥
speedCannotReplaceConstraint ()

speedCannotReplaceInvariant : RuntimeSpeedCanReplaceInvariantProof → ⊥
speedCannotReplaceInvariant ()

speedCannotReplacePrecondition : RuntimeSpeedCanReplacePreconditionProof → ⊥
speedCannotReplacePrecondition ()

speedCannotReplacePostcondition : RuntimeSpeedCanReplacePostconditionProof → ⊥
speedCannotReplacePostcondition ()

gapReductionIsProgressNotAcceptance : GapReductionCanReplaceGapClosureAtAcceptance → ⊥
gapReductionIsProgressNotAcceptance ()
