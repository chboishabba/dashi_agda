module DASHI.Core.RelationalSelfDescentExact where

------------------------------------------------------------------------
-- TRANSPORT-BASED RELATIONAL SELF DESCENT
--
-- DASHI CONTRIBUTION
--
-- Relationship-indexed local sections need not be literally equal on every
-- context change.  This file retains explicit two-sided transports and a
-- cycle/holonomy residual.  The construction is intentionally called
-- "stack-like" only in commentary: no claim is made that a psychological
-- source supplied a groupoid, stack, or Grothendieck topology.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.RelationalSelfStalkExact as Stalk

data RelationalPatch : Set where
  patchAB : RelationalPatch
  patchBC : RelationalPatch
  patchCA : RelationalPatch

record TypedTransport (State : Set) : Set₁ where
  constructor typed-transport
  field
    sourcePatch targetPatch : RelationalPatch
    forward : State → State
    backward : State → State
    backwardAfterForward :
      (state : State) → backward (forward state) ≡ state
    forwardAfterBackward :
      (state : State) → forward (backward state) ≡ state
    transportReceipt : String

open TypedTransport public

identityTransport :
  ∀ {State : Set} →
  RelationalPatch → RelationalPatch → TypedTransport State
identityTransport source target =
  typed-transport source target
    (λ state → state)
    (λ state → state)
    (λ state → refl)
    (λ state → refl)
    "DASHI identity transport witness"

record TriadicLocalSections (State : Set) : Set where
  constructor triadic-local-sections
  field
    sectionAB : State
    sectionBC : State
    sectionCA : State

open TriadicLocalSections public

data HolonomyResidual : Set where
  cycleCloses : HolonomyResidual
  cycleResidualRetained : HolonomyResidual

record RelationalDescentState (State : Set) : Set₁ where
  constructor relational-descent-state
  field
    localSections : TriadicLocalSections State
    transportABtoBC : TypedTransport State
    transportBCtoCA : TypedTransport State
    transportCAtoAB : TypedTransport State
    cycleResidual : HolonomyResidual
    provenanceReceipt : String

open RelationalDescentState public

data DemoSection : Set where
  sameLocalSection : DemoSection

canonicalLocals : TriadicLocalSections DemoSection
canonicalLocals =
  triadic-local-sections
    sameLocalSection sameLocalSection sameLocalSection

closedDescent : RelationalDescentState DemoSection
closedDescent =
  relational-descent-state
    canonicalLocals
    (identityTransport patchAB patchBC)
    (identityTransport patchBC patchCA)
    (identityTransport patchCA patchAB)
    cycleCloses
    "DASHI closed-cycle descent witness"

residualDescent : RelationalDescentState DemoSection
residualDescent =
  relational-descent-state
    canonicalLocals
    (identityTransport patchAB patchBC)
    (identityTransport patchBC patchCA)
    (identityTransport patchCA patchAB)
    cycleResidualRetained
    "DASHI same locals/transports with retained cycle residual"

localSectionObserver :
  RelationalDescentState DemoSection →
  TriadicLocalSections DemoSection
localSectionObserver = localSections

holonomyConsumer :
  RelationalDescentState DemoSection →
  HolonomyResidual
holonomyConsumer = cycleResidual

sameLocalSections :
  localSectionObserver closedDescent
  ≡ localSectionObserver residualDescent
sameLocalSections = refl

differentHolonomy :
  holonomyConsumer closedDescent
  ≡ holonomyConsumer residualDescent →
  ⊥
differentHolonomy ()

localSectionsDoNotDetermineHolonomy :
  Descent.ConsumerNonDescentWitness
    localSectionObserver holonomyConsumer
localSectionsDoNotDetermineHolonomy =
  Descent.consumerNonDescentWitness
    closedDescent residualDescent sameLocalSections differentHolonomy

holonomyCannotFactorThroughLocalSections :
  Descent.FactorsThrough localSectionObserver holonomyConsumer → ⊥
holonomyCannotFactorThroughLocalSections =
  Descent.nonDescentWitnessBlocksFactorization
    localSectionsDoNotDetermineHolonomy

record RelationalSelfDescentBoundary : Set where
  constructor relational-self-descent-boundary
  field
    contextChangeRequiresLiteralSelfEquality : Bool
    typedTransportIsRetainedEvidence : Bool
    localSectionsDetermineCycleResidual : Bool
    sourceTheoryAlreadyContainsStackSemantics : Bool
    pathResidualMayRemainAfterLocalAgreement : Bool

canonicalRelationalSelfDescentBoundary : RelationalSelfDescentBoundary
canonicalRelationalSelfDescentBoundary =
  relational-self-descent-boundary false true false false true
