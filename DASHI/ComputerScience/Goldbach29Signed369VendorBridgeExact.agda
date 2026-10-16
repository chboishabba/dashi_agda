module DASHI.ComputerScience.Goldbach29Signed369VendorBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.ComputerScience.FibreMachineFoundation369Exact as Fibre369

------------------------------------------------------------------------
-- ATTRIBUTED EXTERNAL PRODUCER
--
-- Upstream owner: Mike Dupont / meta-introspector
-- Repository: meta-introspector/aok
-- Commit: c168223e96f7acc6179044f2a365a92db2e350c3
-- Upstream work: Goldbach29 29-fraction FRACTRAN construction and fstep_enc.
--
-- DASHI does not re-author or silently internalise that construction here.
-- This module records the attributed numerical/reduction boundary and reuses
-- DASHI's already-proved signed-SSP/369 fibre semantics to state what follows
-- from coarse/fine separation without pretending the external 30<->29 weak
-- bisimulation has already been discharged.
------------------------------------------------------------------------

externalGoldbach30FractionCount : Nat
externalGoldbach30FractionCount = 30

externalGoldbach29FractionCount : Nat
externalGoldbach29FractionCount = 29

externalReductionSavesOneFraction :
  suc externalGoldbach29FractionCount ≡ externalGoldbach30FractionCount
externalReductionSavesOneFraction = refl

------------------------------------------------------------------------
-- Existing signed-369 theorem reused as the semantic law.
--
-- A coarse observer collision is not state identity.  The canonical virtual
-- and geometric 53 executions share the same 369 observer address but differ
-- in execution-length consumer.  This is the exact in-repo witness that the
-- Goldbach visualisation discussion needs: observer equality is weaker than
-- fine-state/consumer equality.
------------------------------------------------------------------------

fineStateNeedNotEqualCoarseObserver :
  Descent.ConsumerNonDescentWitness
    Fibre369.address369Observer
    Fibre369.executionLengthConsumer
fineStateNeedNotEqualCoarseObserver =
  Fibre369.canonical369ExecutionLengthCollision

coarse369NotSufficientForExecutionLength :
  Descent.ConsumerSufficient
    Fibre369.address369Observer
    Fibre369.executionLengthConsumer →
  ⊥
coarse369NotSufficientForExecutionLength =
  Fibre369.address369AloneNotConsumerSufficientForExecutionLength

------------------------------------------------------------------------
-- Consumer-relative reduction boundary.
--
-- Eliminating a control state (Mike's SA removal) is therefore not required
-- to preserve literal fine-state identity.  The correct target is preservation
-- of a declared consumer through an adequate relation/observer.  Until a
-- concrete relation on the pinned Goldbach30/29 reachable states is supplied,
-- DASHI records that theorem as unpaid rather than manufacturing equivalence.
------------------------------------------------------------------------

record GoldbachReductionConsumerBoundary : Set where
  constructor mkGoldbachReductionConsumerBoundary
  field
    mikeOwnsGoldbach29Construction : Bool
    dashiOwnsObserverTranslation : Bool
    fractionCountReducedThirtyToTwentyNine : Bool
    literalFineStateIdentityRequired : Bool
    consumerRelativeAdequacyRequired : Bool
    weakOrStutteringSimulationIsNaturalTarget : Bool
    fullReachableWeakBisimulationPaidFlag : Bool
    goldbachConjectureSolvedByThisBridge : Bool

open GoldbachReductionConsumerBoundary public

canonicalGoldbachReductionConsumerBoundary :
  GoldbachReductionConsumerBoundary
canonicalGoldbachReductionConsumerBoundary =
  mkGoldbachReductionConsumerBoundary
    true
    true
    true
    false
    true
    true
    false
    false

fullReachableWeakBisimulationPaid : Bool
fullReachableWeakBisimulationPaid = false

goldbachReductionConsumerBoundary : GoldbachReductionConsumerBoundary
goldbachReductionConsumerBoundary = canonicalGoldbachReductionConsumerBoundary

------------------------------------------------------------------------
-- Signed-SSP 369 repair principle exported for the Goldbach lane.
-- Any valid refinement that repairs the canonical 369 collision must separate
-- the witness states.  This is the constructive rule for improving a coarse
-- Goldbach visualiser: add exactly the coordinate needed by the consumer,
-- rather than demanding globally injective state rendering.
------------------------------------------------------------------------

anyConsumerRepairMustSeparateKnown369Collision :
  ∀ {Refinement : Set}
    (refine : Signed.SignedSSPExecutionState → Refinement) →
  Descent.ConsumerSufficient
    (λ state → Fibre369.address369Observer state , refine state)
    Fibre369.executionLengthConsumer →
  refine Signed.canonicalVirtualFiftyThreeState
  ≡ refine Signed.canonicalGeometryFiftyThreeState →
  ⊥
anyConsumerRepairMustSeparateKnown369Collision refine repaired same =
  Fibre369.anyRepairMustSeparateCanonical369Collision
    refine
    repaired
    same
