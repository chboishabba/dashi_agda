module DASHI.ComputerScience.Goldbach29Signed369VendorBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
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
-- Exact success-path microstep accounting from Mike's two published rule sets.
--
-- Goldbach30 success branch:
--   NT_B*f -> SA                                      (1 dispatch)
--   SA*a -> SB*b*c ; SB -> SA                        (2 per unit of a)
--   SA*c -> RA_A*a^2*d^2*f                           (1 finish)
-- hence 2*a + 2 microsteps.
--
-- Goldbach29 success branch:
--   NT_B*f*a -> SB*b*c ; SB -> NT_B*f                (2 per unit of a)
--   NT_B*f -> NT2_B*a*b ; NT2_B -> NT_B              (2 staging)
--   NT_B*b*c -> RA_A*a*d^2*f                         (1 reused finish)
-- hence 2*a + 3 microsteps.
--
-- We encode the recurrence rather than importing upstream code.  This is a
-- DASHI-owned reconstruction of the attributed rule-count consequence.
------------------------------------------------------------------------

oldSuccessExecutionLength : Nat → Nat
oldSuccessExecutionLength zero = 2
oldSuccessExecutionLength (suc a) =
  suc (suc (oldSuccessExecutionLength a))

newSuccessExecutionLength : Nat → Nat
newSuccessExecutionLength zero = 3
newSuccessExecutionLength (suc a) =
  suc (suc (newSuccessExecutionLength a))

newSuccessExecutionLengthIsOneMore :
  (a : Nat) →
  newSuccessExecutionLength a ≡ suc (oldSuccessExecutionLength a)
newSuccessExecutionLengthIsOneMore zero = refl
newSuccessExecutionLengthIsOneMore (suc a)
  rewrite newSuccessExecutionLengthIsOneMore a = refl

signedSSPAlreadySeparatesProgramFromExecution :
  Signed.shortestProgramLengthEqualsExecutionLength
    Signed.canonicalSignedSSPWeaveBoundary
  ≡ false
signedSSPAlreadySeparatesProgramFromExecution =
  Signed.shortestProgramLengthEqualsExecutionLengthIsFalse
    Signed.canonicalSignedSSPWeaveBoundary

staticReductionCanIncreaseSuccessExecutionLength :
  (a : Nat) →
  (suc externalGoldbach29FractionCount ≡ externalGoldbach30FractionCount)
  ×
  (newSuccessExecutionLength a ≡ suc (oldSuccessExecutionLength a))
staticReductionCanIncreaseSuccessExecutionLength a =
  externalReductionSavesOneFraction
  , newSuccessExecutionLengthIsOneMore a

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
    successPathExecutionLengthAlsoReduced : Bool
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
  Repair.RefinementRepairs
    Fibre369.address369Observer
    refine
    Fibre369.executionLengthConsumer →
  refine Signed.canonicalVirtualFiftyThreeState
  ≡ refine Signed.canonicalGeometryFiftyThreeState →
  ⊥
anyConsumerRepairMustSeparateKnown369Collision refine repaired same =
  Fibre369.anyRepairMustSeparateCanonical369Collision
    refine
    repaired
    same
