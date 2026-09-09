module DASHI.ComputerScience.FibreMachineFoundation369Exact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Weave
import DASHI.Geometry.SSP369Ultrametric as SSP

------------------------------------------------------------------------
-- FIBRE-FIRST COMPUTER-SCIENCE FOUNDATION
--
-- Programs, implementations, builds, and physical executions are treated as
-- fibres by default.  No representation is globally "the program": an
-- observer is adequate only relative to a declared downstream consumer.
-- Binary, balanced-ternary/369, FRACTRAN, quantum, compiler, git/build, zkSEC,
-- and physical supply-chain layers can therefore reuse the same descent law.
------------------------------------------------------------------------

record ExecutionFibre : Set₁ where
  constructor executionFibre
  field
    State : Set
    Surface : Set
    Outcome : Set
    Cost : Set
    observe : State → Surface
    consumer : State → Outcome
    cost : State → Cost

open ExecutionFibre public

ConsumerAdequate : ExecutionFibre → Set
ConsumerAdequate fibre =
  Descent.ConsumerSufficient (observe fibre) (consumer fibre)

record RefinementFibre (base : ExecutionFibre) : Set₁ where
  constructor refinementFibre
  field
    Refinement : Set
    refine : State base → Refinement

open RefinementFibre public

RefinementAdequate :
  (base : ExecutionFibre) →
  RefinementFibre base →
  Set
RefinementAdequate base refinement =
  Repair.RefinementRepairs
    (observe base)
    (refine refinement)
    (consumer base)

------------------------------------------------------------------------
-- 369 / FRACTRAN regression.
--
-- The existing signed SSP execution carrier deliberately keeps the 369 fibre
-- address distinct from program/execution length.  The canonical geometric
-- and virtual 53 states therefore provide an immediate CS regression:
-- identical 369 address, different execution-length consumer.
------------------------------------------------------------------------

address369Observer :
  Weave.SignedSSPExecutionState → SSP.Address 3
address369Observer = Weave.address369

executionLengthConsumer :
  Weave.SignedSSPExecutionState → Nat
executionLengthConsumer = Weave.executionLength

sameCanonicalFiftyThree369Address :
  address369Observer Weave.canonicalVirtualFiftyThreeState
  ≡ address369Observer Weave.canonicalGeometryFiftyThreeState
sameCanonicalFiftyThree369Address = refl

differentCanonicalFiftyThreeExecutionLength :
  executionLengthConsumer Weave.canonicalVirtualFiftyThreeState
  ≡ executionLengthConsumer Weave.canonicalGeometryFiftyThreeState →
  ⊥
differentCanonicalFiftyThreeExecutionLength ()

canonical369ExecutionLengthCollision :
  Descent.ConsumerNonDescentWitness
    address369Observer
    executionLengthConsumer
canonical369ExecutionLengthCollision =
  Descent.consumerNonDescentWitness
    Weave.canonicalVirtualFiftyThreeState
    Weave.canonicalGeometryFiftyThreeState
    sameCanonicalFiftyThree369Address
    differentCanonicalFiftyThreeExecutionLength

address369AloneNotConsumerSufficientForExecutionLength :
  Descent.ConsumerSufficient
    address369Observer
    executionLengthConsumer →
  ⊥
address369AloneNotConsumerSufficientForExecutionLength =
  Descent.nonDescentWitnessBlocksSufficiency
    canonical369ExecutionLengthCollision

addressAndExecutionObserver :
  Weave.SignedSSPExecutionState → SSP.Address 3 × Nat
addressAndExecutionObserver =
  Observer.pairObserver
    address369Observer
    executionLengthConsumer

addressAndExecutionIsConsumerSufficient :
  Descent.ConsumerSufficient
    addressAndExecutionObserver
    executionLengthConsumer
addressAndExecutionIsConsumerSufficient =
  Observer.pairRefinesRight
    address369Observer
    executionLengthConsumer

executionLengthCoordinateRepairs369Collision :
  Repair.RefinementRepairs
    address369Observer
    executionLengthConsumer
    executionLengthConsumer
executionLengthCoordinateRepairs369Collision =
  addressAndExecutionIsConsumerSufficient

anyRepairMustSeparateCanonical369Collision :
  ∀ {Refinement : Set}
    (refine : Weave.SignedSSPExecutionState → Refinement) →
  Repair.RefinementRepairs
    address369Observer
    refine
    executionLengthConsumer →
  refine Weave.canonicalVirtualFiftyThreeState
  ≡ refine Weave.canonicalGeometryFiftyThreeState →
  ⊥
anyRepairMustSeparateCanonical369Collision refine repaired =
  Repair.refinementRepairSeparatesWitness
    canonical369ExecutionLengthCollision
    repaired

record FibreMachineFoundation369Boundary : Set where
  constructor fibreMachineFoundation369Boundary
  field
    fibresArePrimitive : Bool
    observerAdequacyIsConsumerRelative : Bool
    same369AddressImpliesSameExecutionLength : Bool
    executionLengthRepairsThis369Collision : Bool
    everyValidRepairSeparatesThisCollision : Bool
    sameCardinalityImpliesSameMachineSemantics : Bool
    observerPairingHasSingleCanonicalOwner : Bool

canonicalFibreMachineFoundation369Boundary :
  FibreMachineFoundation369Boundary
canonicalFibreMachineFoundation369Boundary =
  fibreMachineFoundation369Boundary
    true true false true true false true
