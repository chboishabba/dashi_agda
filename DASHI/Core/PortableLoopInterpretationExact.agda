module DASHI.Core.PortableLoopInterpretationExact where

open import DASHI.Core.Prelude
import DASHI.Core.PortableSemanticInterpretationExact as Portable

------------------------------------------------------------------------
-- EXACT FINITE LOOP INTERPRETATION FIXTURE
--
-- `jsSequential` and `gpuParallel` name implementation roles only.  This file
-- does not import or claim the full operational semantics of JavaScript or
-- WebGPU.  It proves the narrower reusable point: distinct execution strategy
-- metadata can refine the same exact consumer-observed logical result.
------------------------------------------------------------------------

sumNat : List Nat → Nat
sumNat [] = zero
sumNat (x ∷ xs) = x + sumNat xs

data LoopBackend : Set where
  jsSequential : LoopBackend
  gpuParallel : LoopBackend

data ExecutionStrategy : Set where
  sequentialSchedule : ExecutionStrategy
  parallelSchedule : ExecutionStrategy

record LoopArtifact : Set where
  constructor loopArtifact
  field
    input : List Nat
    strategy : ExecutionStrategy
    logicalResult : Nat

open LoopArtifact public

LoopImplementation : LoopBackend → Set
LoopImplementation _ = LoopArtifact

interpretLoop :
  (backend : LoopBackend) →
  List Nat →
  LoopImplementation backend
interpretLoop jsSequential xs =
  loopArtifact xs sequentialSchedule (sumNat xs)
interpretLoop gpuParallel xs =
  loopArtifact xs parallelSchedule (sumNat xs)

loopProblem : Portable.SemanticInterpretationProblem
loopProblem =
  Portable.semanticInterpretationProblem
    (List Nat)
    Nat
    LoopBackend
    LoopImplementation
    ⊤
    (λ _ → Nat)
    sumNat
    (λ _ result → result)
    interpretLoop
    (λ _ _ implementation → logicalResult implementation)

canonicalInput : List Nat
canonicalInput = 2 ∷ 3 ∷ 5 ∷ []

jsRefinesLogicalResult :
  Portable.SemanticRefinement
    loopProblem jsSequential canonicalInput tt
jsRefinesLogicalResult = Portable.semanticRefinement refl

gpuRefinesLogicalResult :
  Portable.SemanticRefinement
    loopProblem gpuParallel canonicalInput tt
gpuRefinesLogicalResult = Portable.semanticRefinement refl

CanonicalLoopConsumerEquivalence : Set
CanonicalLoopConsumerEquivalence =
  Portable.BackendEquivalentFor
    loopProblem canonicalInput tt jsSequential gpuParallel

jsAndGpuEquivalentForResult : CanonicalLoopConsumerEquivalence
jsAndGpuEquivalentForResult =
  Portable.twoRefinementsGiveConsumerEquivalence
    jsRefinesLogicalResult
    gpuRefinesLogicalResult

DifferentExecutionStrategy : Set
DifferentExecutionStrategy =
  strategy (interpretLoop jsSequential canonicalInput)
  ≡
  strategy (interpretLoop gpuParallel canonicalInput)
  → ⊥

canonicalDifferentExecutionStrategy : DifferentExecutionStrategy
canonicalDifferentExecutionStrategy ()

record PortableLoopInterpretationBoundary : Set where
  constructor portableLoopInterpretationBoundary
  field
    sameLogicalResultImpliesSameSchedule : Bool
    sameLogicalResultImpliesSameScheduleIsFalse :
      sameLogicalResultImpliesSameSchedule ≡ false
    sameLogicalResultImpliesSameEfficiency : Bool
    sameLogicalResultImpliesSameEfficiencyIsFalse :
      sameLogicalResultImpliesSameEfficiency ≡ false
    roleNameImportsFullRuntimeSemantics : Bool
    roleNameImportsFullRuntimeSemanticsIsFalse :
      roleNameImportsFullRuntimeSemantics ≡ false

canonicalPortableLoopInterpretationBoundary :
  PortableLoopInterpretationBoundary
canonicalPortableLoopInterpretationBoundary =
  portableLoopInterpretationBoundary
    false refl
    false refl
    false refl
