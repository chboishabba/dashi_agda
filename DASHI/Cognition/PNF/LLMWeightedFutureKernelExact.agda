module DASHI.Cognition.PNF.LLMWeightedFutureKernelExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.LLMWeightedFutureQuotientExact as Weighted
import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Finite weighted analogue of a language-model output kernel.
------------------------------------------------------------------------

record BinaryWeightKernel : Set where
  constructor binaryWeightKernel
  field
    zeroWeight : Nat
    oneWeight : Nat

open BinaryWeightKernel public

totalWeight : BinaryWeightKernel → Nat
totalWeight kernel = zeroWeight kernel + oneWeight kernel

data KernelState : Set where
  leftBefore rightBefore leftAfter rightAfter : KernelState

data KernelAction : Set where
  extendContext : KernelAction

kernelObservation : KernelState → BinaryWeightKernel
kernelObservation leftBefore = binaryWeightKernel 1 1
kernelObservation rightBefore = binaryWeightKernel 1 1
kernelObservation leftAfter = binaryWeightKernel 2 0
kernelObservation rightAfter = binaryWeightKernel 0 2

currentNextTokenKernelEqual :
  kernelObservation leftBefore ≡ kernelObservation rightBefore
currentNextTokenKernelEqual = refl

allDisplayedKernelsHaveWeightTwo :
  (state : KernelState) → totalWeight (kernelObservation state) ≡ 2
allDisplayedKernelsHaveWeightTwo leftBefore = refl
allDisplayedKernelsHaveWeightTwo rightBefore = refl
allDisplayedKernelsHaveWeightTwo leftAfter = refl
allDisplayedKernelsHaveWeightTwo rightAfter = refl

futureKernelsDiffer :
  kernelObservation leftAfter ≡ kernelObservation rightAfter → ⊥
futureKernelsDiffer ()

advanceKernelState : KernelState → KernelState
advanceKernelState leftBefore = leftAfter
advanceKernelState rightBefore = rightAfter
advanceKernelState leftAfter = leftAfter
advanceKernelState rightAfter = rightAfter

record ExactKernelPost
    (before : KernelState)
    (action : KernelAction)
    (after : KernelState) : Set where
  constructor exactKernelPost
  field
    afterIsExact : after ≡ advanceKernelState before

open ExactKernelPost public

kernelSystem : Dependency.DependentActionSystem KernelState KernelAction
kernelSystem = record
  { Precondition = λ state action → ⊤
  ; Postcondition = ExactKernelPost
  ; actionLabel = λ action → "extend context"
  }

extendAdmissible :
  (state : KernelState) →
  Dependency.AdmissibleAction kernelSystem state extendContext
extendAdmissible state = record
  { precondition = tt
  ; after = advanceKernelState state
  ; postcondition = exactKernelPost refl
  ; dependencyReceipt = "deterministic context extension"
  }

extendTrace : List KernelAction
extendTrace = extendContext ∷ []

leftFutureKernelObservation :
  Future.FutureObservation
    kernelSystem kernelObservation leftBefore extendTrace
    (binaryWeightKernel 2 0)
leftFutureKernelObservation =
  Future.futureObservation
    leftAfter
    (Reachability.executesCons
      (extendAdmissible leftBefore)
      Reachability.executesNil)
    refl

rightCannotReachLeftKernel :
  Future.FutureObservation
    kernelSystem kernelObservation rightBefore extendTrace
    (binaryWeightKernel 2 0)
  → ⊥
rightCannotReachLeftKernel
  (Future.futureObservation after
    (Reachability.executesCons admissible Reachability.executesNil)
    observationProof)
  with afterIsExact (Dependency.postcondition admissible)
... | refl = contradiction observationProof
  where
    contradiction : binaryWeightKernel 0 2 ≡ binaryWeightKernel 2 0 → ⊥
    contradiction ()

sameCurrentKernelDoesNotImplyWeightedFutureEquivalence :
  Future.FutureObservationEquivalent
    kernelSystem kernelObservation leftBefore rightBefore
  → ⊥
sameCurrentKernelDoesNotImplyWeightedFutureEquivalence equivalent =
  rightCannotReachLeftKernel
    (Future.forward
      (Future.sameFutureLanguage equivalent
        extendTrace (binaryWeightKernel 2 0))
      leftFutureKernelObservation)

------------------------------------------------------------------------
-- Instantiation of the generic weighted future quotient.
------------------------------------------------------------------------

outcomeWeight : BinaryWeightKernel → Bool → Nat
outcomeWeight kernel false = zeroWeight kernel
outcomeWeight kernel true = oneWeight kernel

traceWeight : KernelState → List KernelAction → Bool → Nat
traceWeight state [] outcome = outcomeWeight (kernelObservation state) outcome
traceWeight state (extendContext ∷ rest) outcome =
  traceWeight (advanceKernelState state) rest outcome

canonicalWeightedKernel :
  Weighted.WeightedFutureKernel KernelState KernelAction Bool
canonicalWeightedKernel = Weighted.weightedFutureKernel traceWeight

currentFalseWeightAgrees :
  traceWeight leftBefore [] false ≡ traceWeight rightBefore [] false
currentFalseWeightAgrees = refl

currentTrueWeightAgrees :
  traceWeight leftBefore [] true ≡ traceWeight rightBefore [] true
currentTrueWeightAgrees = refl

futureFalseWeightsSeparate :
  traceWeight leftBefore extendTrace false
  ≡ traceWeight rightBefore extendTrace false → ⊥
futureFalseWeightsSeparate ()

sameCurrentKernelDoesNotImplyCanonicalWeightedFutureEquivalence :
  Weighted.WeightedFutureEquivalent canonicalWeightedKernel leftBefore rightBefore → ⊥
sameCurrentKernelDoesNotImplyCanonicalWeightedFutureEquivalence equivalent =
  futureFalseWeightsSeparate
    (Weighted.sameWeightedFuture equivalent extendTrace false)

------------------------------------------------------------------------
-- Concrete approximate-future witness.
------------------------------------------------------------------------

natDistance : Nat → Nat → Nat
natDistance left right = (left ∸ right) + (right ∸ left)

natDistanceReflexive : (n : Nat) → natDistance n n ≡ 0
natDistanceReflexive n =
  trans
    (cong (λ k → k + (n ∸ n)) (n∸n≡0 n))
    refl

currentFalseDistanceIsZero :
  natDistance
    (traceWeight leftBefore [] false)
    (traceWeight rightBefore [] false)
  ≡ 0
currentFalseDistanceIsZero = refl

futureFalseDistanceIsTwo :
  natDistance
    (traceWeight leftBefore extendTrace false)
    (traceWeight rightBefore extendTrace false)
  ≡ 2
futureFalseDistanceIsTwo = refl

futureNotWithinUnitTolerance :
  Weighted.ApproximateWeightedFutureEquivalent
    canonicalWeightedKernel natDistance 1 leftBefore rightBefore → ⊥
futureNotWithinUnitTolerance approximate =
  impossible
    (Weighted.weightedFutureWithinTolerance approximate extendTrace false)
  where
    impossible : 2 ≤ 1 → ⊥
    impossible ()

------------------------------------------------------------------------
-- Boundary: integer weights are a finite kernel surface, not a claim of
-- calibrated probabilities or stochastic-process measure theory.
------------------------------------------------------------------------
