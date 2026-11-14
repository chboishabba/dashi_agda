{-# OPTIONS --safe #-}
module DASHI.Reasoning.FederatedStreamingBlockRefinementFiniteExact where

-- Finite source-independent specimen of overlapped communication, queue
-- backpressure, and block-refinement revision admission. It does NOT assert
-- that original LILA/Qwen code implements diffusion or that WAN RTT vanishes.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)

data Admission (A : Set) : Set where
  rejected : Admission A
  admitted : A → Admission A

-- A *completed* two-stage pipeline can overlap communication of item B
-- and compute of item A when their inputs are independently ready.
maxNat : Nat → Nat → Nat
maxNat zero n = n
maxNat (suc m) zero = suc m
maxNat (suc m) (suc n) = suc (maxNat m n)

sequentialTwoStage : Nat → Nat → Nat
sequentialTwoStage transfer compute = transfer + compute

steadyStateInterval : Nat → Nat → Nat
steadyStateInterval transfer compute = maxNat transfer compute

-- 8 units transfer and 20 compute: first item still requires both.
firstItemCompletesAfter28 :
  sequentialTwoStage 8 20 ≡ 28
firstItemCompletesAfter28 = refl

-- Once pipeline is filled, *different independent* work items complete
-- at the bottleneck stage interval. This does not remove startup latency.
twoStageSteadyStateInterval20 :
  steadyStateInterval 8 20 ≡ 20
twoStageSteadyStateInterval20 = refl

-- Communication can be bottleneck instead: no always-free-WAN inference.
bandwidthBottleneckInterval20 :
  steadyStateInterval 20 8 ≡ 20
bandwidthBottleneckInterval20 = refl

-- Even when tasks are independent, end-to-end completion is not the
-- per-item interval. Three tasks on the finite pipeline take 68 units:
-- A transfer 0..8, compute 8..28; B transfer 8..16, compute 28..48;
-- C transfer 16..24, compute 48..68.
threePipelinedItems : Nat
threePipelinedItems = (8 + 20) + (20 + 20)

threeItemsCompleteAfter68 :
  threePipelinedItems ≡ 68
threeItemsCompleteAfter68 = refl

threeSequentialItems : Nat
threeSequentialItems = 28 + (28 + 28)

threeSequentialItemsNeed84 :
  threeSequentialItems ≡ 84
threeSequentialItemsNeed84 = refl

-- Backpressure: express a finite two-slot queue using an intrinsic
-- capacity type instead of a Nat occupancy that can overrun.
data Queue2 : Set where
  empty one two : Queue2

enqueue : Queue2 → Admission Queue2
enqueue empty = admitted one
enqueue one = admitted two
enqueue two = rejected

dequeue : Queue2 → Admission Queue2
dequeue empty = rejected
dequeue one = admitted empty
dequeue two = admitted one

cannotOverfill :
  enqueue two ≡ rejected
cannotOverfill = refl

cannotUnderflow :
  dequeue empty ≡ rejected
cannotUnderflow = refl

secondEnqueueFillsQueue :
  enqueue one ≡ admitted two
secondEnqueueFillsQueue = refl

thirdEnqueueRejected :
  enqueue two ≡ rejected
thirdEnqueueRejected = refl

dequeueFullQueue :
  dequeue two ≡ admitted one
dequeueFullQueue = refl

-- Separate immutable model revision and mutable history/denoising
-- generation: neither can silently stand in for the other.
data Revision : Set where
  oldRevision currentRevision : Revision

data Generation : Set where
  generation0 generation1 : Generation

sameRevision : Revision → Revision → Bool
sameRevision oldRevision oldRevision = true
sameRevision oldRevision currentRevision = false
sameRevision currentRevision oldRevision = false
sameRevision currentRevision currentRevision = true

sameGeneration : Generation → Generation → Bool
sameGeneration generation0 generation0 = true
sameGeneration generation0 generation1 = false
sameGeneration generation1 generation0 = false
sameGeneration generation1 generation1 = true

record BlockCandidate : Set where
  constructor candidate
  field
    modelRevision : Revision
    historyGeneration : Generation
    refinementGeneration : Generation
    proposedValue : Nat
open BlockCandidate public

admitCandidate :
  Revision → Generation → Generation → BlockCandidate →
  Admission Nat
admitCandidate model history refinement proposal
  with sameRevision model (modelRevision proposal)
     | sameGeneration history (historyGeneration proposal)
     | sameGeneration refinement (refinementGeneration proposal)
... | true | true | true = admitted (proposedValue proposal)
... | _ | _ | _ = rejected

validCandidateAccepted : (value : Nat) →
  admitCandidate currentRevision generation0 generation1
    (candidate currentRevision generation0 generation1 value)
    ≡ admitted value
validCandidateAccepted value = refl

staleModelRejected : (value : Nat) →
  admitCandidate currentRevision generation0 generation1
    (candidate oldRevision generation0 generation1 value)
    ≡ rejected
staleModelRejected value = refl

staleHistoryRejected : (value : Nat) →
  admitCandidate currentRevision generation0 generation1
    (candidate currentRevision generation1 generation1 value)
    ≡ rejected
staleHistoryRejected value = refl

staleRefinementRejected : (value : Nat) →
  admitCandidate currentRevision generation0 generation1
    (candidate currentRevision generation0 generation0 value)
    ≡ rejected
staleRefinementRejected value = refl

-- An arbitrary, actually verified expert/denoiser computation can be
-- transported through admission, but no source neural equivalence is
-- manufactured by this conditional law.
admittedRefinementPreservesReference :
  (reference worker : Nat → Nat) →
  ((x : Nat) → worker x ≡ reference x) →
  (input : Nat) →
  admitCandidate currentRevision generation0 generation1
    (candidate currentRevision generation0 generation1 (worker input))
  ≡ admitted (reference input)
admittedRefinementPreservesReference reference worker agree input
  rewrite agree input = refl

-- A finite counterexample: accepting generation0 in generation1 would
-- contradict constructors; refusal is a real admission property.
oldGenerationCannotCommit :
  (value : Nat) →
  admitCandidate currentRevision generation0 generation1
    (candidate currentRevision generation0 generation0 value)
  ≡ admitted value →
  false ≡ true
oldGenerationCannotCommit value ()

------------------------------------------------------------------------
-- Batching lemma: arbitrary finite lists of independently source-
-- equivalent refinement results may be transported element by element.
-- It does not claim that an actual neural denoiser is separable in time.
------------------------------------------------------------------------

mapResult : (Nat → Nat) → List Nat → List Nat
mapResult f [] = []
mapResult f (x ∷ xs) = f x ∷ mapResult f xs

blockBatchRefinementPreservesReference :
  (reference worker : Nat → Nat) →
  ((x : Nat) → worker x ≡ reference x) →
  (inputs : List Nat) →
  mapResult worker inputs ≡ mapResult reference inputs
blockBatchRefinementPreservesReference reference worker agree [] = refl
blockBatchRefinementPreservesReference reference worker agree (x ∷ xs)
  rewrite agree x
        | blockBatchRefinementPreservesReference reference worker agree xs
  = refl
