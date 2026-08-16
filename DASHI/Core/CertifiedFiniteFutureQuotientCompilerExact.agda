module DASHI.Core.CertifiedFiniteFutureQuotientCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.FiniteRankedRefinementStabilizationExact as Ranked
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.GenericFuturePartitionRefinementExact as Refinement
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as Bridge

record RelationIff (A B : Set) : Set where
  constructor relationIff
  field
    forward : A → B
    backward : B → A

open RelationIff public

composeIff : ∀ {A B C : Set} → RelationIff A B → RelationIff B C → RelationIff A C
composeIff left right = relationIff
  (λ a → forward right (forward left a))
  (λ c → backward left (backward right c))

RefineOnce :
  ∀ {State Action Observation : Set} →
  (State → Observation) →
  (Action → State → State) →
  (State → State → Set) →
  State → State → Set
RefineOnce {Action = Action} observe step relation left right =
  (observe left ≡ observe right)
  × ((action : Action) → relation (step action left) (step action right))

mapRefineIff :
  ∀ {State Action Observation}
    {observe : State → Observation}
    {step : Action → State → State}
    {leftRelation rightRelation : State → State → Set} →
  (∀ left right → RelationIff (leftRelation left right) (rightRelation left right)) →
  ∀ left right →
  RelationIff
    (RefineOnce observe step leftRelation left right)
    (RefineOnce observe step rightRelation left right)
mapRefineIff pointwise left right = relationIff
  (λ refined →
    proj₁ refined , λ action →
      forward (pointwise _ _) (proj₂ refined action))
  (λ refined →
    proj₁ refined , λ action →
      backward (pointwise _ _) (proj₂ refined action))

record CertifiedPartitionRefiner
    (State Action Observation : Set) : Set₁ where
  constructor certifiedPartitionRefiner
  field
    observe : State → Observation
    step : Action → State → State
    actionLabel : Action → String

    process : Ranked.RankedRefinementProcess
    initialCode : Ranked.Code process
    relation : Ranked.Code process → State → State → Set

    initialCorrect :
      (left right : State) →
      RelationIff
        (relation initialCode left right)
        (Refinement.RefinesToDepth 0 observe step left right)

    advanceCorrect :
      (code : Ranked.Code process) →
      (left right : State) →
      RelationIff
        (relation (Ranked.advance process code) left right)
        (RefineOnce observe step (relation code) left right)

open CertifiedPartitionRefiner public

forwardIterate :
  ∀ {State Action Observation} →
  (compiler : CertifiedPartitionRefiner State Action Observation) →
  Nat → Ranked.Code (process compiler)
forwardIterate compiler zero = initialCode compiler
forwardIterate compiler (suc depth) =
  Ranked.advance (process compiler) (forwardIterate compiler depth)

advanceCommutesWithBackwardIterate :
  (process : Ranked.RankedRefinementProcess) →
  (depth : Nat) →
  (code : Ranked.Code process) →
  Ranked.advance process (Ranked.iterate process depth code)
  ≡ Ranked.iterate process depth (Ranked.advance process code)
advanceCommutesWithBackwardIterate process zero code = refl
advanceCommutesWithBackwardIterate process (suc depth) code =
  advanceCommutesWithBackwardIterate process depth (Ranked.advance process code)

forwardEqualsBackwardIterate :
  ∀ {State Action Observation} →
  (compiler : CertifiedPartitionRefiner State Action Observation) →
  (depth : Nat) →
  forwardIterate compiler depth
  ≡ Ranked.iterate (process compiler) depth (initialCode compiler)
forwardEqualsBackwardIterate compiler zero = refl
forwardEqualsBackwardIterate compiler (suc depth) =
  trans
    (cong (Ranked.advance (process compiler))
      (forwardEqualsBackwardIterate compiler depth))
    (advanceCommutesWithBackwardIterate
      (process compiler) depth (initialCode compiler))

codeAtCorrect :
  ∀ {State Action Observation}
    (compiler : CertifiedPartitionRefiner State Action Observation)
    (depth : Nat)
    (left right : State) →
  RelationIff
    (relation compiler (forwardIterate compiler depth) left right)
    (Refinement.RefinesToDepth depth
      (observe compiler) (step compiler) left right)
codeAtCorrect compiler zero left right = initialCorrect compiler left right
codeAtCorrect compiler (suc depth) left right =
  composeIff
    (advanceCorrect compiler (forwardIterate compiler depth) left right)
    (mapRefineIff
      (λ successorLeft successorRight →
        codeAtCorrect compiler depth successorLeft successorRight)
      left right)

transportRelation :
  ∀ {State Action Observation}
    (compiler : CertifiedPartitionRefiner State Action Observation)
    {left right : State}
    {from to : Ranked.Code (process compiler)} →
  from ≡ to →
  relation compiler from left right →
  relation compiler to left right
transportRelation compiler refl related = related

stableAtFromCodeFixedPoint :
  ∀ {State Action Observation}
    (compiler : CertifiedPartitionRefiner State Action Observation)
    (depth : Nat) →
  forwardIterate compiler depth
    ≡ Ranked.advance (process compiler) (forwardIterate compiler depth) →
  Refinement.StableAt depth (observe compiler) (step compiler)
stableAtFromCodeFixedPoint compiler depth codeStable =
  Refinement.stableAt forwardStable Refinement.refinementMonotone
  where
    forwardStable :
      ∀ {left right} →
      Refinement.RefinesToDepth depth
        (observe compiler) (step compiler) left right →
      Refinement.RefinesToDepth (suc depth)
        (observe compiler) (step compiler) left right
    forwardStable {left} {right} related =
      forward (codeAtCorrect compiler (suc depth) left right)
        (transportRelation compiler codeStable
          (backward (codeAtCorrect compiler depth left right) related))

record CompiledFutureQuotient
    {State Action Observation : Set}
    (compiler : CertifiedPartitionRefiner State Action Observation) : Set₁ where
  constructor compiledFutureQuotient
  field
    stableDepth : Nat
    depthBound : stableDepth ≤ Ranked.rankBound (process compiler)
    stableRefinement :
      Refinement.StableAt stableDepth (observe compiler) (step compiler)
    canonicalExact :
      (left right : State) →
      (Refinement.RefinesToDepth stableDepth
        (observe compiler) (step compiler) left right →
        Future.FutureObservationEquivalent
          (Bridge.deterministicSystem (step compiler) (actionLabel compiler))
          (observe compiler) left right)
      ×
      (Future.FutureObservationEquivalent
          (Bridge.deterministicSystem (step compiler) (actionLabel compiler))
          (observe compiler) left right →
        Refinement.RefinesToDepth stableDepth
          (observe compiler) (step compiler) left right)

open CompiledFutureQuotient public

compileFutureQuotient :
  ∀ {State Action Observation}
    (compiler : CertifiedPartitionRefiner State Action Observation) →
  CompiledFutureQuotient compiler
compileFutureQuotient compiler
  with Ranked.rankedRefinementStabilizes
    (process compiler) (initialCode compiler)
... | Ranked.stabilizationWitness depth depth≤bound backwardStable =
  compiledFutureQuotient
    depth
    depth≤bound
    stableRelation
    (Bridge.stableRefinementExactlyCanonicalFuture stableRelation)
  where
    forwardBackward :
      forwardIterate compiler depth
      ≡ Ranked.iterate (process compiler) depth (initialCode compiler)
    forwardBackward = forwardEqualsBackwardIterate compiler depth

    forwardStableCode :
      forwardIterate compiler depth
      ≡ Ranked.advance (process compiler) (forwardIterate compiler depth)
    forwardStableCode =
      trans forwardBackward
        (trans backwardStable
          (cong (Ranked.advance (process compiler)) (sym forwardBackward)))

    stableRelation :
      Refinement.StableAt depth (observe compiler) (step compiler)
    stableRelation = stableAtFromCodeFixedPoint compiler depth forwardStableCode
