module DASHI.Analysis.NonArchimedeanFiniteUniformHittingBlockCompilerExact where

------------------------------------------------------------------------
-- FINITE UNIFORM HITTING-BLOCK COMPILER
--
-- Directed reachability gives one finite forward word from every state to a
-- fixed target.  On an exhaustively enumerated finite carrier, take the maximum
-- chosen word length.  This produces one uniform finite hitting-block length.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_≤_)
open import Data.Product using (Σ; _,_; proj₁)

import DASHI.Analysis.NonArchimedeanForwardTranslationIrreducibilityCompilerExact as Forward
import DASHI.Core.FiniteWitnessMaximumExact as FiniteMax

wordLength :
  {data : Forward.ForwardTranslationData} →
  Forward.ForwardWord data → Nat
wordLength Forward.done = zero
wordLength (Forward.useA word) = suc (wordLength word)
wordLength (Forward.useB word) = suc (wordLength word)

record FiniteForwardStateEnumeration
  (data : Forward.ForwardTranslationData) : Set where
  field
    states : List (Forward.State data)
    exhaustive : (state : Forward.State data) → state ∈ states

open FiniteForwardStateEnumeration public

ChosenHit :
  (data : Forward.ForwardTranslationData) →
  Forward.DirectedForwardReachability data →
  Forward.State data →
  Forward.State data →
  Set
ChosenHit data reach target state =
  Σ (Forward.ForwardWord data)
    (λ word → Forward.run data word state ≡ target)

chosenHit :
  (data : Forward.ForwardTranslationData) →
  (reach : Forward.DirectedForwardReachability data) →
  (target state : Forward.State data) →
  ChosenHit data reach target state
chosenHit data reach target state =
  Forward.reaches reach state target

chosenHitCost :
  (data : Forward.ForwardTranslationData) →
  (reach : Forward.DirectedForwardReachability data) →
  (target : Forward.State data) →
  Forward.State data → Nat
chosenHitCost data reach target state =
  wordLength (proj₁ (chosenHit data reach target state))

hittingAtlas :
  (data : Forward.ForwardTranslationData) →
  (reach : Forward.DirectedForwardReachability data) →
  FiniteForwardStateEnumeration data →
  (target : Forward.State data) →
  FiniteMax.FiniteWitnessAtlas
hittingAtlas data reach enumeration target = record
  { State = Forward.State data
  ; Witness = ChosenHit data reach target
  ; states = states enumeration
  ; exhaustive = exhaustive enumeration
  ; witness = chosenHit data reach target
  ; cost = chosenHitCost data reach target
  }

record UniformHittingBlock
  (data : Forward.ForwardTranslationData)
  (reach : Forward.DirectedForwardReachability data)
  (target : Forward.State data) : Set where
  field
    blockLength : Nat
    chosenWordLengthBound :
      (state : Forward.State data) →
      chosenHitCost data reach target state ≤ blockLength

open UniformHittingBlock public

compileUniformHittingBlock :
  (data : Forward.ForwardTranslationData) →
  (reach : Forward.DirectedForwardReachability data) →
  (enumeration : FiniteForwardStateEnumeration data) →
  (target : Forward.State data) →
  UniformHittingBlock data reach target
compileUniformHittingBlock data reach enumeration target =
  let
    atlas = hittingAtlas data reach enumeration target
    uniform = FiniteMax.compileUniformWitnessBound atlas
  in
  record
    { blockLength = FiniteMax.UniformWitnessBound.bound uniform
    ; chosenWordLengthBound =
        FiniteMax.UniformWitnessBound.bounds uniform
    }
