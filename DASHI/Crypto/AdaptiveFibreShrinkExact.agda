module DASHI.Crypto.AdaptiveFibreShrinkExact where

------------------------------------------------------------------------
-- ADAPTIVE FIBRE SHRINKAGE
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Empty using (⊥)

import DASHI.Crypto.ChosenCiphertextObservationRefinementExact as Obs

record StrictRefinementWitness
    (system : Obs.ObservationSystem) : Set where
  constructor strictRefinementWitness
  field
    beforeLeft beforeRight : Obs.Hidden system
    sample : Obs.ObservationSample system
    leftSurvives : Obs.CompatibleWithSample system beforeLeft sample
    rightRejected : Obs.CompatibleWithSample system beforeRight sample → ⊥

open StrictRefinementWitness public

strictRefinementFromSplit :
  ∀ {system : Obs.ObservationSystem} →
  Obs.ObservationSplitWitness system →
  StrictRefinementWitness system
strictRefinementFromSplit split = strictRefinementWitness
  (Obs.left split)
  (Obs.right split)
  (Obs.honestSample _ (Obs.left split) (Obs.distinguishingQuery split))
  refl
  (Obs.rightCandidateRejectedByLeftObservation split)

record EliminationStep (system : Obs.ObservationSystem) : Set where
  constructor eliminationStep
  field
    actual eliminated : Obs.Hidden system
    query : Obs.Query system
    actualSurvives :
      Obs.observe system actual query ≡ Obs.observe system actual query
    eliminatedDiffers :
      Obs.observe system eliminated query ≡ Obs.observe system actual query → ⊥

open EliminationStep public

------------------------------------------------------------------------
-- Repeated strict shrinkage is tracked independently from the hidden carrier's
-- finiteness proof.  Each count step witnesses removal of at least one live
-- candidate by the exact equation before = suc after.  A chain indexed by n
-- therefore contains n certified strict refinements.
------------------------------------------------------------------------

record StrictCountRefinement : Set where
  constructor strictCountRefinement
  field
    before after : Nat
    oneOrMoreRemoved : before ≡ suc after

open StrictCountRefinement public

data StrictShrinkChain : Nat → Set where
  emptyChain : StrictShrinkChain zero
  _then_ : ∀ {n} → StrictCountRefinement → StrictShrinkChain n → StrictShrinkChain (suc n)

------------------------------------------------------------------------
-- Exact two-candidate finite harness: one leaked bit shrinks 2 candidates to 1.
------------------------------------------------------------------------

data QueryOne : Set where ask : QueryOne

bitObservation : Obs.ObservationSystem
bitObservation = Obs.observationSystem Bool QueryOne Bool (λ hidden q → hidden)

bitSplit : Obs.ObservationSplitWitness bitObservation
bitSplit = Obs.observationSplitWitness false true ask different
  where
  different : false ≡ true → ⊥
  different ()

bitStrictRefinement : StrictRefinementWitness bitObservation
bitStrictRefinement = strictRefinementFromSplit bitSplit

beforeCandidateCount : Nat
beforeCandidateCount = 2

afterCandidateCount : Nat
afterCandidateCount = 1

oneSplitShrinksTwoToOne : beforeCandidateCount ≡ 2 * afterCandidateCount
oneSplitShrinksTwoToOne = refl

boolCountStrict : StrictCountRefinement
boolCountStrict = strictCountRefinement 2 1 refl

oneStepShrinkChain : StrictShrinkChain 1
oneStepShrinkChain = boolCountStrict then emptyChain

-- Two independent certified eliminations can be recorded as a two-step chain;
-- the chain type itself does not pretend the steps apply to the same finite
-- candidate population unless the caller also supplies that semantic bridge.
twoStepShrinkChain : StrictShrinkChain 2
twoStepShrinkChain = boolCountStrict then (boolCountStrict then emptyChain)
