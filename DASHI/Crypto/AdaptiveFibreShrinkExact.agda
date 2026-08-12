module DASHI.Crypto.AdaptiveFibreShrinkExact where

------------------------------------------------------------------------
-- ADAPTIVE FIBRE SHRINKAGE
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; _*_)
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
