{-# OPTIONS --safe #-}
module DASHI.Reasoning.LeechParityC3ActionKernelExact where

-- Concrete C2 chart action, independent C3 cyclic trialectic rotation,
-- and exact shared-expert conjugation. Source ownership:
-- LeechSignedHistoryExpertBidiExact; the trialectic/369 and finite
-- wave/phase hierarchy are *separate* existing owners.
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Reasoning.LeechSignedHistoryExpertBidiExact as S

data Chart : Set where
  direct inverse fixed : Chart

flipChart : Chart → Chart
flipChart direct = inverse
flipChart inverse = direct
flipChart fixed = fixed

flipTwice : (s : Chart) → flipChart (flipChart s) ≡ s
flipTwice direct = refl
flipTwice inverse = refl
flipTwice fixed = refl

centre : S.HistoryState
centre = S.historyState S.centre S.centre

-- The fixed chart maps to the group-action fixed point, so a zero
-- orientation is not spuriously marked positive or negative.
signedExpert : (S.HistoryState → S.HistoryState) →
               Chart → S.HistoryState → S.HistoryState
signedExpert F direct z = F z
signedExpert F inverse z = S.invertHistory (F (S.invertHistory z))
signedExpert F fixed z = centre

-- The mathematical C2 prior: a chosen chart must reverse when
-- activation AND expert memory are inverted. A neural orientation
-- scorer needs a signed tie-break for nonzero zero-score states.
signedExpertInversion :
  (F : S.HistoryState → S.HistoryState)
  (choose : S.HistoryState → Chart) →
  ((z : S.HistoryState) →
     choose (S.invertHistory z) ≡ flipChart (choose z)) →
  (z : S.HistoryState) →
  signedExpert F (choose (S.invertHistory z)) (S.invertHistory z)
    ≡ S.invertHistory (signedExpert F (choose z) z)
signedExpertInversion F choose lawful z
  rewrite lawful z with choose z
... | direct rewrite S.invertHistoryInvolutive z = refl
... | inverse
  rewrite S.invertHistoryInvolutive (F (S.invertHistory z)) = refl
... | fixed = refl

record TrialecticTriple : Set where
  constructor triple
  field
    a b c : S.HistoryState
open TrialecticTriple public

cycle3 : TrialecticTriple → TrialecticTriple
cycle3 (triple a b c) = triple b c a

invertTriple : TrialecticTriple → TrialecticTriple
invertTriple (triple a b c) =
  triple (S.invertHistory a) (S.invertHistory b) (S.invertHistory c)

threeCyclesReturn :
  (t : TrialecticTriple) →
  cycle3 (cycle3 (cycle3 t)) ≡ t
threeCyclesReturn (triple a b c) = refl

inversionCommutesWithCyclicAction :
  (t : TrialecticTriple) →
  invertTriple (cycle3 t) ≡ cycle3 (invertTriple t)
inversionCommutesWithCyclicAction (triple a b c) = refl

-- A cyclic action is NOT C2 inversion; neither denotes logical
-- negation, argumentative objection, good/evil or semantic face.
-- The latter needs independently supplied source/consumer evidence.
