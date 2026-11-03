{-# OPTIONS --safe #-}
module DASHI.Reasoning.LeechOddOnlyApproximationObstructionExact where

------------------------------------------------------------------------
-- F02a: exact algebraic odd-only approximation no-go.
--
-- Reuse the signed HISTORY inversion already owned by
-- DASHI.Reasoning.LeechSignedHistoryExpertBidiExact.
-- The same orientation must act on activation AND retained memory.
-- This result is deliberately independent of a metric, PyTorch,
-- real GELU, inner products, E8 / Leech group actions, and ethics.
--
-- It says: if a target function is not odd at a particular historical
-- state, an odd student cannot equal the target at BOTH that state and
-- its mirrored historical state.
--
-- The stronger real-inner-product pairwise MSE lower bound
-- (the even-component squared norm) is a DIFFERENT theorem, F02b.
-- It needs an explicit norm / half-scalar and parallelogram laws.
-- Do not claim F02b is established by this finite theorem.
--
-- Original neural model Leech-LILA: Anatolii Kornienko
-- DOI 10.5281/zenodo.18784424.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Reasoning.LeechSignedHistoryExpertBidiExact as History

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

cong : ∀ {A B : Set} (f : A → B) {x y : A} →
       x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} →
        x ≡ y → y ≡ z → x ≡ z
trans refl right = right

-- No involution assumptions are needed for the local contradiction:
-- the proof only uses the student's oddness at the given state.
oddCannotMatchNonOddPair :
  ∀ {Domain Output : Set}
    (mirror : Domain → Domain)
    (negative : Output → Output)
    (target student : Domain → Output)
    (state : Domain) →
  ((z : Domain) →
    student (mirror z) ≡ negative (student z)) →
  ¬ (target (mirror state) ≡ negative (target state)) →
  student state ≡ target state →
  student (mirror state) ≡ target (mirror state) →
  ⊥
oddCannotMatchNonOddPair mirror negative target student state
                          oddLaw targetNotOdd equalHere equalMirror =
  targetNotOdd
    (trans (sym equalMirror)
      (trans (oddLaw state)
        (cong negative equalHere)))

-- Concrete SAME-SOURCE historical involution; avoids importing a new
-- trit or making up a new "semantic opposite" carrier.
historyOddCannotMatchNonOddPair :
  ∀ {Output : Set}
    (negative : Output → Output)
    (target student : History.HistoryState → Output)
    (state : History.HistoryState) →
  ((z : History.HistoryState) →
    student (History.invertHistory z) ≡ negative (student z)) →
  ¬ (target (History.invertHistory state) ≡ negative (target state)) →
  student state ≡ target state →
  student (History.invertHistory state)
    ≡ target (History.invertHistory state) →
  ⊥
historyOddCannotMatchNonOddPair negative target student state =
  oddCannotMatchNonOddPair History.invertHistory
                            negative target student state

-- This is a restriction on exact odd-only fitting. The executable
-- learner has a separately trained EVEN channel, so it does not
-- automatically satisfy the premise "student is odd". A trained
-- EVEN + ODD model may still have huge CE for unrelated reasons.
