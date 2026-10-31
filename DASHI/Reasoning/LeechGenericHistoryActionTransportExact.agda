{-# OPTIONS --safe #-}
module DASHI.Reasoning.LeechGenericHistoryActionTransportExact where

-- A concrete arbitrary-E pointwise state-update commuting square.
-- This closes a genuine missing part of weighted mixture action transport:
-- unselected histories must also be transported correctly.
-- It consumes the canonical generic selected-only updater.
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Fin using (Fin)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Reasoning.LeechGenericTopKActionTransportExact as M

-- The action on expert IDs is explicit. A proof of bijectivity and
-- TopK permutation identity remains needed for actual learned top-k.
pointwiseHistoryCommutation :
  ∀ {E : Nat} {H : Set}
  (p : Fin E → Fin E)
  (selected selected' : Fin E → Bool)
  (old old' : Fin E → H)
  (advance advance' : Fin E → H → H) →
  ((e : Fin E) → selected' (p e) ≡ selected e) →
  ((e : Fin E) → old' (p e) ≡ old e) →
  ((e : Fin E) →
    advance' (p e) (old' (p e)) ≡ advance e (old e)) →
  (e : Fin E) →
  M.updateHistory selected' old' advance' (p e)
    ≡ M.updateHistory selected old advance e
pointwiseHistoryCommutation p selected selected' old old' advance advance'
  selectedCompatible oldCompatible advanceCompatible e
  rewrite selectedCompatible e with selected e
... | true = advanceCompatible e
... | false = oldCompatible e

-- This theorem is independent of response polarity and independently
-- excludes the assumption that argument opposition chooses a sign.
-- Joint output+history commutation requires this theorem AND
-- M.transportPreservesWeightedMixture with their respective hypotheses.
