{-# OPTIONS --safe #-}
module DASHI.Reasoning.LeechSharedCanonicalOrbitHistoryExact where

-- For a chosen family of E8-root-preserving chart operators, a single
-- canonical expert history is sufficient for reconstructing all E
-- expert-relative histories IF the forward/inverse actions are proven.
-- This theorem is generic: it does not identify a punctured-nine site
-- permutation with an E8 root action, nor assert whole neural semantics.
--
-- The companion executable Python E8 signed-coordinate actions and
-- JQ1 byte predictors implement one concrete candidate action family.
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Fin using (Fin)
open import Agda.Builtin.Equality using (_≡_; refl)

record InvertibleChart (State : Set) : Set where
  constructor invertibleChart
  field
    forward : State → State
    backward : State → State
    backwardForward : (s : State) →
      backward (forward s) ≡ s
    forwardBackward : (s : State) →
      forward (backward s) ≡ s
open InvertibleChart public

record CanonicalHistoryFamily (E : Nat) (State : Set) : Set where
  constructor canonicalHistoryFamily
  field
    canonical : State
    actions : Fin E → InvertibleChart State
open CanonicalHistoryFamily public

observedHistory :
  ∀ {E : Nat} {State : Set} →
  CanonicalHistoryFamily E State →
  Fin E → State
observedHistory family e =
  forward (actions family e) (canonical family)

recoverCanonical :
  ∀ {E : Nat} {State : Set} →
  CanonicalHistoryFamily E State →
  Fin E → State
recoverCanonical family e =
  backward (actions family e) (observedHistory family e)

everyExpertReopensSharedCanonical :
  ∀ {E : Nat} {State : Set} →
  (family : CanonicalHistoryFamily E State) →
  (e : Fin E) →
  recoverCanonical family e ≡ canonical family
everyExpertReopensSharedCanonical family e =
  backwardForward (actions family e) (canonical family)

crossExpertHistoryReconstruction :
  ∀ {E : Nat} {State : Set} →
  (family : CanonicalHistoryFamily E State) →
  (source target : Fin E) →
  forward (actions family target)
          (backward (actions family source)
                    (observedHistory family source))
    ≡ observedHistory family target
crossExpertHistoryReconstruction family source target
  rewrite backwardForward (actions family source)
                          (canonical family) = refl

-- The above theorem is NOT true for arbitrary independent histories:
-- see LeechPerExpertSymmetryDoesNotForceHistoryReuseExact.
-- A real distributed peer must additionally authenticate a coherent
-- model revision, the canonical-history revision and chosen action IDs.
-- A byte quotient preserving arbitrary consumer outputs requires
-- explicit consumer-fibre constancy or complete correction.
