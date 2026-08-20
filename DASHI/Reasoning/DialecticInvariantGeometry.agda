module DASHI.Reasoning.DialecticInvariantGeometry where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Predicate geometry: thesis, antithesis, common invariant
------------------------------------------------------------------------

Predicate : Set → Set
Predicate X = X → Bool

_∧_ : Bool → Bool → Bool
true ∧ b = b
false ∧ _ = false

_∨_ : Bool → Bool → Bool
true ∨ _ = true
false ∨ b = b

¬_ : Bool → Bool
¬ true = false
¬ false = true

_∩_ : ∀ {X} → Predicate X → Predicate X → Predicate X
(A ∩ B) x = A x ∧ B x

_∪_ : ∀ {X} → Predicate X → Predicate X → Predicate X
(A ∪ B) x = A x ∨ B x

complement : ∀ {X} → Predicate X → Predicate X
complement A x = ¬ A x

∧-comm : ∀ a b → a ∧ b ≡ b ∧ a
∧-comm true true = refl
∧-comm true false = refl
∧-comm false true = refl
∧-comm false false = refl

∩-comm : ∀ {X} (A B : Predicate X) (x : X) → (A ∩ B) x ≡ (B ∩ A) x
∩-comm A B x = ∧-comm (A x) (B x)

------------------------------------------------------------------------
-- Stance involution
------------------------------------------------------------------------

data Stance : Set where
  thesisSide antithesisSide : Stance

mirrorStance : Stance → Stance
mirrorStance thesisSide = antithesisSide
mirrorStance antithesisSide = thesisSide

mirrorStance²-id : ∀ s → mirrorStance (mirrorStance s) ≡ s
mirrorStance²-id thesisSide = refl
mirrorStance²-id antithesisSide = refl

record DialecticField (X : Set) : Set where
  constructor dialecticField
  field
    observe : Stance → Predicate X

open DialecticField public

thesis : ∀ {X} → DialecticField X → Predicate X
thesis F = observe F thesisSide

antithesis : ∀ {X} → DialecticField X → Predicate X
antithesis F = observe F antithesisSide

common : ∀ {X} → DialecticField X → Predicate X
common F = thesis F ∩ antithesis F

swap : ∀ {X} → DialecticField X → DialecticField X
observe (swap F) s = observe F (mirrorStance s)

common-swap-invariant :
  ∀ {X} (F : DialecticField X) (x : X) →
  common (swap F) x ≡ common F x
common-swap-invariant F x = ∧-comm (antithesis F x) (thesis F x)

------------------------------------------------------------------------
-- Traversable corridors and boundary semantics
------------------------------------------------------------------------

corridor : ∀ {X} → DialecticField X → Predicate X
corridor F x = (thesis F x ∨ antithesis F x) ∧ ¬ common F x

disagreement : ∀ {X} → DialecticField X → Predicate X
disagreement F x =
  (thesis F x ∧ ¬ antithesis F x) ∨
  (antithesis F x ∧ ¬ thesis F x)

corridor-is-disagreement :
  ∀ {X} (F : DialecticField X) (x : X) →
  corridor F x ≡ disagreement F x
corridor-is-disagreement F x with thesis F x | antithesis F x
... | true | true = refl
... | true | false = refl
... | false | true = refl
... | false | false = refl

------------------------------------------------------------------------
-- Projection is not intersection: preserve both operators explicitly
------------------------------------------------------------------------

record ProjectionAlgebra (X : Set) : Set₁ where
  constructor projectionAlgebra
  field
    project : DialecticField X → Predicate X
    common-implies-projected :
      ∀ (F : DialecticField X) (x : X) →
      common F x ≡ true → project F x ≡ true

record SoftOverlap (X Score : Set) : Set₁ where
  constructor softOverlap
  field
    score : DialecticField X → X → Score
    threshold : Score → Bool
    realizes-common :
      ∀ (F : DialecticField X) (x : X) →
      threshold (score F x) ≡ common F x
    swap-invariant :
      ∀ (F : DialecticField X) (x : X) →
      score (swap F) x ≡ score F x

------------------------------------------------------------------------
-- Quantization bridge into the nine-state motif supervisor
------------------------------------------------------------------------

import DASHI.Algebra.Trit as T
import DASHI.Reasoning.DialecticMotifKernel as M

record TernaryQuantizer (X : Set) : Set₁ where
  constructor ternaryQuantizer
  field
    quantize : Predicate X → T.Trit

record DialecticToMotif (X : Set) : Set₁ where
  constructor dialecticToMotif
  field
    dialectic : DialecticField X
    quantizer : TernaryQuantizer X
    pastField nowField futureField : DialecticField X

open TernaryQuantizer public
open DialecticToMotif public

stateOf : ∀ {X} → DialecticToMotif X → M.State9
stateOf B =
  M.state9
    (quantize (quantizer B) (thesis (pastField B)))
    (quantize (quantizer B) (thesis (nowField B)))
    (quantize (quantizer B) (thesis (futureField B)))
    (quantize (quantizer B) (common (pastField B)))
    (quantize (quantizer B) (common (nowField B)))
    (quantize (quantizer B) (common (futureField B)))
    (quantize (quantizer B) (antithesis (pastField B)))
    (quantize (quantizer B) (antithesis (nowField B)))
    (quantize (quantizer B) (antithesis (futureField B)))

motifOf : ∀ {X} → M.Overflow → DialecticToMotif X → M.Motif
motifOf overflow B = M.supervise overflow (stateOf B)
