module DASHI.Physics.Closure.NSTriadKNLuoFiniteKroneckerEnumerationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Classical finite-set/Kronecker-delta algebra; repository-original proof.
-- DOI: not applicable.
--
-- PURPOSE
-- Remove the free delta-action field from finite Fourier inversion. Given a
-- decidable point equality and a proof that a target occurs exactly once in a
-- finite point list, the Kronecker kernel satisfies
--
--   sum_y f(y) delta(y,x) = f(x).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym)
open import Relation.Nullary using (Dec; yes; no)

_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = left ≡ right → ⊥

data All {A : Set} (P : A → Set) : List A → Set where
  all[] : All P []
  all∷ :
    ∀ {item items} →
    P item → All P items → All P (item ∷ items)

data UniqueOccurrence {A : Set} (target : A) : List A → Set where
  occursHere :
    ∀ {items} →
    All (λ item → target ≢ item) items →
    UniqueOccurrence target (target ∷ items)
  occursThere :
    ∀ {item items} →
    target ≢ item →
    UniqueOccurrence target items →
    UniqueOccurrence target (item ∷ items)

kronecker :
  ∀ {A : Set} →
  ((left right : A) → Dec (left ≡ right)) →
  A → A → ℚ
kronecker decide left right with decide left right
... | yes _ = 1ℚ
... | no _ = 0ℚ

sumBy : ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumBy [] value = 0ℚ
sumBy (item ∷ items) value = value item + sumBy items value

kroneckerSelf :
  ∀ {A : Set}
    (decide : (left right : A) → Dec (left ≡ right))
    (value : A) →
  kronecker decide value value ≡ 1ℚ
kroneckerSelf decide value with decide value value
... | yes proof = refl
... | no contradiction = ⊥-elim (contradiction refl)

kroneckerDistinct :
  ∀ {A : Set}
    (decide : (left right : A) → Dec (left ≡ right))
    (left right : A) →
  left ≢ right →
  kronecker decide left right ≡ 0ℚ
kroneckerDistinct decide left right distinct with decide left right
... | yes proof = ⊥-elim (distinct proof)
... | no _ = refl

allKroneckerZero :
  ∀ {A : Set}
    (decide : (left right : A) → Dec (left ≡ right))
    (target : A)
    (items : List A) →
  All (λ item → target ≢ item) items →
  (value : A → ℚ) →
  sumBy items (λ item → value item * kronecker decide item target)
  ≡ 0ℚ
allKroneckerZero decide target [] all[] value = refl
allKroneckerZero decide target (item ∷ items)
  (all∷ targetNotItem restDistinct) value =
  let
    itemNotTarget : item ≢ target
    itemNotTarget equality = targetNotItem (sym equality)
  in
  rewrite kroneckerDistinct decide item target itemNotTarget
        | allKroneckerZero decide target items restDistinct value =
  solve (value item ∷ [])

kroneckerActsAsIdentity :
  ∀ {A : Set}
    (decide : (left right : A) → Dec (left ≡ right))
    (target : A)
    (items : List A) →
  UniqueOccurrence target items →
  (value : A → ℚ) →
  sumBy items (λ item → value item * kronecker decide item target)
  ≡ value target
kroneckerActsAsIdentity decide target .(target ∷ items)
  (occursHere {items} restDistinct) value
  rewrite kroneckerSelf decide target
        | allKroneckerZero decide target items restDistinct value =
  solve (value target ∷ [])
kroneckerActsAsIdentity decide target (item ∷ items)
  (occursThere targetNotItem occurrence) value =
  let
    itemNotTarget : item ≢ target
    itemNotTarget equality = targetNotItem (sym equality)
  in
  rewrite kroneckerDistinct decide item target itemNotTarget
        | kroneckerActsAsIdentity decide target items occurrence value =
  solve (value item ∷ value target ∷ [])
