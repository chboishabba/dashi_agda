module DASHI.Physics.Closure.NSTriadKNLuoFiniteFinEnumerationExact where

------------------------------------------------------------------------
-- PURPOSE
-- Construct the exact growing finite enumeration needed by a cyclic Galerkin
-- carrier. For every n and every i : Fin n, i occurs exactly once in the
-- recursively enumerated list of all Fin n values. A decidable equality is
-- provided on the same carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Agda.Builtin.Nat as ℕ
open import Data.Empty using (⊥)
import Data.Fin.Base as Fin
open Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (cong)
open import Relation.Nullary using (Dec; yes; no)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteKroneckerEnumerationExact as Delta

_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = left ≡ right → ⊥

map :
  ∀ {A B : Set} →
  (A → B) → List A → List B
map transform [] = []
map transform (item ∷ items) =
  transform item ∷ map transform items

enumerateFin : (n : Nat) → List (Fin n)
enumerateFin ℕ.zero = []
enumerateFin (ℕ.suc n) =
  Fin.zero ∷ map Fin.suc (enumerateFin n)

sucInjective :
  ∀ {n : Nat} {left right : Fin n} →
  Fin.suc left ≡ Fin.suc right → left ≡ right
sucInjective refl = refl

zeroNotSuc :
  ∀ {n : Nat} (value : Fin n) →
  (Fin.zero {n}) ≢ Fin.suc value
zeroNotSuc value ()

sucNotZero :
  ∀ {n : Nat} (value : Fin n) →
  Fin.suc value ≢ (Fin.zero {n})
sucNotZero value ()

mapAll :
  ∀ {A B : Set}
    {P : A → Set}
    {Q : B → Set}
    (transform : A → B) →
  ((item : A) → P item → Q (transform item)) →
  (items : List A) →
  Delta.All P items →
  Delta.All Q (map transform items)
mapAll transform transfer [] Delta.all[] = Delta.all[]
mapAll transform transfer (item ∷ items)
  (Delta.all∷ itemProof restProof) =
  Delta.all∷
    (transfer item itemProof)
    (mapAll transform transfer items restProof)

allMappedSucNotZero :
  ∀ {n : Nat} (items : List (Fin n)) →
  Delta.All
    (λ value → (Fin.zero {n}) ≢ Fin.suc value)
    items
allMappedSucNotZero [] = Delta.all[]
allMappedSucNotZero (item ∷ items) =
  Delta.all∷
    (zeroNotSuc item)
    (allMappedSucNotZero items)

allSucImagesNotZero :
  ∀ {n : Nat} (items : List (Fin n)) →
  Delta.All
    (λ image → (Fin.zero {n}) ≢ image)
    (map Fin.suc items)
allSucImagesNotZero items =
  mapAll
    Fin.suc
    (λ item proof → proof)
    items
    (allMappedSucNotZero items)

mapUniqueSuc :
  ∀ {n : Nat}
    (target : Fin n)
    (items : List (Fin n)) →
  Delta.UniqueOccurrence target items →
  Delta.UniqueOccurrence (Fin.suc target) (map Fin.suc items)
mapUniqueSuc target .(target ∷ items)
  (Delta.occursHere {items} restDistinct) =
  Delta.occursHere
    (mapAll
      Fin.suc
      (λ item targetNotItem equality →
        targetNotItem (sucInjective equality))
      items
      restDistinct)
mapUniqueSuc target (item ∷ items)
  (Delta.occursThere targetNotItem occurrence) =
  Delta.occursThere
    (λ equality → targetNotItem (sucInjective equality))
    (mapUniqueSuc target items occurrence)

finOccursExactlyOnce :
  ∀ {n : Nat} (value : Fin n) →
  Delta.UniqueOccurrence value (enumerateFin n)
finOccursExactlyOnce {ℕ.zero} ()
finOccursExactlyOnce {ℕ.suc n} Fin.zero =
  Delta.occursHere
    (allSucImagesNotZero (enumerateFin n))
finOccursExactlyOnce {ℕ.suc n} (Fin.suc value) =
  Delta.occursThere
    (sucNotZero value)
    (mapUniqueSuc value (enumerateFin n)
      (finOccursExactlyOnce value))

finDecidableEquality :
  ∀ {n : Nat} (left right : Fin n) →
  Dec (left ≡ right)
finDecidableEquality {ℕ.suc n} Fin.zero Fin.zero = yes refl
finDecidableEquality {ℕ.suc n} Fin.zero (Fin.suc right) =
  no (zeroNotSuc right)
finDecidableEquality {ℕ.suc n} (Fin.suc left) Fin.zero =
  no (sucNotZero left)
finDecidableEquality {ℕ.suc n} (Fin.suc left) (Fin.suc right)
  with finDecidableEquality left right
... | yes equality = yes (cong Fin.suc equality)
... | no distinct = no (λ equality → distinct (sucInjective equality))
