{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact where

------------------------------------------------------------------------
-- R443/R445 P0: CONCRETE FINITE CODEC FOR THE ORIGINAL PERIODIC BONDS.
--
-- Reuses the canonical finite enumerations in BalabanPeriodicTorus4Carrier
-- and their duplicate-free proofs in BalabanFiniteEnumerationDistinctExact.
-- At EVERY actual periodic side L, the full original positive-bond
-- FUNCTION field is represented by a Vec of EXACTLY the enumerated bonds.
--
-- The decoder is defined, not a caller-supplied arbitrary field. We prove
-- Vec -> function -> Vec identity and function -> Vec -> function
-- pointwise identity. No unrestricted function extensionality is needed.
--
-- This is pure finite combinatorics: no compact Borel Haar measure,
-- metric/R124 source, RG estimate, continuum limit or Clay gap is claimed.
-- Mathematical provenance: Wilson; Balaban; previous DASHI owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Agda.Builtin.List as List
import Data.Vec.Base as Vec
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (_∈_)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanFiniteEnumerationDistinctExact as Unique

listLength : ∀ {A : Set} → List.List A → Nat
listLength List.[] = zero
listLength (List._∷_ x xs) = suc (listLength xs)

-- The already-computed original enumeration, with no new bond geometry.
originalPositiveBondFinite :
  (L : Nat) → Torus.FiniteEnumeration (Torus.PositiveBond L)
originalPositiveBondFinite L =
  Torus.productFinite
    (Torus.periodicTorus4Finite L)
    (Torus.cyclicIndexFinite Torus.four)

originalSiteDistinct :
  (L : Nat) →
  Unique.DuplicateFree
    (Torus.elements (Torus.periodicTorus4Finite L))
originalSiteDistinct L =
  Unique.cartesianDuplicateFree
    (Unique.cartesianDuplicateFree
      (Unique.allCyclicIndicesDuplicateFree L)
      (Unique.allCyclicIndicesDuplicateFree L))
    (Unique.cartesianDuplicateFree
      (Unique.allCyclicIndicesDuplicateFree L)
      (Unique.allCyclicIndicesDuplicateFree L))

originalPositiveBondDistinct :
  (L : Nat) →
  Unique.DuplicateFree
    (Torus.elements (originalPositiveBondFinite L))
originalPositiveBondDistinct L =
  Unique.cartesianDuplicateFree
    (originalSiteDistinct L)
    (Unique.allCyclicIndicesDuplicateFree Torus.four)

originalPositiveBondCount : Nat → Nat
originalPositiveBondCount L =
  listLength (Torus.elements (originalPositiveBondFinite L))

-- The side-four selected physical source uses 256 sites x 4 positive axes.
-- This is definitional enumeration cardinality, not a free linkCount field.
originalSideFourCountIs1024 :
  originalPositiveBondCount Torus.four ≡ 1024
originalSideFourCountIs1024 = refl

listValues :
  ∀ {A B : Set} (xs : List.List A) →
  (A → B) → Vec.Vec B (listLength xs)
listValues List.[] f = Vec.[]
listValues (List._∷_ x xs) f =
  Vec._∷_ (f x) (listValues xs f)

-- Canonical list-membership position lookup, without an equality oracle.
memberValue :
  ∀ {A B : Set} {x : A} {xs : List.List A} →
  x ∈ xs → Vec.Vec B (listLength xs) → B
memberValue Torus.here (Vec._∷_ head tail) = head
memberValue (Torus.there inTail) (Vec._∷_ head tail) =
  memberValue inTail tail

memberValueOfListValues :
  ∀ {A B : Set} {x : A} {xs : List.List A}
    (f : A → B) (membership : x ∈ xs) →
  memberValue membership (listValues xs f) ≡ f x
memberValueOfListValues f Torus.here = refl
memberValueOfListValues f (Torus.there inTail) =
  memberValueOfListValues f inTail

-- Every position has an original bond label, and a membership certificate.
listAt :
  ∀ {A : Set} (xs : List.List A) →
  Fin (listLength xs) → A
listAt (List._∷_ x xs) fzero = x
listAt (List._∷_ x xs) (fsuc index) = listAt xs index

listAtMember :
  ∀ {A : Set} (xs : List.List A)
    (index : Fin (listLength xs)) →
  listAt xs index ∈ xs
listAtMember (List._∷_ x xs) fzero = Torus.here
listAtMember (List._∷_ x xs) (fsuc index) =
  Torus.there (listAtMember xs index)

listAtMemberValue :
  ∀ {A B : Set} (xs : List.List A)
    (index : Fin (listLength xs))
    (values : Vec.Vec B (listLength xs)) →
  memberValue (listAtMember xs index) values
  ≡ Vec.lookup values index
listAtMemberValue (List._∷_ x xs) fzero
    (Vec._∷_ head tail) = refl
listAtMemberValue (List._∷_ x xs) (fsuc index)
    (Vec._∷_ head tail) =
  listAtMemberValue xs index tail

listValuesAt :
  ∀ {A B : Set} (xs : List.List A)
    (f : A → B) (index : Fin (listLength xs)) →
  Vec.lookup (listValues xs f) index ≡ f (listAt xs index)
listValuesAt (List._∷_ x xs) f fzero = refl
listValuesAt (List._∷_ x xs) f (fsuc index) =
  listValuesAt xs f index

-- Duplicate freeness is exactly what prevents a lookup from selecting
-- the wrong occurrence of a repeated bond label.
membershipUnique :
  ∀ {A : Set} {x : A} {xs : List.List A}
    (distinct : Unique.DuplicateFree xs)
    (left right : x ∈ xs) →
  left ≡ right
membershipUnique Unique.[]-free () ()
membershipUnique (Unique._∷-free_ absent rest) Torus.here Torus.here = refl
membershipUnique (Unique._∷-free_ absent rest)
    Torus.here (Torus.there later) =
  ⊥-elim (absent later)
membershipUnique (Unique._∷-free_ absent rest)
    (Torus.there earlier) Torus.here =
  ⊥-elim (absent earlier)
membershipUnique (Unique._∷-free_ absent rest)
    (Torus.there earlier) (Torus.there later) =
  cong Torus.there (membershipUnique rest earlier later)

vecPointwiseEquality :
  ∀ {B : Set} {n : Nat}
    {left right : Vec.Vec B n} →
  (∀ index → Vec.lookup left index ≡ Vec.lookup right index) →
  left ≡ right
vecPointwiseEquality {left = Vec.[]} {right = Vec.[]} equalAt = refl
vecPointwiseEquality
    {left = Vec._∷_ leftHead leftTail}
    {right = Vec._∷_ rightHead rightTail}
    equalAt
  with equalAt fzero
... | refl =
  cong (Vec._∷_ leftHead)
    (vecPointwiseEquality (λ index → equalAt (fsuc index)))

-- Generic proved finite-enumeration codec. Inhabiting an enumeration and
-- duplicate-free certificate is enough; no arbitrary encode/decode laws.
encodeField :
  ∀ {A B : Set}
    (finite : Torus.FiniteEnumeration A) →
  (A → B) →
  Vec.Vec B (listLength (Torus.elements finite))
encodeField finite field = listValues (Torus.elements finite) field

decodeField :
  ∀ {A B : Set}
    (finite : Torus.FiniteEnumeration A) →
  Vec.Vec B (listLength (Torus.elements finite)) →
  A → B
decodeField finite vector label =
  memberValue (Torus.complete finite label) vector

decodeEncodeAt :
  ∀ {A B : Set}
    (finite : Torus.FiniteEnumeration A)
    (field : A → B) label →
  decodeField finite (encodeField finite field) label
  ≡ field label
decodeEncodeAt finite field label =
  memberValueOfListValues field (Torus.complete finite label)

encodeDecodeExactly :
  ∀ {A B : Set}
    (finite : Torus.FiniteEnumeration A)
    (distinct : Unique.DuplicateFree (Torus.elements finite))
    (vector : Vec.Vec B (listLength (Torus.elements finite))) →
  encodeField finite (decodeField finite vector) ≡ vector
encodeDecodeExactly finite distinct vector =
  vecPointwiseEquality (λ index →
    trans
      (listValuesAt (Torus.elements finite)
        (decodeField finite vector) index)
      (trans
        (cong (λ membership → memberValue membership vector)
          (membershipUnique distinct
            (Torus.complete finite
              (listAt (Torus.elements finite) index))
            (listAtMember (Torus.elements finite) index)))
        (listAtMemberValue (Torus.elements finite) index vector)))

-- Instantiation: SAME original periodic function carrier at every cutoff.
encodeOriginalBonds :
  ∀ {B : Set} (L : Nat) →
  Torus.BondField L B → Vec.Vec B (originalPositiveBondCount L)
encodeOriginalBonds L = encodeField (originalPositiveBondFinite L)

decodeOriginalBonds :
  ∀ {B : Set} (L : Nat) →
  Vec.Vec B (originalPositiveBondCount L) → Torus.BondField L B
decodeOriginalBonds L = decodeField (originalPositiveBondFinite L)

originalBondsDecodeEncodeAt :
  ∀ {B : Set} (L : Nat) (field : Torus.BondField L B) bond →
  decodeOriginalBonds L (encodeOriginalBonds L field) bond ≡ field bond
originalBondsDecodeEncodeAt L =
  decodeEncodeAt (originalPositiveBondFinite L)

originalBondsEncodeDecodeExactly :
  ∀ {B : Set} (L : Nat)
    (vector : Vec.Vec B (originalPositiveBondCount L)) →
  encodeOriginalBonds L (decodeOriginalBonds L vector) ≡ vector
originalBondsEncodeDecodeExactly L =
  encodeDecodeExactly
    (originalPositiveBondFinite L)
    (originalPositiveBondDistinct L)
