module DASHI.Mathematics.NumberTheory.PartitionErdosKMajorFactorCoordinateUniqueExact where

------------------------------------------------------------------------
-- DUPLICATE-FREEDOM OF THE K-MAJOR FACTOR SCAN
--
-- Uniqueness is structural.  Within one k-block, equality of outputs recovers
-- equality of the divisor candidate.  Across blocks, equality of outputs
-- recovers equality of the outer copies coordinate.  Thus no equality of
-- order-proof fields is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Empty using (⊥)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any as Any using ()
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; sym; trans)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteDependentPairEnumerationExact as Dep
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as OneTo
import DASHI.Mathematics.NumberTheory.PartitionErdosKMajorFactorCoordinateExact as KMajor

coordinatesForCopiesDivisorMember :
  (n copies : Nat) →
  (copiesPositive : suc zero ≤ copies) →
  (copiesBound : copies ≤ n) →
  (divisors : List Nat) →
  (bounds : All.All (λ v → (suc zero ≤ v) × (v ≤ n)) divisors) →
  ∀ {coordinate : KMajor.KMajorFactorCoordinate n} →
  coordinate ∈
    KMajor.coordinatesForCopies
      n copies copiesPositive copiesBound divisors bounds →
  KMajor.divisor coordinate ∈ divisors
coordinatesForCopiesDivisorMember
    n copies copiesPositive copiesBound [] All.[] ()
coordinatesForCopiesDivisorMember
    n copies copiesPositive copiesBound
    (candidate ∷ divisors) (All._∷_ candidateBounds rest) member
  with (copies * candidate) NatP.≤? n
... | no _ =
  Any.there
    (coordinatesForCopiesDivisorMember
      n copies copiesPositive copiesBound divisors rest member)
... | yes productBound with member
...   | Any.here equality = Any.here (cong KMajor.divisor equality)
...   | Any.there tailMember =
  Any.there
    (coordinatesForCopiesDivisorMember
      n copies copiesPositive copiesBound divisors rest tailMember)

coordinatesForCopiesCopies :
  (n copies : Nat) →
  (copiesPositive : suc zero ≤ copies) →
  (copiesBound : copies ≤ n) →
  (divisors : List Nat) →
  (bounds : All.All (λ v → (suc zero ≤ v) × (v ≤ n)) divisors) →
  ∀ {coordinate : KMajor.KMajorFactorCoordinate n} →
  coordinate ∈
    KMajor.coordinatesForCopies
      n copies copiesPositive copiesBound divisors bounds →
  KMajor.copies coordinate ≡ copies
coordinatesForCopiesCopies
    n copies copiesPositive copiesBound [] All.[] ()
coordinatesForCopiesCopies
    n copies copiesPositive copiesBound
    (candidate ∷ divisors) (All._∷_ candidateBounds rest) member
  with (copies * candidate) NatP.≤? n
... | no _ =
  coordinatesForCopiesCopies
    n copies copiesPositive copiesBound divisors rest member
... | yes productBound with member
...   | Any.here equality = cong KMajor.copies equality
...   | Any.there tailMember =
  coordinatesForCopiesCopies
    n copies copiesPositive copiesBound divisors rest tailMember

coordinatesForCopiesUnique :
  (n copies : Nat) →
  (copiesPositive : suc zero ≤ copies) →
  (copiesBound : copies ≤ n) →
  (divisors : List Nat) →
  (bounds : All.All (λ v → (suc zero ≤ v) × (v ≤ n)) divisors) →
  Unique divisors →
  Unique
    (KMajor.coordinatesForCopies
      n copies copiesPositive copiesBound divisors bounds)
coordinatesForCopiesUnique
    n copies copiesPositive copiesBound [] All.[] AllPairs.[] = AllPairs.[]
coordinatesForCopiesUnique
    n copies copiesPositive copiesBound
    (candidate ∷ divisors) (All._∷_ candidateBounds rest)
    (AllPairs._∷_ fresh tailUnique)
  with (copies * candidate) NatP.≤? n
... | no _ =
  coordinatesForCopiesUnique
    n copies copiesPositive copiesBound divisors rest tailUnique
... | yes productBound =
  AllPairs._∷_
    headFresh
    (coordinatesForCopiesUnique
      n copies copiesPositive copiesBound divisors rest tailUnique)
  where
  head : KMajor.KMajorFactorCoordinate n
  head =
    KMajor.kMajorFactorCoordinate
      copies candidate copiesPositive copiesBound
      (proj₁ candidateBounds) (proj₂ candidateBounds) productBound

  headFresh :
    All.All
      (λ coordinate → head ≢ coordinate)
      (KMajor.coordinatesForCopies
        n copies copiesPositive copiesBound divisors rest)
  headFresh =
    All.tabulate λ member equality →
      All.lookup fresh
        (coordinatesForCopiesDivisorMember
          n copies copiesPositive copiesBound divisors rest member)
        (cong KMajor.divisor equality)

kMajorFactorCoordinatesFromCopiesMember :
  (n : Nat) →
  (copiesList : List Nat) →
  (bounds : All.All (λ k → (suc zero ≤ k) × (k ≤ n)) copiesList) →
  ∀ {coordinate : KMajor.KMajorFactorCoordinate n} →
  coordinate ∈ KMajor.kMajorFactorCoordinatesFrom n copiesList bounds →
  KMajor.copies coordinate ∈ copiesList
kMajorFactorCoordinatesFromCopiesMember n [] All.[] ()
kMajorFactorCoordinatesFromCopiesMember
    n (candidate ∷ restCopies) (All._∷_ candidateBounds restBounds) member
  with ∈-++⁻
    (KMajor.coordinatesForCopies
      n candidate
      (proj₁ candidateBounds) (proj₂ candidateBounds)
      (Hecke.oneTo n) (OneTo.oneToAllBounds n))
    member
... | inj₁ blockMember =
  Any.here
    (coordinatesForCopiesCopies
      n candidate
      (proj₁ candidateBounds) (proj₂ candidateBounds)
      (Hecke.oneTo n) (OneTo.oneToAllBounds n)
      blockMember)
... | inj₂ tailMember =
  Any.there
    (kMajorFactorCoordinatesFromCopiesMember
      n restCopies restBounds tailMember)

kMajorFactorCoordinatesFromUnique :
  (n : Nat) →
  (copiesList : List Nat) →
  (bounds : All.All (λ k → (suc zero ≤ k) × (k ≤ n)) copiesList) →
  Unique copiesList →
  Unique (KMajor.kMajorFactorCoordinatesFrom n copiesList bounds)
kMajorFactorCoordinatesFromUnique n [] All.[] AllPairs.[] = AllPairs.[]
kMajorFactorCoordinatesFromUnique
    n (candidate ∷ restCopies) (All._∷_ candidateBounds restBounds)
    (AllPairs._∷_ fresh tailUnique) =
  Dep.uniqueAppendDisjoint
    blockUnique
    (kMajorFactorCoordinatesFromUnique n restCopies restBounds tailUnique)
    cross
  where
  block : List (KMajor.KMajorFactorCoordinate n)
  block =
    KMajor.coordinatesForCopies
      n candidate
      (proj₁ candidateBounds) (proj₂ candidateBounds)
      (Hecke.oneTo n) (OneTo.oneToAllBounds n)

  blockUnique : Unique block
  blockUnique =
    coordinatesForCopiesUnique
      n candidate
      (proj₁ candidateBounds) (proj₂ candidateBounds)
      (Hecke.oneTo n) (OneTo.oneToAllBounds n)
      (OneTo.oneToUnique n)

  cross :
    ∀ {left right} →
    left ∈ block →
    right ∈ KMajor.kMajorFactorCoordinatesFrom n restCopies restBounds →
    left ≢ right
  cross leftMember rightMember equality =
    All.lookup fresh
      (kMajorFactorCoordinatesFromCopiesMember
        n restCopies restBounds rightMember)
      candidateEqualsRight
    where
    leftCopies : KMajor.copies left ≡ candidate
    leftCopies =
      coordinatesForCopiesCopies
        n candidate
        (proj₁ candidateBounds) (proj₂ candidateBounds)
        (Hecke.oneTo n) (OneTo.oneToAllBounds n)
        leftMember

    outputCopies : KMajor.copies left ≡ KMajor.copies right
    outputCopies = cong KMajor.copies equality

    candidateEqualsRight : candidate ≡ KMajor.copies right
    candidateEqualsRight = trans (sym leftCopies) outputCopies

kMajorFactorCoordinatesUnique :
  (n : Nat) → Unique (KMajor.kMajorFactorCoordinates n)
kMajorFactorCoordinatesUnique n =
  kMajorFactorCoordinatesFromUnique
    n
    (Hecke.oneTo n)
    (OneTo.oneToAllBounds n)
    (OneTo.oneToUnique n)

------------------------------------------------------------------------
-- The k-major factor carrier is now finite, complete and duplicate-free.
-- What remains for the exact permutation is only a membership bridge between
-- this coordinate presentation and the existing residual-major factor data.
------------------------------------------------------------------------
