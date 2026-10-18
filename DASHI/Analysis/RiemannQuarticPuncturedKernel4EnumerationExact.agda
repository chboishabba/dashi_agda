module DASHI.Analysis.RiemannQuarticPuncturedKernel4EnumerationExact where

------------------------------------------------------------------------
-- CONCRETE PUNCTURED KERNEL-4 ENUMERATION
--
-- DASHI CONTRIBUTION
--
-- Transport the repository's canonical unique enumeration
--
--   Vec (Fin 3) 4
--
-- through the exact coordinate codec Fin 3 <-> Trit into
--
--   TriadicPAdicCodec.Kernel 4.
--
-- Filtering by nonzero trit support then yields a unique, complete list of
-- punctured four-trit states.  Its exact length is 80.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (tt)
open import Data.Bool.Base using (T)
import Data.Fin.Base as Fin
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (map; filterᵇ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using
  (∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Function.Base using (_∘_)
open import Relation.Nullary.Decidable.Core using (T?)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.Vec.Base as Vec

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Analysis.RiemannQuarticTriadicCodecKernelBridgeExact as Bridge
import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Product
import DASHI.Mathematics.NumberTheory.FiniteProductCardinalityExact as Count
import DASHI.Mathematics.NumberTheory.FiniteDependentPairCardinalityExact as Card
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

open Codec using ([]ᵥ; _∷ᵥ_)

------------------------------------------------------------------------
-- 1. Exact Fin 3 <-> Trit coordinate chart.
------------------------------------------------------------------------

fin3ToTrit : Fin 3 → Trit
fin3ToTrit Fin.zero = neg
fin3ToTrit (Fin.suc Fin.zero) = zer
fin3ToTrit (Fin.suc (Fin.suc Fin.zero)) = pos

tritToFin3 : Trit → Fin 3
tritToFin3 neg = Fin.zero
tritToFin3 zer = Fin.suc Fin.zero
tritToFin3 pos = Fin.suc (Fin.suc Fin.zero)

fin3TritRoundTrip :
  (index : Fin 3) →
  tritToFin3 (fin3ToTrit index) ≡ index
fin3TritRoundTrip Fin.zero = refl
fin3TritRoundTrip (Fin.suc Fin.zero) = refl
fin3TritRoundTrip (Fin.suc (Fin.suc Fin.zero)) = refl

tritFin3RoundTrip :
  (trit : Trit) →
  fin3ToTrit (tritToFin3 trit) ≡ trit
tritFin3RoundTrip neg = refl
tritFin3RoundTrip zer = refl
tritFin3RoundTrip pos = refl

------------------------------------------------------------------------
-- 2. Coordinatewise vector/kernel chart.
------------------------------------------------------------------------

finVecToKernel :
  ∀ {dimension : Nat} →
  Vec.Vec (Fin 3) dimension →
  Codec.Kernel dimension
finVecToKernel Vec.[] = []ᵥ
finVecToKernel (head Vec.∷ tail) =
  fin3ToTrit head ∷ᵥ finVecToKernel tail

kernelToFinVec :
  ∀ {dimension : Nat} →
  Codec.Kernel dimension →
  Vec.Vec (Fin 3) dimension
kernelToFinVec []ᵥ = Vec.[]
kernelToFinVec (head ∷ᵥ tail) =
  tritToFin3 head Vec.∷ kernelToFinVec tail

finKernelRoundTrip :
  ∀ {dimension : Nat} →
  (vector : Vec.Vec (Fin 3) dimension) →
  kernelToFinVec (finVecToKernel vector) ≡ vector
finKernelRoundTrip Vec.[] = refl
finKernelRoundTrip (head Vec.∷ tail)
  rewrite fin3TritRoundTrip head
        | finKernelRoundTrip tail = refl

kernelFinRoundTrip :
  ∀ {dimension : Nat} →
  (kernel : Codec.Kernel dimension) →
  finVecToKernel (kernelToFinVec kernel) ≡ kernel
kernelFinRoundTrip []ᵥ = refl
kernelFinRoundTrip (head ∷ᵥ tail)
  rewrite tritFin3RoundTrip head
        | kernelFinRoundTrip tail = refl

finVecToKernelInjective :
  ∀ {dimension : Nat}
    {left right : Vec.Vec (Fin 3) dimension} →
  finVecToKernel left ≡ finVecToKernel right →
  left ≡ right
finVecToKernelInjective {left = left} {right = right} equality =
  trans
    (sym (finKernelRoundTrip left))
    (trans
      (cong kernelToFinVec equality)
      (finKernelRoundTrip right))

------------------------------------------------------------------------
-- 3. Unique complete Kernel-4 enumeration.
------------------------------------------------------------------------

kernel4Enumeration : List Bridge.Kernel4
kernel4Enumeration =
  map finVecToKernel
    (Product.uniqueFinVectorPower 3 4)

kernel4EnumerationUnique :
  Unique kernel4Enumeration
kernel4EnumerationUnique =
  UniqueP.map⁺
    finVecToKernelInjective
    (Product.uniqueFinVectorPowerNoDuplicates 3 4)

kernel4EnumerationComplete :
  (kernel : Bridge.Kernel4) →
  kernel ∈ kernel4Enumeration
kernel4EnumerationComplete kernel
  rewrite sym (kernelFinRoundTrip kernel) =
  Product.mapMember
    finVecToKernel
    (Product.uniqueFinVectorPowerComplete
      (kernelToFinVec kernel))

kernel4EnumerationLengthIs81 :
  Reindex.listLength kernel4Enumeration ≡ 81
kernel4EnumerationLengthIs81 =
  trans
    (Card.mapLength
      finVecToKernel
      (Product.uniqueFinVectorPower 3 4))
    (trans
      (Count.uniqueFinVectorPowerLength 3 4)
      refl)

------------------------------------------------------------------------
-- 4. Filter to the support-punctured carrier.
------------------------------------------------------------------------

puncturedKernel4Enumeration : List Bridge.Kernel4
puncturedKernel4Enumeration =
  filterᵇ Bridge.kernel4Support kernel4Enumeration

puncturedKernel4EnumerationUnique :
  Unique puncturedKernel4Enumeration
puncturedKernel4EnumerationUnique =
  UniqueP.filter⁺
    (T? ∘ Bridge.kernel4Support)
    kernel4EnumerationUnique

T-to-true :
  ∀ {value : Bool} →
  T value →
  value ≡ true
T-to-true {false} ()
T-to-true {true} witness = refl

true-to-T :
  ∀ {value : Bool} →
  value ≡ true →
  T value
true-to-T refl = tt

puncturedKernel4EnumerationSound :
  (kernel : Bridge.Kernel4) →
  kernel ∈ puncturedKernel4Enumeration →
  Bridge.kernel4Support kernel ≡ true
puncturedKernel4EnumerationSound kernel member
  with ∈-filter⁻ (T? ∘ Bridge.kernel4Support) member
... | baseMember , supportWitness =
  T-to-true supportWitness

puncturedKernel4EnumerationComplete :
  (kernel : Bridge.Kernel4) →
  Bridge.kernel4Support kernel ≡ true →
  kernel ∈ puncturedKernel4Enumeration
puncturedKernel4EnumerationComplete kernel supportExact =
  ∈-filter⁺
    (T? ∘ Bridge.kernel4Support)
    (kernel4EnumerationComplete kernel)
    (true-to-T supportExact)

puncturedKernel4EnumerationLengthIs80 :
  Reindex.listLength puncturedKernel4Enumeration ≡ 80
puncturedKernel4EnumerationLengthIs80 = refl

------------------------------------------------------------------------
-- 5. Constructive finite-cardinality certificate.
------------------------------------------------------------------------

record PuncturedKernel4FiniteEnumeration : Set where
  constructor punctured-kernel4-finite-enumeration
  field
    states : List Bridge.Kernel4
    statesAreCanonical :
      states ≡ puncturedKernel4Enumeration
    noDuplicates :
      Unique states
    sound :
      (kernel : Bridge.Kernel4) →
      kernel ∈ states →
      Bridge.kernel4Support kernel ≡ true
    complete :
      (kernel : Bridge.Kernel4) →
      Bridge.kernel4Support kernel ≡ true →
      kernel ∈ states
    stateCount :
      Reindex.listLength states ≡ 80

canonicalPuncturedKernel4FiniteEnumeration :
  PuncturedKernel4FiniteEnumeration
canonicalPuncturedKernel4FiniteEnumeration =
  punctured-kernel4-finite-enumeration
    puncturedKernel4Enumeration
    refl
    puncturedKernel4EnumerationUnique
    puncturedKernel4EnumerationSound
    puncturedKernel4EnumerationComplete
    puncturedKernel4EnumerationLengthIs80

record RiemannQuarticPuncturedKernel4EnumerationBoundary : Set where
  constructor riemann-quartic-punctured-kernel4-enumeration-boundary
  field
    fin3TritChartExact : Bool
    kernel4EnumerationComplete : Bool
    kernel4EnumerationUnique : Bool
    fullKernel4Count81 : Bool
    supportPunctureComplete : Bool
    supportPunctureUnique : Bool
    puncturedKernel4Count80 : Bool
    rhSemanticIdentityClaimed : Bool

canonicalRiemannQuarticPuncturedKernel4EnumerationBoundary :
  RiemannQuarticPuncturedKernel4EnumerationBoundary
canonicalRiemannQuarticPuncturedKernel4EnumerationBoundary =
  riemann-quartic-punctured-kernel4-enumeration-boundary
    true true true true true true true false
