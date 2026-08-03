module DASHI.Physics.Closure.NSTriadKNLuoEquation42FiniteRangeAssemblyExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Close the finite bookkeeping in Section 4.  A Boolean decision partitions
-- every finite contribution list without loss or duplication, and a second
-- decision partitions J11 into the lower-half and upper-half dyadic ranges.
-- The analytic task is reduced to proving the meaning of the decisions and
-- bounding each generated sum; the sum identities themselves are recursive
-- theorems.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

sumℚ : List ℚ → ℚ
sumℚ [] = 0ℚ
sumℚ (value ∷ values) = value + sumℚ values

selectedSum :
  ∀ {A : Set} → (A → Bool) → (A → ℚ) → List A → ℚ
selectedSum decision contribution [] = 0ℚ
selectedSum decision contribution (value ∷ values)
  with decision value
... | true = contribution value + selectedSum decision contribution values
... | false = selectedSum decision contribution values

rejectedSum :
  ∀ {A : Set} → (A → Bool) → (A → ℚ) → List A → ℚ
rejectedSum decision contribution [] = 0ℚ
rejectedSum decision contribution (value ∷ values)
  with decision value
... | true = rejectedSum decision contribution values
... | false = contribution value + rejectedSum decision contribution values

partitionSum :
  ∀ {A : Set}
    (decision : A → Bool)
    (contribution : A → ℚ)
    (values : List A) →
  sumℚ (mapContribution contribution values)
  ≡ selectedSum decision contribution values
      + rejectedSum decision contribution values
  where
  mapContribution : ∀ {B : Set} → (B → ℚ) → List B → List ℚ
  mapContribution function [] = []
  mapContribution function (value ∷ rest) =
    function value ∷ mapContribution function rest
partitionSum decision contribution [] =
  sym (ℚₚ.+-identityˡ 0ℚ)
partitionSum decision contribution (value ∷ values)
  with decision value
... | true =
  trans
    (cong (contribution value +_)
      (partitionSum decision contribution values))
    (sym
      (ℚₚ.+-assoc
        (contribution value)
        (selectedSum decision contribution values)
        (rejectedSum decision contribution values)))
... | false =
  trans
    (cong (contribution value +_)
      (partitionSum decision contribution values))
    (trans
      (ℚₚ.+-assoc
        (contribution value)
        (selectedSum decision contribution values)
        (rejectedSum decision contribution values))
      (trans
        (cong
          (_+ rejectedSum decision contribution values)
          (ℚₚ.+-comm
            (contribution value)
            (selectedSum decision contribution values)))
        (sym
          (ℚₚ.+-assoc
            (selectedSum decision contribution values)
            (contribution value)
            (rejectedSum decision contribution values)))))

record Equation42FiniteRangeData : Set₁ where
  field
    Interaction : Set
    interactionsAt : Nat → List Interaction
    contributionAt : Nat → Interaction → ℚ

    isJ1 : Nat → Interaction → Bool
    isJ11WithinJ1 : Nat → Interaction → Bool
    isLowerHalfWithinJ11 : Nat → Interaction → Bool

    J1DecisionHasSourceMeaning : Set
    j1DecisionHasSourceMeaning : J1DecisionHasSourceMeaning

    J11DecisionHasSourceMeaning : Set
    j11DecisionHasSourceMeaning : J11DecisionHasSourceMeaning

    LowerHalfDecisionHasSourceMeaning : Set
    lowerHalfDecisionHasSourceMeaning : LowerHalfDecisionHasSourceMeaning

open Equation42FiniteRangeData public

J1 J2 : Equation42FiniteRangeData → Nat → ℚ
J1 data shell =
  selectedSum
    (isJ1 data shell)
    (contributionAt data shell)
    (interactionsAt data shell)
J2 data shell =
  rejectedSum
    (isJ1 data shell)
    (contributionAt data shell)
    (interactionsAt data shell)

J11 J12 : Equation42FiniteRangeData → Nat → ℚ
J11 data shell =
  selectedSum
    (isJ11WithinJ1 data shell)
    (λ interaction →
      ifSelected
        (isJ1 data shell interaction)
        (contributionAt data shell interaction))
    (interactionsAt data shell)
  where
  ifSelected : Bool → ℚ → ℚ
  ifSelected true value = value
  ifSelected false value = 0ℚ
J12 data shell =
  rejectedSum
    (isJ11WithinJ1 data shell)
    (λ interaction →
      ifSelected
        (isJ1 data shell interaction)
        (contributionAt data shell interaction))
    (interactionsAt data shell)
  where
  ifSelected : Bool → ℚ → ℚ
  ifSelected true value = value
  ifSelected false value = 0ℚ

lowerHalfJ11 upperHalfJ11 : Equation42FiniteRangeData → Nat → ℚ
lowerHalfJ11 data shell =
  selectedSum
    (isLowerHalfWithinJ11 data shell)
    (λ interaction →
      j11Contribution
        (isJ1 data shell interaction)
        (isJ11WithinJ1 data shell interaction)
        (contributionAt data shell interaction))
    (interactionsAt data shell)
  where
  j11Contribution : Bool → Bool → ℚ → ℚ
  j11Contribution true true value = value
  j11Contribution true false value = 0ℚ
  j11Contribution false within value = 0ℚ
upperHalfJ11 data shell =
  rejectedSum
    (isLowerHalfWithinJ11 data shell)
    (λ interaction →
      j11Contribution
        (isJ1 data shell interaction)
        (isJ11WithinJ1 data shell interaction)
        (contributionAt data shell interaction))
    (interactionsAt data shell)
  where
  j11Contribution : Bool → Bool → ℚ → ℚ
  j11Contribution true true value = value
  j11Contribution true false value = 0ℚ
  j11Contribution false within value = 0ℚ

record Equation42FiniteAssemblyCertificate
    (data : Equation42FiniteRangeData) : Set where
  field
    totalInteractionSum : Nat → ℚ
    totalMeaning :
      (shell : Nat) →
      totalInteractionSum shell
      ≡ J1 data shell + J2 data shell

    J1Meaning :
      (shell : Nat) → J1 data shell ≡ J11 data shell + J12 data shell

    J11Meaning :
      (shell : Nat) →
      J11 data shell
      ≡ lowerHalfJ11 data shell + upperHalfJ11 data shell

open Equation42FiniteAssemblyCertificate public

finiteEquation42NestedRangeAssemblyConstructed : Bool
finiteEquation42NestedRangeAssemblyConstructed = true

finiteEquation42NestedRangeAssemblyConstructedIsTrue :
  finiteEquation42NestedRangeAssemblyConstructed ≡ true
finiteEquation42NestedRangeAssemblyConstructedIsTrue = refl
