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
-- Close the finite bookkeeping in Section 4. A Boolean decision partitions
-- every finite contribution list without loss or duplication, and subsequent
-- decisions partition J1 into J11/J12 and J11 into the lower/upper dyadic
-- ranges. The analytic task is only to identify the decisions with Luo's
-- ranges and bound each generated sum; every sum identity below is derived.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

mapContribution :
  ∀ {A : Set} → (A → ℚ) → List A → List ℚ
mapContribution function [] = []
mapContribution function (value ∷ rest) =
  function value ∷ mapContribution function rest

sumℚ : List ℚ → ℚ
sumℚ [] = 0ℚ
sumℚ (value ∷ values) = value + sumℚ values

mask : Bool → ℚ → ℚ
mask true value = value
mask false value = 0ℚ

maskedContribution :
  ∀ {A : Set} → (A → Bool) → (A → ℚ) → A → ℚ
maskedContribution decision contribution value =
  mask (decision value) (contribution value)

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

selectedSumIsMaskedSum :
  ∀ {A : Set}
    (decision : A → Bool)
    (contribution : A → ℚ)
    (values : List A) →
  selectedSum decision contribution values
  ≡ sumℚ
      (mapContribution
        (maskedContribution decision contribution)
        values)
selectedSumIsMaskedSum decision contribution [] = refl
selectedSumIsMaskedSum decision contribution (value ∷ values)
  with decision value
... | true =
  cong (contribution value +_)
    (selectedSumIsMaskedSum decision contribution values)
... | false =
  trans
    (selectedSumIsMaskedSum decision contribution values)
    (sym
      (ℚₚ.+-identityˡ
        (sumℚ
          (mapContribution
            (maskedContribution decision contribution)
            values))))

partitionSum :
  ∀ {A : Set}
    (decision : A → Bool)
    (contribution : A → ℚ)
    (values : List A) →
  sumℚ (mapContribution contribution values)
  ≡ selectedSum decision contribution values
      + rejectedSum decision contribution values
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

    J2DecisionHasSourceMeaning : Set
    j2DecisionHasSourceMeaning : J2DecisionHasSourceMeaning

    J11DecisionHasSourceMeaning : Set
    j11DecisionHasSourceMeaning : J11DecisionHasSourceMeaning

    LowerHalfDecisionHasSourceMeaning : Set
    lowerHalfDecisionHasSourceMeaning : LowerHalfDecisionHasSourceMeaning

open Equation42FiniteRangeData public

j1Contribution :
  (data : Equation42FiniteRangeData) →
  Nat → Interaction data → ℚ
j1Contribution data shell =
  maskedContribution
    (isJ1 data shell)
    (contributionAt data shell)

j11Contribution :
  (data : Equation42FiniteRangeData) →
  Nat → Interaction data → ℚ
j11Contribution data shell =
  maskedContribution
    (isJ11WithinJ1 data shell)
    (j1Contribution data shell)

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
    (j1Contribution data shell)
    (interactionsAt data shell)
J12 data shell =
  rejectedSum
    (isJ11WithinJ1 data shell)
    (j1Contribution data shell)
    (interactionsAt data shell)

lowerHalfJ11 upperHalfJ11 : Equation42FiniteRangeData → Nat → ℚ
lowerHalfJ11 data shell =
  selectedSum
    (isLowerHalfWithinJ11 data shell)
    (j11Contribution data shell)
    (interactionsAt data shell)
upperHalfJ11 data shell =
  rejectedSum
    (isLowerHalfWithinJ11 data shell)
    (j11Contribution data shell)
    (interactionsAt data shell)

totalInteractionSum : Equation42FiniteRangeData → Nat → ℚ
totalInteractionSum data shell =
  sumℚ
    (mapContribution
      (contributionAt data shell)
      (interactionsAt data shell))

J1J2Meaning :
  (data : Equation42FiniteRangeData) →
  (shell : Nat) →
  totalInteractionSum data shell
  ≡ J1 data shell + J2 data shell
J1J2Meaning data shell =
  partitionSum
    (isJ1 data shell)
    (contributionAt data shell)
    (interactionsAt data shell)

J11J12Meaning :
  (data : Equation42FiniteRangeData) →
  (shell : Nat) →
  J1 data shell ≡ J11 data shell + J12 data shell
J11J12Meaning data shell =
  trans
    (selectedSumIsMaskedSum
      (isJ1 data shell)
      (contributionAt data shell)
      (interactionsAt data shell))
    (partitionSum
      (isJ11WithinJ1 data shell)
      (j1Contribution data shell)
      (interactionsAt data shell))

J11RangeMeaning :
  (data : Equation42FiniteRangeData) →
  (shell : Nat) →
  J11 data shell
  ≡ lowerHalfJ11 data shell + upperHalfJ11 data shell
J11RangeMeaning data shell =
  trans
    (selectedSumIsMaskedSum
      (isJ11WithinJ1 data shell)
      (j1Contribution data shell)
      (interactionsAt data shell))
    (partitionSum
      (isLowerHalfWithinJ11 data shell)
      (j11Contribution data shell)
      (interactionsAt data shell))

record Equation42FiniteAssemblyCertificate
    (data : Equation42FiniteRangeData) : Set where
  constructor finite-assembly
  field
    totalMeaning :
      (shell : Nat) →
      totalInteractionSum data shell
      ≡ J1 data shell + J2 data shell

    J1Meaning :
      (shell : Nat) → J1 data shell ≡ J11 data shell + J12 data shell

    J11Meaning :
      (shell : Nat) →
      J11 data shell
      ≡ lowerHalfJ11 data shell + upperHalfJ11 data shell

open Equation42FiniteAssemblyCertificate public

equation42FiniteAssemblyCertificate :
  (data : Equation42FiniteRangeData) →
  Equation42FiniteAssemblyCertificate data
equation42FiniteAssemblyCertificate data =
  finite-assembly
    (J1J2Meaning data)
    (J11J12Meaning data)
    (J11RangeMeaning data)

finiteEquation42NestedRangeAssemblyConstructed : Bool
finiteEquation42NestedRangeAssemblyConstructed = true

finiteEquation42NestedRangeAssemblyConstructedIsTrue :
  finiteEquation42NestedRangeAssemblyConstructed ≡ true
finiteEquation42NestedRangeAssemblyConstructedIsTrue = refl
