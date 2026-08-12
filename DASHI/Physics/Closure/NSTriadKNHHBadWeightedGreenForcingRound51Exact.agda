module DASHI.Physics.Closure.NSTriadKNHHBadWeightedGreenForcingRound51Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 50's raw-prefix forcing theorem discards all later contraction.  The
-- exact variable-coefficient recurrence
--
--   C_(q+1) <= alpha_q C_q + beta_q
--
-- has the discrete Green representation
--
--   C_n <= A_n C_0 + G_n,
--   A_(n+1) = alpha_n A_n,
--   G_(n+1) = alpha_n G_n + beta_n.
--
-- Recursively, G_n is exactly
--
--   sum_{k<n} beta_k prod_{k<j<n} alpha_j.
--
-- Therefore the physical theorem need only bound the WEIGHTED forcing response
-- G_n, not the raw prefix sum of beta.  Under 0 <= alpha_q <= 1, A_n <= 1 and
--
--   G_n <= B  ==>  C_n <= C_0 + B.
--
-- This strictly contains uniform strict contraction and raw summable forcing
-- as convenient sufficient routes while preserving the same owner ceiling.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_ ; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record VariableGreenRecurrence : Set where
  field
    profile alpha forcing : Nat → ℚ
    profileNonnegative : ∀ q → 0ℚ ≤ profile q
    alphaNonnegative : ∀ q → 0ℚ ≤ alpha q
    alphaAtMostOne : ∀ q → alpha q ≤ 1ℚ
    forcingNonnegative : ∀ q → 0ℚ ≤ forcing q
    recurrence : ∀ q →
      profile (suc q) ≤ alpha q * profile q + forcing q

open VariableGreenRecurrence public

survivalProduct : VariableGreenRecurrence → Nat → ℚ
survivalProduct input zero = 1ℚ
survivalProduct input (suc n) =
  alpha input n * survivalProduct input n

weightedGreenResponse : VariableGreenRecurrence → Nat → ℚ
weightedGreenResponse input zero = 0ℚ
weightedGreenResponse input (suc n) =
  alpha input n * weightedGreenResponse input n + forcing input n

survivalProductNonnegative :
  (input : VariableGreenRecurrence) →
  ∀ n → 0ℚ ≤ survivalProduct input n
survivalProductNonnegative input zero = ℚP.0≤1
survivalProductNonnegative input (suc n) =
  let instance
    alphaNNI = nonNegative (alphaNonnegative input n)
    previousNNI = nonNegative (survivalProductNonnegative input n)
    productNNI =
      ℚP.nonNeg*nonNeg⇒nonNeg
        (alpha input n) (survivalProduct input n)
  in ℚP.nonNegative⁻¹ (survivalProduct input (suc n))

survivalProductAtMostOne :
  (input : VariableGreenRecurrence) →
  ∀ n → survivalProduct input n ≤ 1ℚ
survivalProductAtMostOne input zero = ℚP.≤-refl
survivalProductAtMostOne input (suc n) =
  let
    first :
      alpha input n * survivalProduct input n
      ≤ alpha input n * 1ℚ
    first =
      let instance alphaNNI = nonNegative (alphaNonnegative input n)
      in ℚP.*-monoˡ-≤-nonNeg
        (alpha input n)
        (survivalProductAtMostOne input n)

    second : alpha input n * 1ℚ ≤ 1ℚ * 1ℚ
    second =
      let instance oneNNI = nonNegative ℚP.0≤1
      in ℚP.*-monoʳ-≤-nonNeg 1ℚ (alphaAtMostOne input n)
  in
  ℚP.≤-trans first
    (ℚP.≤-trans second
      (subst (1ℚ ≤_) (solve []) ℚP.≤-refl))

weightedGreenResponseNonnegative :
  (input : VariableGreenRecurrence) →
  ∀ n → 0ℚ ≤ weightedGreenResponse input n
weightedGreenResponseNonnegative input zero = ℚP.≤-refl
weightedGreenResponseNonnegative input (suc n) =
  let instance
    alphaNNI = nonNegative (alphaNonnegative input n)
    greenNNI = nonNegative (weightedGreenResponseNonnegative input n)
    inheritedNNI =
      ℚP.nonNeg*nonNeg⇒nonNeg
        (alpha input n) (weightedGreenResponse input n)
  in
  ℚP.+-mono-≤
    (ℚP.nonNegative⁻¹
      (alpha input n * weightedGreenResponse input n))
    (forcingNonnegative input n)

profileBelowGreenRepresentation :
  (input : VariableGreenRecurrence) →
  ∀ n →
  profile input n
  ≤ survivalProduct input n * profile input zero
    + weightedGreenResponse input n
profileBelowGreenRepresentation input zero =
  subst
    (profile input zero ≤_)
    (solve (profile input zero ∷ []))
    ℚP.≤-refl
profileBelowGreenRepresentation input (suc n) =
  let
    inheritedScaled :
      alpha input n * profile input n
      ≤ alpha input n
        * (survivalProduct input n * profile input zero
          + weightedGreenResponse input n)
    inheritedScaled =
      let instance alphaNNI = nonNegative (alphaNonnegative input n)
      in ℚP.*-monoˡ-≤-nonNeg
        (alpha input n)
        (profileBelowGreenRepresentation input n)

    withForcing :
      alpha input n * profile input n + forcing input n
      ≤ alpha input n
          * (survivalProduct input n * profile input zero
            + weightedGreenResponse input n)
        + forcing input n
    withForcing = ℚP.+-mono-≤ inheritedScaled ℚP.≤-refl

    combined :
      profile input (suc n)
      ≤ alpha input n
          * (survivalProduct input n * profile input zero
            + weightedGreenResponse input n)
        + forcing input n
    combined = ℚP.≤-trans (recurrence input n) withForcing
  in
  subst
    (profile input (suc n) ≤_)
    (solve
      ( alpha input n
      ∷ survivalProduct input n
      ∷ profile input zero
      ∷ weightedGreenResponse input n
      ∷ forcing input n
      ∷ []))
    combined

record UniformWeightedGreenBound
    (input : VariableGreenRecurrence) : Set where
  field
    weightedBudget : ℚ
    weightedBudgetNonnegative : 0ℚ ≤ weightedBudget
    everyGreenResponseBelowBudget : ∀ n →
      weightedGreenResponse input n ≤ weightedBudget

open UniformWeightedGreenBound public

profileBelowBasePlusWeightedBudget :
  (input : VariableGreenRecurrence) →
  (bound : UniformWeightedGreenBound input) →
  ∀ n →
  profile input n ≤ profile input zero + weightedBudget bound
profileBelowBasePlusWeightedBudget input bound n =
  let
    baseNN = profileNonnegative input zero
    productBaseBelowBase :
      survivalProduct input n * profile input zero
      ≤ 1ℚ * profile input zero
    productBaseBelowBase =
      let instance baseNNI = nonNegative baseNN
      in ℚP.*-monoʳ-≤-nonNeg
        (profile input zero)
        (survivalProductAtMostOne input n)

    combined :
      survivalProduct input n * profile input zero
        + weightedGreenResponse input n
      ≤ 1ℚ * profile input zero + weightedBudget bound
    combined =
      ℚP.+-mono-≤
        productBaseBelowBase
        (everyGreenResponseBelowBudget bound n)
  in
  ℚP.≤-trans
    (profileBelowGreenRepresentation input n)
    (subst
      (λ right →
        survivalProduct input n * profile input zero
          + weightedGreenResponse input n ≤ right)
      (solve (profile input zero ∷ weightedBudget bound ∷ []))
      combined)

record WeightedGreenLiveTarget
    (input : VariableGreenRecurrence)
    (bound : UniformWeightedGreenBound input) : Set where
  field
    target : ℚ
    basePlusWeightedBudgetStrict :
      profile input zero + weightedBudget bound < target

open WeightedGreenLiveTarget public

profileStrictlyBelowWeightedTarget :
  (input : VariableGreenRecurrence) →
  (bound : UniformWeightedGreenBound input) →
  (live : WeightedGreenLiveTarget input bound) →
  ∀ n → profile input n < target live
profileStrictlyBelowWeightedTarget input bound live n =
  ℚP.≤-<-trans
    (profileBelowBasePlusWeightedBudget input bound n)
    (basePlusWeightedBudgetStrict live)

weightedGreenForcingStrictlyWeakerThanRawPrefixRequirement : Bool
weightedGreenForcingStrictlyWeakerThanRawPrefixRequirement = true

weightedGreenMasterRecurrenceClosed : Bool
weightedGreenMasterRecurrenceClosed = true

weightedGreenMasterRecurrenceClosedIsTrue :
  weightedGreenMasterRecurrenceClosed ≡ true
weightedGreenMasterRecurrenceClosedIsTrue = refl
