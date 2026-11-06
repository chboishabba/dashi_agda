module DASHI.Physics.YangMills.YMClayRGLossBudgetToNonGaussianExact where

------------------------------------------------------------------------
-- 2026-11-06 | R445/T5/Clay : uniform physical noncollapse from an
-- actual reference-scale charge and a summable one-sided RG loss.
--
-- This is NOT another unproved field named "finiteCumulantLowerBound":
-- that whole cutoff-uniform family is DERIVED below.
--
-- The remaining physics is independently explicit: identify the same
-- Wilson/J charge, establish the original RG change-of-charge losses,
-- prove the summable physical error budget, and make the selected
-- continuum limit equal the actual weak-limit expectation/cumulant.
--
-- A sign convention on the chosen fourth cumulant must be proved
-- against the original observable; no sign is manufactured here.
-- Exact-head Agda and transitive source trust and Agda acceptance PENDING.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.YangMills.BalabanClayT5CumulantLowerBoundNontrivialityExact as T5

finiteRGLoss : (Nat → ℚ) → Nat → ℚ
finiteRGLoss loss zero = 0ℚ
finiteRGLoss loss (suc n) = finiteRGLoss loss n + loss n

record RGReferenceChargeSurvival : Set₁ where
  field
    charge : Nat → ℚ
    oneStepLoss : Nat → ℚ
    eta budget : ℚ

    etaPositive : 0ℚ < eta
    referenceCushion : eta + budget ≤ charge zero
    -- Original SAME-source Wilson conditional/RG change.
    nextChargeAtLeastPreviousMinusLoss : ∀ n →
      charge n ≤ charge (suc n) + oneStepLoss n
    -- The actual physical source estimate; not an arbitrary
    -- single-finite-stage budget.
    everyFiniteLossBelowBudget : ∀ n →
      finiteRGLoss oneStepLoss n ≤ budget

open RGReferenceChargeSurvival public

referenceChargeBelowCurrentPlusLoss :
  (r : RGReferenceChargeSurvival) (n : Nat) →
  charge r zero ≤ charge r n + finiteRGLoss (oneStepLoss r) n
referenceChargeBelowCurrentPlusLoss r zero =
  subst
    (λ right → charge r zero ≤ right)
    (sym (ℚP.+-identityʳ (charge r zero)))
    ℚP.≤-refl
referenceChargeBelowCurrentPlusLoss r (suc n) =
  let
    previous = referenceChargeBelowCurrentPlusLoss r n
    step = nextChargeAtLeastPreviousMinusLoss r n
    moved = ℚP.≤-trans previous
      (ℚP.+-mono-≤ step ℚP.≤-refl)
    reshuffle :
      (charge r (suc n) + oneStepLoss r n)
        + finiteRGLoss (oneStepLoss r) n
      ≡
      charge r (suc n)
        + (finiteRGLoss (oneStepLoss r) n + oneStepLoss r n)
    reshuffle = trans
      (ℚP.+-assoc
        (charge r (suc n))
        (oneStepLoss r n)
        (finiteRGLoss (oneStepLoss r) n))
      (cong (charge r (suc n) +_)
        (ℚP.+-comm (oneStepLoss r n)
          (finiteRGLoss (oneStepLoss r) n)))
  in
  subst (λ right → charge r zero ≤ right) reshuffle moved

-- Universal finite UV noncollapse IS NOW THE CONCLUSION.
referenceRGUniformNoncollapse :
  (r : RGReferenceChargeSurvival) →
  ∀ n → eta r ≤ charge r n
referenceRGUniformNoncollapse r n =
  let
    fromReference :
      eta r + budget r
      ≤ charge r n + finiteRGLoss (oneStepLoss r) n
    fromReference = ℚP.≤-trans
      (referenceCushion r)
      (referenceChargeBelowCurrentPlusLoss r n)
    toBudget :
      eta r + budget r ≤ charge r n + budget r
    toBudget = ℚP.≤-trans fromReference
      (ℚP.+-mono-≤ ℚP.≤-refl
        (everyFiniteLossBelowBudget r n))
  in
  ℚP.+-cancelʳ-≤ (budget r) toBudget

-- The original T5 non-Gaussianity owner needs a convergent selected
-- continuum fourth-cumulant and a closed order interval, NOT a new
-- arbitrary fourth-cumulant lower bound.
record ActualRGContinuumChargeLimit
    (r : RGReferenceChargeSurvival) (Scalar : Set) : Set₁ where
  field
    -- The actual physical continuum scalar may be a vendor Bishop
    -- completion; it is NOT assumed to be a rational number.
    continuumCharge : Scalar
    zero : Scalar
    embed : ℚ → Scalar
    embedZero : embed 0ℚ ≡ zero
    LessEqual : Scalar → Scalar → Set
    Positive : Scalar → Set
    Converges : (Nat → Scalar) → Scalar → Set

    embedPreservesOrder : ∀ {a b : ℚ} →
      a ≤ b → LessEqual (embed a) (embed b)
    embedPreservesPositive : ∀ q →
      0ℚ < q → Positive (embed q)
    positiveCannotLieBelowZero : ∀ value →
      Positive value → LessEqual value zero → T5.Empty

    actualChargeConverges :
      Converges (λ cutoff → embed (charge r cutoff)) continuumCharge
    selectedOrderIntervalClosed :
      ∀ sequence target →
      Converges sequence target →
      (∀ cutoff → LessEqual (embed (eta r)) (sequence cutoff)) →
      LessEqual (embed (eta r)) target

open ActualRGContinuumChargeLimit public

asOriginalT5Nontriviality :
  ∀ {Scalar : Set} (r : RGReferenceChargeSurvival) →
  ActualRGContinuumChargeLimit r Scalar →
  T5.UniformCumulantLowerBoundData Scalar
asOriginalT5Nontriviality r limit = record
  { T5.UniformCumulantLowerBoundData.zero = zero limit
  ; T5.UniformCumulantLowerBoundData.eta = embed limit (eta r)
  ; T5.UniformCumulantLowerBoundData.finiteCumulant =
      λ n → embed limit (charge r n)
  ; T5.UniformCumulantLowerBoundData.continuumCumulant =
      continuumCharge limit
  ; T5.UniformCumulantLowerBoundData.LessEqual = LessEqual limit
  ; T5.UniformCumulantLowerBoundData.Positive = Positive limit
  ; T5.UniformCumulantLowerBoundData.Converges = Converges limit
  ; T5.UniformCumulantLowerBoundData.finiteCumulantsConverge =
      actualChargeConverges limit
  ; T5.UniformCumulantLowerBoundData.finiteUniformLowerBound =
      λ cutoff → embedPreservesOrder limit
        (referenceRGUniformNoncollapse r cutoff)
  ; T5.UniformCumulantLowerBoundData.lowerOrderIntervalClosed =
      selectedOrderIntervalClosed limit
  ; T5.UniformCumulantLowerBoundData.etaPositive =
      embedPreservesPositive limit (eta r) (etaPositive r)
  ; T5.UniformCumulantLowerBoundData.positiveCannotLieBelowZero =
      positiveCannotLieBelowZero limit
  }

-- This proof respects the vendored Bishop real carrier: instantiate
-- Scalar with the completed carrier and pay the original embedding/
-- weak-limit semantics, rather than pretending a continuum cumulant
-- lies in Q.
continuumRGChargeIsNonzero :
  ∀ {Scalar : Set} (r : RGReferenceChargeSurvival)
  (limit : ActualRGContinuumChargeLimit r Scalar) →
  continuumCharge limit ≡ zero limit → T5.Empty
continuumRGChargeIsNonzero r limit =
  T5.uniformFiniteLowerBoundForcesContinuumNonzero
    (asOriginalT5Nontriviality r limit)
