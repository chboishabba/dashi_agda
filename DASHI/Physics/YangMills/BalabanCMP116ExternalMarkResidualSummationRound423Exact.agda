{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116ExternalMarkResidualSummationRound423Exact where

------------------------------------------------------------------------
-- ROUND423 / EXTERNAL MARK FACTORS THROUGH POSITIVE CMP116 RESIDUAL SUM
--
-- This is the actual finite positive summation step needed by the shortest
-- R406 source route.
--
-- Suppose the selected source pair contributes one Y-independent marked
-- separation factor w_ext, while each surviving localization domain Y carries
-- a nonnegative residual tree/localisation weight r(Y):
--
--     commonYShell(Y) <= w_ext * r(Y)
--
-- and CMP116 residual summability gives
--
--     sum_Y r(Y) <= R.
--
-- Then
--
--     sum_Y commonYShell(Y) <= w_ext * R.
--
-- No new YM decay estimate is used here.  The theorem is finite ordered-real
-- algebra: sum monotonicity, distributivity, and multiplication monotonicity
-- for nonnegative factors.  The physical source work is now explicitly:
--
--   * retain the common external marked factor on every selected Y;
--   * prove the residual weights nonnegative;
--   * instantiate the published CMP116 residual tree/localisation sum;
--   * identify w_ext * R with the literal shared hessian shell.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _+ℝ_ ; _*ℝ_ ; _≤ℝ_
  ; ≤ℝ-refl ; ≤ℝ-trans ; +-mono-≤
  ; mulMonotoneNonnegative
  ; *-distribˡ-+ ; mulZeroʳ )
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum

sumNonnegative :
  ∀ {A : Set}
    (xs : List A)
    (value : A → ℝ) →
  (∀ x → 0ℝ ≤ℝ value x) →
  0ℝ ≤ℝ Resum.sumℝ value xs
sumNonnegative [] value pointwise = ≤ℝ-refl
sumNonnegative (x ∷ xs) value pointwise =
  +-mono-≤
    (pointwise x)
    (sumNonnegative xs value pointwise)

externalTimesSumExact :
  ∀ {A : Set}
    (external : ℝ)
    (value : A → ℝ)
    (xs : List A) →
  external *ℝ Resum.sumℝ value xs
  ≡
  Resum.sumℝ (λ x → external *ℝ value x) xs
externalTimesSumExact external value [] =
  mulZeroʳ external
externalTimesSumExact external value (x ∷ xs)
  rewrite *-distribˡ-+ external (value x) (Resum.sumℝ value xs)
        | externalTimesSumExact external value xs = refl

record ExternalMarkedResidualSummationData (Domain : Set) : Set₁ where
  field
    domains : List Domain

    commonYShell residualWeight : Domain → ℝ
    externalMarkedWeight residualEnvelope : ℝ

    externalMarkedWeightNonnegative :
      0ℝ ≤ℝ externalMarkedWeight

    residualWeightNonnegative :
      ∀ domain → 0ℝ ≤ℝ residualWeight domain

    commonYShellBelowExternalTimesResidual :
      ∀ domain →
      commonYShell domain
      ≤ℝ externalMarkedWeight *ℝ residualWeight domain

    residualSummability :
      Resum.sumℝ residualWeight domains ≤ℝ residualEnvelope

open ExternalMarkedResidualSummationData public

sumCommonYShellBelowExternalTimesResidualSum :
  ∀ {Domain}
    (dataSet : ExternalMarkedResidualSummationData Domain) →
  Resum.sumℝ (commonYShell dataSet) (domains dataSet)
  ≤ℝ
  externalMarkedWeight dataSet *ℝ
    Resum.sumℝ (residualWeight dataSet) (domains dataSet)
sumCommonYShellBelowExternalTimesResidualSum dataSet =
  subst
    (λ upper →
      Resum.sumℝ (commonYShell dataSet) (domains dataSet)
      ≤ℝ upper)
    (sym
      (externalTimesSumExact
        (externalMarkedWeight dataSet)
        (residualWeight dataSet)
        (domains dataSet)))
    (Resum.sumℝ-mono
      (domains dataSet)
      (commonYShellBelowExternalTimesResidual dataSet))

externalTimesResidualSumBelowEnvelope :
  ∀ {Domain}
    (dataSet : ExternalMarkedResidualSummationData Domain) →
  externalMarkedWeight dataSet *ℝ
    Resum.sumℝ (residualWeight dataSet) (domains dataSet)
  ≤ℝ
  externalMarkedWeight dataSet *ℝ residualEnvelope dataSet
externalTimesResidualSumBelowEnvelope dataSet =
  mulMonotoneNonnegative
    (externalMarkedWeightNonnegative dataSet)
    ≤ℝ-refl
    (sumNonnegative
      (domains dataSet)
      (residualWeight dataSet)
      (residualWeightNonnegative dataSet))
    (residualSummability dataSet)

sumCommonYShellBelowFactoredEnvelope :
  ∀ {Domain}
    (dataSet : ExternalMarkedResidualSummationData Domain) →
  Resum.sumℝ (commonYShell dataSet) (domains dataSet)
  ≤ℝ externalMarkedWeight dataSet *ℝ residualEnvelope dataSet
sumCommonYShellBelowFactoredEnvelope dataSet =
  ≤ℝ-trans
    (sumCommonYShellBelowExternalTimesResidualSum dataSet)
    (externalTimesResidualSumBelowEnvelope dataSet)

sumCommonYShellBelowTarget :
  ∀ {Domain}
    (dataSet : ExternalMarkedResidualSummationData Domain)
    (target : ℝ) →
  externalMarkedWeight dataSet *ℝ residualEnvelope dataSet ≡ target →
  Resum.sumℝ (commonYShell dataSet) (domains dataSet) ≤ℝ target
sumCommonYShellBelowTarget dataSet target factoredEnvelopeIsTarget =
  subst
    (λ upper →
      Resum.sumℝ (commonYShell dataSet) (domains dataSet) ≤ℝ upper)
    factoredEnvelopeIsTarget
    (sumCommonYShellBelowFactoredEnvelope dataSet)

round423ExternalMarkResidualSummationCompilerLevel : ProofLevel
round423ExternalMarkResidualSummationCompilerLevel = machineChecked

-- The finite positive sum is now compiler-owned.  These source facts remain:
round423PointwiseMarkedResidualFactorizationLevel : ProofLevel
round423PointwiseMarkedResidualFactorizationLevel = conditional

round423CMP116ResidualSummabilityInstantiationLevel : ProofLevel
round423CMP116ResidualSummabilityInstantiationLevel = conditional

round423SharedShellFactorizationLevel : ProofLevel
round423SharedShellFactorizationLevel = conditional

round423FreshOuterFiniteSumTheoremRequired : Bool
round423FreshOuterFiniteSumTheoremRequired = false
