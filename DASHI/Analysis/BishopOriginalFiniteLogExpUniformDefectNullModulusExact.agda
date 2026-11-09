{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalFiniteLogExpUniformDefectNullModulusExact where

------------------------------------------------------------------------
-- K04d P0.03: THE EXPLICIT STAGEWISE ERROR MODULUS TENDS TO ZERO.
--
-- For each *fixed* original LOG degree N and radius r, the source
-- numerical majorant
--
-- B_N(r,h) = |h|*S_N(r,0)*exp_B(|h|P_N(r))
--          + P_N(r)*(exp_B(|h|P_N(r))-1)
--
-- converges to 0 for EVERY original Bishop null sequence h_j->0.
-- This is an actual source-native sequential convergence witness.
--
-- Combined with the preceding radius-uniform order theorem, this
-- closes fixed-stage compact-uniform factor quotient continuity.
-- Uniformity IN N and the terminal finite-stage endpoint bound
-- are separate outstanding analytic obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.BishopOriginalFiniteLogExpStagewiseUniformDefectExact as Uniform
import DASHI.Analysis.BishopOriginalFiniteLogQuotientSecondOrderExact as Second
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopOriginalExponentialSequentialContinuityExact as ExpCont
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as ExpZero
import DASHI.Foundations.BishopLogAtanFiniteDerivativeGeometricExact as Geo

originalNullAbsoluteConvergesZero :
  ∀ {h : Nat → R.ℝ} →
  Seq._ConvergesTo_ h R.0ℝ →
  Seq._ConvergesTo_ (λ k → R.∣ h k ∣) R.0ℝ
originalNullAbsoluteConvergesZero {h} hConverges =
  Seq.xₙ→x∧x≃y⇒xₙ→y
    (Seq.∣xₙ∣→∣x₀∣ (R.0ℝ , hConverges))
    (RP.nonNegx⇒∣x∣≃x RP.nonNeg0)

originalNullScaledConvergesZero :
  (scale : R.ℝ) →
  ∀ {h : Nat → R.ℝ} →
  Seq._ConvergesTo_ h R.0ℝ →
  Seq._ConvergesTo_ (λ k → R._*_ h k scale) R.0ℝ
originalNullScaledConvergesZero scale {h} hConverges =
  Seq.xₙ→x∧x≃y⇒xₙ→y
    (Seq.xₙyₙ→x₀y₀
      (R.0ℝ , hConverges)
      (scale , Power.constantConverges scale))
    (let open RP.ℝ-Solver in
     solve 1
       (λ ss → Κ 0ℚᵘ ⊗ ss ⊜ Κ 0ℚᵘ)
       RP.≃-refl scale)

originalNullExpOfScaledAbsConvergesOne :
  (scale : R.ℝ) →
  ∀ {h : Nat → R.ℝ} →
  Seq._ConvergesTo_ h R.0ℝ →
  Seq._ConvergesTo_
    (λ k → Exp.bishopExp
      (R._*_ (R.∣ h k ∣) scale))
    R.1ℝ
originalNullExpOfScaledAbsConvergesOne
    scale {h} hConverges =
  Seq.xₙ→x∧x≃y⇒xₙ→y
    (ExpCont.originalBishopExpSequentiallyContinuous
      (λ k → R._*_ (R.∣ h k ∣) scale)
      R.0ℝ
      (originalNullScaledConvergesZero
        scale (originalNullAbsoluteConvergesZero hConverges)))
    ExpZero.bishopExpZero

originalNullExpOfScaledAbsMinusOneConvergesZero :
  (scale : R.ℝ) →
  ∀ {h : Nat → R.ℝ} →
  Seq._ConvergesTo_ h R.0ℝ →
  Seq._ConvergesTo_
    (λ k → R._-_
      (Exp.bishopExp (R._*_ (R.∣ h k ∣) scale))
      R.1ℝ)
    R.0ℝ
originalNullExpOfScaledAbsMinusOneConvergesZero
    scale {h} hConverges =
  Seq.xₙ→x∧x≃y⇒xₙ→y
    (Seq.xₙ+yₙ→x₀+y₀
      (R.1ℝ , originalNullExpOfScaledAbsConvergesOne
        scale hConverges)
      (R.-_ R.1ℝ , Power.constantConverges (R.-_ R.1ℝ)))
    (RP.+-inverseʳ R.1ℝ)

-- The real endpoint error budget itself is a finite sum of two
-- original source products. Both approach zero independently.
originalFiniteLogStagewiseUniformBudgetConvergesZero :
  (stage : Nat) (radius : R.ℝ) →
  ∀ {h : Nat → R.ℝ} →
  Seq._ConvergesTo_ h R.0ℝ →
  Seq._ConvergesTo_
    (λ k → Uniform.sourceOriginalUniformErrorBudget
      stage radius (h k))
    R.0ℝ
originalFiniteLogStagewiseUniformBudgetConvergesZero
    stage radius {h} hConverges =
  let
    p = Geo.negativeLogDerivativePolynomial radius stage
    s = Second.sourceFiniteLogSecondQuotient radius R.0ℝ stage
    absConverges = originalNullAbsoluteConvergesZero hConverges
    scaledConverges =
      originalNullScaledConvergesZero s absConverges
    expConverges =
      originalNullExpOfScaledAbsConvergesOne p hConverges
    expMinusOneConverges =
      originalNullExpOfScaledAbsMinusOneConvergesZero
        p hConverges
    firstConverges :
      Seq._ConvergesTo_
        (λ k →
          R._*_
            (R._*_ (R.∣ h k ∣) s)
            (Exp.bishopExp (R._*_ (R.∣ h k ∣) p)))
        R.0ℝ
    firstConverges =
      Seq.xₙ→x∧x≃y⇒xₙ→y
        (Seq.xₙyₙ→x₀y₀
          (R.0ℝ , scaledConverges)
          (R.1ℝ , expConverges))
        (let open RP.ℝ-Solver in
         solve 0
           (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊜ Κ 0ℚᵘ)
           RP.≃-refl)
    secondConverges :
      Seq._ConvergesTo_
        (λ k →
          R._*_ p
            (R._-_
              (Exp.bishopExp (R._*_ (R.∣ h k ∣) p))
              R.1ℝ))
        R.0ℝ
    secondConverges =
      Seq.xₙ→x∧x≃y⇒xₙ→y
        (Seq.xₙyₙ→x₀y₀
          (p , Power.constantConverges p)
          (R.0ℝ , expMinusOneConverges))
        (let open RP.ℝ-Solver in
         solve 1
           (λ pp → pp ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
           RP.≃-refl p)
  in
  Seq.xₙ→x∧x≃y⇒xₙ→y
    (Seq.xₙ+yₙ→x₀+y₀
      (R.0ℝ , firstConverges)
      (R.0ℝ , secondConverges))
    (RP.+-identityʳ R.0ℝ)
