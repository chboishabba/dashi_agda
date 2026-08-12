module DASHI.Physics.Closure.NSTriadKNHHBadDyadicInheritedHalfRound48Exact where

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
-- The Round-47 selected recurrence needs
--
--   inherited_(q+1) <= (alpha/2) B_q.
--
-- This file isolates one exact mechanism capable of producing the required
-- half: one inverse dyadic shell factor.  If the inherited component has the
-- same-object factorization
--
--   I_q = delta_* 2^(-q) A_q
--
-- and the scale-free coefficient obeys
--
--   A_(q+1) <= alpha A_q,
--
-- then
--
--   I_(q+1) <= (alpha/2) I_q.
--
-- The theorem is deliberately conditional on the physical inverse-shell
-- factorization.  Dyadic notation alone does not prove that the actual
-- directional-defect transport has this form.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadDissipativeFloorChargingRound36Exact as Floor
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as Scale

record InverseShellInheritedDefect
    (parameter : Threshold.PositiveThreshold) : Set where
  field
    coefficient : Nat → ℚ
    coefficientNonnegative : ∀ q → 0ℚ ≤ coefficient q
    alpha : ℚ
    alphaNonnegative : 0ℚ ≤ alpha
    coefficientTransfer : ∀ q →
      coefficient (suc q) ≤ alpha * coefficient q

open InverseShellInheritedDefect public

inheritedDefect :
  ∀ {parameter} →
  InverseShellInheritedDefect parameter → Nat → ℚ
inheritedDefect {parameter} dataSet q =
  Threshold.threshold parameter
    * Sharp.inverseDyadicScale q
    * coefficient dataSet q

inheritedDefectNonnegative :
  ∀ {parameter}
    (dataSet : InverseShellInheritedDefect parameter) q →
  0ℚ ≤ inheritedDefect dataSet q
inheritedDefectNonnegative {parameter} dataSet q =
  let
    thresholdNN = Threshold.thresholdNonnegative parameter
    inverseNN = Floor.inverseDyadicScaleNonnegative q
    coefficientNN = coefficientNonnegative dataSet q
    instance
      thresholdNNI = nonNegative thresholdNN
      inverseNNI = nonNegative inverseNN
      thresholdInverseNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (Threshold.threshold parameter)
          (Sharp.inverseDyadicScale q)
      coefficientNNI = nonNegative coefficientNN
      totalNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (Threshold.threshold parameter * Sharp.inverseDyadicScale q)
          (coefficient dataSet q)
  in
  ℚP.nonNegative⁻¹ (inheritedDefect dataSet q)

inverseShellInheritedDefectHalvesModuloCoefficient :
  ∀ {parameter}
    (dataSet : InverseShellInheritedDefect parameter) q →
  inheritedDefect dataSet (suc q)
  ≤ alpha dataSet * Sharp.half * inheritedDefect dataSet q
inverseShellInheritedDefectHalvesModuloCoefficient
    {parameter} dataSet q =
  let
    prefactor : ℚ
    prefactor =
      Threshold.threshold parameter
        * Sharp.half * Sharp.inverseDyadicScale q

    prefactorNN : 0ℚ ≤ prefactor
    prefactorNN =
      let
        thresholdNN = Threshold.thresholdNonnegative parameter
        halfNN = Scale.halfNonnegative
        inverseNN = Floor.inverseDyadicScaleNonnegative q
        instance
          thresholdNNI = nonNegative thresholdNN
          halfNNI = nonNegative halfNN
          firstNNI =
            ℚP.nonNeg*nonNeg⇒nonNeg
              (Threshold.threshold parameter) Sharp.half
          inverseNNI = nonNegative inverseNN
          totalNNI =
            ℚP.nonNeg*nonNeg⇒nonNeg
              (Threshold.threshold parameter * Sharp.half)
              (Sharp.inverseDyadicScale q)
      in
      ℚP.nonNegative⁻¹ prefactor

    scaledCoefficient :
      prefactor * coefficient dataSet (suc q)
      ≤ prefactor * (alpha dataSet * coefficient dataSet q)
    scaledCoefficient =
      let instance prefactorNNI = nonNegative prefactorNN
      in ℚP.*-monoˡ-≤-nonNeg prefactor
          (coefficientTransfer dataSet q)

    leftMeaning :
      prefactor * coefficient dataSet (suc q)
      ≡ inheritedDefect dataSet (suc q)
    leftMeaning = solve
      ( Threshold.threshold parameter
      ∷ Sharp.inverseDyadicScale q
      ∷ coefficient dataSet (suc q)
      ∷ [])

    rightMeaning :
      prefactor * (alpha dataSet * coefficient dataSet q)
      ≡ alpha dataSet * Sharp.half * inheritedDefect dataSet q
    rightMeaning = solve
      ( Threshold.threshold parameter
      ∷ Sharp.inverseDyadicScale q
      ∷ alpha dataSet
      ∷ coefficient dataSet q
      ∷ [])
  in
  subst
    (λ left →
      left ≤ alpha dataSet * Sharp.half * inheritedDefect dataSet q)
    leftMeaning
    (subst
      (λ right → prefactor * coefficient dataSet (suc q) ≤ right)
      rightMeaning
      scaledCoefficient)

constantScaleFreeCoefficientGivesExactHalf :
  ∀ {parameter}
    (coefficientValue : ℚ) q →
  Threshold.threshold parameter
    * Sharp.inverseDyadicScale (suc q) * coefficientValue
  ≡ Sharp.half
    * (Threshold.threshold parameter
      * Sharp.inverseDyadicScale q * coefficientValue)
constantScaleFreeCoefficientGivesExactHalf coefficientValue q =
  solve
    ( Threshold.threshold _
    ∷ Sharp.inverseDyadicScale q
    ∷ coefficientValue
    ∷ [])

hhBadDyadicInheritanceHalfMechanismClosed : Bool
hhBadDyadicInheritanceHalfMechanismClosed = true

physicalInheritedDefectInverseShellFactorizationConstructed : Bool
physicalInheritedDefectInverseShellFactorizationConstructed = false

hhBadDyadicInheritanceHalfMechanismClosedIsTrue :
  hhBadDyadicInheritanceHalfMechanismClosed ≡ true
hhBadDyadicInheritanceHalfMechanismClosedIsTrue = refl

physicalInheritedDefectInverseShellFactorizationConstructedIsFalse :
  physicalInheritedDefectInverseShellFactorizationConstructed ≡ false
physicalInheritedDefectInverseShellFactorizationConstructedIsFalse = refl
