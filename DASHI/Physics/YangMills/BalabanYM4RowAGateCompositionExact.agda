module DASHI.Physics.YangMills.BalabanYM4RowAGateCompositionExact where

------------------------------------------------------------------------
-- ROW A, COMPOSITION OF THE TWO NUMERICAL GATES ON ONE LITERAL TRAJECTORY
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I.", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The live shell theorem gives
--
--   beta_Z,j >= b_- ,  beta_Int,j >= - C g_j ,  g_j <= gamma
--       ==> beta_j >= b_* := b_- - C gamma.
--
-- Identifying beta_j with u_j-u_{j+1}, u_j=g_j^{-2}, gives the cubic
-- telescope
--
--   b_* sum_{j<K} g_j^3 <= 2 gamma_tube.
--
-- A uniform |d beta_j/dg| <= L therefore yields cumulative inverse-square
-- sensitivity <= L gamma_tube/b_*.  The two sharp numerical gates are
--
--   C gamma < b_- ,
--   L gamma_tube < b_*.
--
-- No physical b_-, C or L is supplied here; Row A remains open.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕP
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; -_; _/_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Decidable using (toWitness)

import DASHI.Physics.YangMills.BalabanYM4LinearInteractionBetaMarginExact as Shell
import DASHI.Physics.YangMills.BalabanYM4CubicCouplingDriftTelescopeExact as Cubic
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Shooting

record RowAGateData (cutoff : Nat) : Set where
  field
    gaussianFloor interactionConstant couplingCap tubeWidth : ℚ
    coupling betaGauss betaInteraction inverseSquare : Nat → ℚ

    interactionConstantNN : 0ℚ ≤ interactionConstant
    couplingCapNN : 0ℚ ≤ couplingCap
    couplingPositive : ∀ j → 0ℚ < coupling j
    couplingBelowCap : ∀ j → coupling j ≤ couplingCap
    gaussianLower : ∀ j → gaussianFloor ≤ betaGauss j
    interactionLower : ∀ j →
      - (interactionConstant * coupling j) ≤ betaInteraction j

    inverseSquareRelation : ∀ j →
      inverseSquare j * (coupling j * coupling j) ≡ 1ℚ
    couplingMonotone : ∀ j → coupling j ≤ coupling (suc j)
    betaIsInverseSquareStep : ∀ j → j ℕ.< cutoff →
      betaGauss j + betaInteraction j
      ≡ inverseSquare j - inverseSquare (suc j)

    couplingTube : ∀ K → coupling K - coupling zero ≤ tubeWidth
    signGate : interactionConstant * couplingCap < gaussianFloor

open RowAGateData public

module Gates {cutoff : Nat} (d : RowAGateData cutoff) where

  betaMargin : ℚ
  betaMargin = Shell.linearMargin
    (gaussianFloor d) (interactionConstant d) (couplingCap d)

  betaMarginPositive : 0ℚ < betaMargin
  betaMarginPositive =
    let
      product = interactionConstant d * couplingCap d
      shifted = ℚP.+-monoʳ-< (- product) (signGate d)
      leftZero : product + (- product) ≡ 0ℚ
      leftZero = ℚRing.solve-∀ product
      rightMargin : gaussianFloor d + (- product) ≡ betaMargin
      rightMargin = ℚRing.solve-∀
        (gaussianFloor d) (interactionConstant d) (couplingCap d)
    in
    subst (λ left → left < betaMargin) leftZero
      (subst (λ right → product + (- product) < right) rightMargin shifted)

  shellAt : Nat → Shell.LinearInteractionShell
    (gaussianFloor d) (interactionConstant d) (couplingCap d)
  shellAt j = record
    { Shell.LinearInteractionShell.coupling = coupling d j
    ; Shell.LinearInteractionShell.betaZ = betaGauss d j
    ; Shell.LinearInteractionShell.betaInt = betaInteraction d j
    ; Shell.LinearInteractionShell.interactionConstantNonnegative = interactionConstantNN d
    ; Shell.LinearInteractionShell.couplingNonnegative = ℚP.<⇒≤ (couplingPositive d j)
    ; Shell.LinearInteractionShell.gammaNonnegative = couplingCapNN d
    ; Shell.LinearInteractionShell.couplingBelowGamma = couplingBelowCap d j
    ; Shell.LinearInteractionShell.gaussianLower = gaussianLower d j
    ; Shell.LinearInteractionShell.interactionLower = interactionLower d j
    }

  inverseSquareMargin : ∀ j → j ℕ.< cutoff →
    betaMargin ≤ inverseSquare d j - inverseSquare d (suc j)
  inverseSquareMargin j j<cutoff =
    subst (λ right → betaMargin ≤ right)
      (betaIsInverseSquareStep d j j<cutoff)
      (Shell.singleShellLinearMargin (shellAt j))

  inducedFlow : Cubic.InverseSquareMarginFlow cutoff
  inducedFlow = record
    { Cubic.InverseSquareMarginFlow.marginConstant = betaMargin
    ; Cubic.InverseSquareMarginFlow.coupling = coupling d
    ; Cubic.InverseSquareMarginFlow.inverseSquare = inverseSquare d
    ; Cubic.InverseSquareMarginFlow.couplingPositive = couplingPositive d
    ; Cubic.InverseSquareMarginFlow.inverseSquareRelation = inverseSquareRelation d
    ; Cubic.InverseSquareMarginFlow.couplingMonotone = couplingMonotone d
    ; Cubic.InverseSquareMarginFlow.marginStep = inverseSquareMargin
    }

  cubicSumBound : ∀ K → K ℕ.≤ cutoff →
    betaMargin * Cubic.sumCubes (coupling d) K ≤ Cubic.twoℚ * tubeWidth d
  cubicSumBound =
    Cubic.Flow.cubicSumInTube inducedFlow
      (ℚP.<⇒≤ betaMarginPositive) (couplingTube d)

  module Tuning
    (derivativeBound : ℚ)
    (derivativeNonNegative : 0ℚ ≤ derivativeBound)
    (sensitivity : Nat → ℚ)
    (sensitivityCubic : ∀ j → sensitivity j
      ≤ (Cubic.halfℚ * derivativeBound)
          * (coupling d j * coupling d j * coupling d j))
    (contractionGate : derivativeBound * tubeWidth d < betaMargin)
    where

    sensitivityData : Shooting.CumulativeSensitivityData cutoff
    sensitivityData = record
      { Shooting.CumulativeSensitivityData.marginConstant = betaMargin
      ; Shooting.CumulativeSensitivityData.derivativeBound = derivativeBound
      ; Shooting.CumulativeSensitivityData.tubeWidth = tubeWidth d
      ; Shooting.CumulativeSensitivityData.coupling = coupling d
      ; Shooting.CumulativeSensitivityData.sensitivity = sensitivity
      ; Shooting.CumulativeSensitivityData.marginPositive = betaMarginPositive
      ; Shooting.CumulativeSensitivityData.derivativeNonNegative = derivativeNonNegative
      ; Shooting.CumulativeSensitivityData.cubicSumBound = cubicSumBound
      ; Shooting.CumulativeSensitivityData.sensitivityCubic = sensitivityCubic
      ; Shooting.CumulativeSensitivityData.contractionGate = contractionGate
      }

    cumulativeSensitivityBelowOne : ∀ K → K ℕ.≤ cutoff →
      Shooting.sum₀ sensitivity K < 1ℚ
    cumulativeSensitivityBelowOne =
      Shooting.Sensitivity.cumulativeSensitivityBelowOne sensitivityData

module BothGatesWitness where

  witnessCoupling witnessInverseSquare : Nat → ℚ
  witnessCoupling zero = + 1 / 2
  witnessCoupling (suc _) = 1ℚ
  witnessInverseSquare zero = + 4 / 1
  witnessInverseSquare (suc _) = 1ℚ

  witnessData : RowAGateData 1
  witnessData = record
    { gaussianFloor = + 3 / 1
    ; interactionConstant = 1ℚ
    ; couplingCap = 1ℚ
    ; tubeWidth = + 1 / 2
    ; coupling = witnessCoupling
    ; betaGauss = λ _ → + 3 / 1
    ; betaInteraction = λ _ → 0ℚ
    ; inverseSquare = witnessInverseSquare
    ; interactionConstantNN = toWitness {a? = 0ℚ ℚP.≤? 1ℚ} _
    ; couplingCapNN = toWitness {a? = 0ℚ ℚP.≤? 1ℚ} _
    ; couplingPositive = positive?
    ; couplingBelowCap = cap
    ; gaussianLower = λ _ → ℚP.≤-refl
    ; interactionLower = interaction
    ; inverseSquareRelation = relation
    ; couplingMonotone = monotone
    ; betaIsInverseSquareStep = betaStep
    ; couplingTube = tube
    ; signGate = toWitness {a? = (1ℚ * 1ℚ) ℚP.<? (+ 3 / 1)} _
    }
    where
      positive? : ∀ j → 0ℚ < witnessCoupling j
      positive? zero = toWitness {a? = 0ℚ ℚP.<? (+ 1 / 2)} _
      positive? (suc _) = toWitness {a? = 0ℚ ℚP.<? 1ℚ} _

      cap : ∀ j → witnessCoupling j ≤ 1ℚ
      cap zero = toWitness {a? = (+ 1 / 2) ℚP.≤? 1ℚ} _
      cap (suc _) = ℚP.≤-refl

      interaction : ∀ j → - (1ℚ * witnessCoupling j) ≤ 0ℚ
      interaction zero = toWitness {a? = (- (1ℚ * (+ 1 / 2))) ℚP.≤? 0ℚ} _
      interaction (suc _) = toWitness {a? = (- (1ℚ * 1ℚ)) ℚP.≤? 0ℚ} _

      relation : ∀ j →
        witnessInverseSquare j * (witnessCoupling j * witnessCoupling j) ≡ 1ℚ
      relation zero = refl
      relation (suc _) = refl

      monotone : ∀ j → witnessCoupling j ≤ witnessCoupling (suc j)
      monotone zero = toWitness {a? = (+ 1 / 2) ℚP.≤? 1ℚ} _
      monotone (suc _) = ℚP.≤-refl

      betaStep : ∀ j → j ℕ.< 1 →
        (+ 3 / 1) + 0ℚ ≡ witnessInverseSquare j - witnessInverseSquare (suc j)
      betaStep zero _ = refl
      betaStep (suc _) (ℕ.s≤s ())

      tube : ∀ K → witnessCoupling K - witnessCoupling zero ≤ + 1 / 2
      tube zero = toWitness {a? = ((+ 1 / 2) - (+ 1 / 2)) ℚP.≤? (+ 1 / 2)} _
      tube (suc _) = toWitness {a? = (1ℚ - (+ 1 / 2)) ℚP.≤? (+ 1 / 2)} _

  open Gates witnessData

  witnessSensitivity : Nat → ℚ
  witnessSensitivity j =
    (Cubic.halfℚ * (+ 2 / 1))
      * (witnessCoupling j * witnessCoupling j * witnessCoupling j)

  open Tuning (+ 2 / 1)
    (toWitness {a? = 0ℚ ℚP.≤? (+ 2 / 1)} _)
    witnessSensitivity
    (λ _ → ℚP.≤-refl)
    (toWitness {a? = ((+ 2 / 1) * (+ 1 / 2)) ℚP.<? betaMargin} _)

  witnessBelowOne : Shooting.sum₀ witnessSensitivity 1 < 1ℚ
  witnessBelowOne = cumulativeSensitivityBelowOne 1 ℕP.≤-refl
