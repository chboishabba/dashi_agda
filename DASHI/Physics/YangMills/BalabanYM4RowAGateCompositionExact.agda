module DASHI.Physics.YangMills.BalabanYM4RowAGateCompositionExact where

------------------------------------------------------------------------
-- ROW A, COMPOSITION OF THE TWO NUMERICAL GATES
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I.", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- WHAT THIS MODULE DOES.  Three row-A modules are joined here along the one
-- identification that makes them a single mechanism: in the running
-- inverse-coupling variable
--
--     u_j = g_j^{-2},
--
-- the shell beta increment *is* the inverse-square step,
--
--     beta_j = u_j - u_{j+1}.
--
-- Consequently:
--
--   * the shell-local sign estimate of
--     `BalabanYM4LinearInteractionBetaMarginExact`
--     (beta_{Z,j} >= b_-, beta_{Int,j} >= -C g_{j-1}, g_{j-1} <= gamma)
--     supplies exactly the positive inverse-square margin
--
--         b_*  =  b_- - C gamma  >  0        (gate 1:  C gamma < b_-)
--
--     required by the cubic drift telescope of
--     `BalabanYM4CubicCouplingDriftTelescopeExact`; hence
--
--         (b_- - C gamma) sum_{j<K} g_j^3  <=  2 (g_K - g_0)  <=  2 gamma_tube,
--
--     uniformly in the number of shells;
--
--   * and the shooting gate of
--     `BalabanYM4ShootingSensitivityFromCubicDriftExact` then closes with the
--     *same* constant:
--
--         L gamma_tube  <  b_- - C gamma      (gate 2)
--     ==> cumulative shooting sensitivity  <  1, uniformly in the cutoff.
--
-- So row A's remaining content is exactly its three analytic producers
-- (b_- > 0 for the literal constrained Gaussian determinant; the uniform
-- differentiated interaction constant C; the uniform coupling derivative L)
-- plus the two displayed numerical gates and the identification of these
-- sequences with the literal Bałaban trajectory.  None of those is proved
-- here: row A stays open and the frozen research count stays at 4.
--
-- Exact rational arithmetic; no postulate, no hole, no receipt.  Checked with
-- `agda --safe`.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕP
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _-_; _/_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import Relation.Nullary.Decidable using (toWitness)

open import DASHI.Physics.YangMills.BalabanYM4LinearInteractionBetaMarginExact
  as ShellMargin
  using (ShellLinearInteractionData; sum₀)
open import DASHI.Physics.YangMills.BalabanYM4CubicCouplingDriftTelescopeExact
  as CubicDrift
  using (InverseSquareMarginFlow; sumCubes; twoℚ; halfℚ)
open import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact
  as Shooting
  using (CumulativeSensitivityData)

record RowAGateData (cutoff : Nat) : Set where
  field
    shellData : ShellLinearInteractionData

  open ShellLinearInteractionData shellData public

  field
    coupling inverseSquare : Nat → ℚ
    tubeWidth              : ℚ

    couplingPositive : ∀ j → 0ℚ < coupling j
    inverseSquareRelation :
      ∀ j → inverseSquare j * (coupling j * coupling j) ≡ 1ℚ
    couplingMonotone : ∀ j → coupling j ≤ coupling (suc j)
    betaIsInverseSquareStep :
      ∀ j → j ℕ.< cutoff → beta j ≡ inverseSquare j - inverseSquare (suc j)
    couplingTube : ∀ K → coupling K - coupling 0 ≤ tubeWidth
    signGate : interactionSlope * couplingCap < gaussianFloor

module Gates {cutoff : Nat} (d : RowAGateData cutoff) where

  open RowAGateData d

  betaMargin : ℚ
  betaMargin = ShellMargin.Shell.shellMargin shellData

  betaMarginPositive : 0ℚ < betaMargin
  betaMarginPositive = ShellMargin.Shell.shellMarginPositive shellData signGate

  inverseSquareMargin :
    ∀ j → j ℕ.< cutoff → betaMargin ≤ inverseSquare j - inverseSquare (suc j)
  inverseSquareMargin j j<cutoff =
    subst (λ z → betaMargin ≤ z) (betaIsInverseSquareStep j j<cutoff)
      (ShellMargin.Shell.shellBetaLower shellData j)

  inducedFlow : InverseSquareMarginFlow cutoff
  inducedFlow = record
    { marginConstant = betaMargin
    ; coupling = coupling
    ; inverseSquare = inverseSquare
    ; couplingPositive = couplingPositive
    ; inverseSquareRelation = inverseSquareRelation
    ; couplingMonotone = couplingMonotone
    ; marginStep = inverseSquareMargin
    }

  cubicSumBound :
    ∀ K → K ℕ.≤ cutoff →
    betaMargin * sumCubes coupling K ≤ twoℚ * tubeWidth
  cubicSumBound = CubicDrift.Flow.cubicSumInTube inducedFlow couplingTube

  module Tuning
    (derivativeBound : ℚ)
    (derivativeNonNegative : 0ℚ ≤ derivativeBound)
    (sensitivity : Nat → ℚ)
    (sensitivityCubic :
      ∀ j → sensitivity j
            ≤ (halfℚ * derivativeBound) * (coupling j * coupling j * coupling j))
    (contractionGate : derivativeBound * tubeWidth < betaMargin)
    where

    sensitivityData : CumulativeSensitivityData cutoff
    sensitivityData = record
      { marginConstant = betaMargin
      ; derivativeBound = derivativeBound
      ; tubeWidth = tubeWidth
      ; coupling = coupling
      ; sensitivity = sensitivity
      ; marginPositive = betaMarginPositive
      ; derivativeNonNegative = derivativeNonNegative
      ; cubicSumBound = cubicSumBound
      ; sensitivityCubic = sensitivityCubic
      ; contractionGate = contractionGate
      }

    cumulativeSensitivityBelowOne :
      ∀ K → K ℕ.≤ cutoff → sum₀ sensitivity K < 1ℚ
    cumulativeSensitivityBelowOne =
      Shooting.Sensitivity.cumulativeSensitivityBelowOne sensitivityData

module BothGatesWitness where

  witnessCoupling witnessInverseSquare : Nat → ℚ
  witnessCoupling zero = + 1 / 2
  witnessCoupling (suc _) = 1ℚ
  witnessInverseSquare zero = + 4 / 1
  witnessInverseSquare (suc _) = 1ℚ

  witnessShellData : ShellLinearInteractionData
  witnessShellData = record
    { gaussianFloor = + 3 / 1
    ; interactionSlope = 1ℚ
    ; couplingCap = 1ℚ
    ; beta = λ _ → + 3 / 1
    ; betaGauss = λ _ → + 3 / 1
    ; betaInt = λ _ → 0ℚ
    ; priorCoupling = λ _ → 0ℚ
    ; betaDecomposition = λ _ → refl
    ; gaussianLower = λ _ → ℚP.≤-refl
    ; interactionLinearLower = λ _ → toWitness {a? = (ℚ.- (1ℚ * 0ℚ)) ℚP.≤? 0ℚ} _
    ; slopeNonNegative = toWitness {a? = 0ℚ ℚP.≤? 1ℚ} _
    ; priorCouplingNonNegative = λ _ → ℚP.≤-refl
    ; priorCouplingCapped = λ _ → toWitness {a? = 0ℚ ℚP.≤? 1ℚ} _
    }

  witnessGateData : RowAGateData 1
  witnessGateData = record
    { shellData = witnessShellData
    ; coupling = witnessCoupling
    ; inverseSquare = witnessInverseSquare
    ; tubeWidth = + 1 / 2
    ; couplingPositive = positive?
    ; inverseSquareRelation = relation
    ; couplingMonotone = monotone
    ; betaIsInverseSquareStep = step
    ; couplingTube = tube
    ; signGate = toWitness {a? = (1ℚ * 1ℚ) ℚP.<? (+ 3 / 1)} _
    }
    where
      positive? : ∀ j → 0ℚ < witnessCoupling j
      positive? zero = toWitness {a? = 0ℚ ℚP.<? (+ 1 / 2)} _
      positive? (suc _) = toWitness {a? = 0ℚ ℚP.<? 1ℚ} _

      relation :
        ∀ j → witnessInverseSquare j * (witnessCoupling j * witnessCoupling j) ≡ 1ℚ
      relation zero = refl
      relation (suc _) = refl

      monotone : ∀ j → witnessCoupling j ≤ witnessCoupling (suc j)
      monotone zero = toWitness {a? = (+ 1 / 2) ℚP.≤? 1ℚ} _
      monotone (suc _) = ℚP.≤-refl

      step :
        ∀ j → j ℕ.< 1 →
        (+ 3 / 1) ≡ witnessInverseSquare j - witnessInverseSquare (suc j)
      step zero _ = refl
      step (suc _) (ℕ.s≤s ())

      tube : ∀ K → witnessCoupling K - witnessCoupling 0 ≤ + 1 / 2
      tube zero = toWitness {a? = ((+ 1 / 2) - (+ 1 / 2)) ℚP.≤? (+ 1 / 2)} _
      tube (suc _) = toWitness {a? = (1ℚ - (+ 1 / 2)) ℚP.≤? (+ 1 / 2)} _

  open Gates witnessGateData

  witnessSensitivity : Nat → ℚ
  witnessSensitivity j =
    (halfℚ * (+ 2 / 1))
      * (witnessCoupling j * witnessCoupling j * witnessCoupling j)

  open Tuning (+ 2 / 1)
    (toWitness {a? = 0ℚ ℚP.≤? (+ 2 / 1)} _)
    witnessSensitivity
    (λ _ → ℚP.≤-refl)
    (toWitness {a? = ((+ 2 / 1) * (+ 1 / 2)) ℚP.<? betaMargin} _)

  witnessBelowOne : sum₀ witnessSensitivity 1 < 1ℚ
  witnessBelowOne = cumulativeSensitivityBelowOne 1 ℕP.≤-refl
