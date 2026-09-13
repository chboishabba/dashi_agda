{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA2DirectMarginalDerivativeRound229Exact where

------------------------------------------------------------------------
-- ROUND229 / A2 DOES NOT NEED THE WHOLE MIXED-CAUCHY PACKAGE
--
-- The marginal history consumer uses only the cutoff-uniform local derivative
-- coefficient L_int for the literal finite-g beta contribution.  The existing
-- mixed normalized-interaction Cauchy package is a strong producer of L_int,
-- but it is not the least-privilege A2 contract.
--
-- On the inverse-square coordinate u = g^-2,
--
--   |d g / d u| = g^3 / 2,
--
-- hence the marginal shell sensitivity is
--
--   q_marg(j) = (L_int / 2) g_j^3.
--
-- The already-owned cubic telescope turns the physical positive-beta tube and
-- the single gate L_int * tubeWidth < margin into a cutoff-uniform cumulative
-- sensitivity < 1.  No Z/Z1/Z2/G0/G1/G2 carrier is required by this consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕP
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4CubicCouplingDriftTelescopeExact as Cubic
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Shoot

record DirectMarginalBetaDerivativeData (cutoff : Nat) : Set₁ where
  field
    localDerivativeConstant : ℚ
    localDerivativeConstantNonnegative : 0ℚ ≤ localDerivativeConstant

    marginConstant tubeWidth : ℚ
    coupling : Nat → ℚ

    marginPositive : 0ℚ < marginConstant

    cubicSumBound :
      ∀ K → K ℕ.≤ cutoff →
      marginConstant * Cubic.sumCubes coupling K
      ≤ Cubic.twoℚ * tubeWidth

    marginalContractionGate :
      localDerivativeConstant * tubeWidth < marginConstant

open DirectMarginalBetaDerivativeData public

marginalSensitivity :
  ∀ {cutoff} → DirectMarginalBetaDerivativeData cutoff → Nat → ℚ
marginalSensitivity dataSet j =
  (Cubic.halfℚ * localDerivativeConstant dataSet)
    * Cubic.cube (coupling dataSet j)

asCumulativeSensitivityData :
  ∀ {cutoff} →
  DirectMarginalBetaDerivativeData cutoff →
  Shoot.CumulativeSensitivityData cutoff
asCumulativeSensitivityData dataSet = record
  { Shoot.CumulativeSensitivityData.marginConstant = marginConstant dataSet
  ; Shoot.CumulativeSensitivityData.derivativeBound = localDerivativeConstant dataSet
  ; Shoot.CumulativeSensitivityData.tubeWidth = tubeWidth dataSet
  ; Shoot.CumulativeSensitivityData.coupling = coupling dataSet
  ; Shoot.CumulativeSensitivityData.sensitivity = marginalSensitivity dataSet
  ; Shoot.CumulativeSensitivityData.marginPositive = marginPositive dataSet
  ; Shoot.CumulativeSensitivityData.derivativeNonNegative =
      localDerivativeConstantNonnegative dataSet
  ; Shoot.CumulativeSensitivityData.cubicSumBound = cubicSumBound dataSet
  ; Shoot.CumulativeSensitivityData.sensitivityCubic = λ _ → ℚP.≤-refl
  ; Shoot.CumulativeSensitivityData.contractionGate = marginalContractionGate dataSet
  }

marginalCumulativeSensitivityBelowOne :
  ∀ {cutoff}
    (dataSet : DirectMarginalBetaDerivativeData cutoff)
    K → K ℕ.≤ cutoff →
  Shoot.sum₀ (marginalSensitivity dataSet) K < 1ℚ
marginalCumulativeSensitivityBelowOne dataSet K K≤cutoff =
  let module Paid = Shoot.Sensitivity (asCumulativeSensitivityData dataSet)
  in Paid.cumulativeSensitivityBelowOne K K≤cutoff

marginalFullPrefixBelowOne :
  ∀ {cutoff}
    (dataSet : DirectMarginalBetaDerivativeData cutoff) →
  Shoot.sum₀ (marginalSensitivity dataSet) cutoff < 1ℚ
marginalFullPrefixBelowOne {cutoff} dataSet =
  marginalCumulativeSensitivityBelowOne dataSet cutoff ℕP.≤-refl

a2DirectMarginalDerivativeCompilerLevel : ProofLevel
a2DirectMarginalDerivativeCompilerLevel = machineChecked

-- Least-privilege physical source leaf for this consumer:
-- prove a cutoff/volume/scale-uniform bound on the literal local finite-g beta
-- derivative on the same generated history.  The mixed-Cauchy package remains
-- a stronger producer of this scalar theorem, not a required A2 primitive.
literalCMP109LocalBetaDerivativeBoundLevel : ProofLevel
literalCMP109LocalBetaDerivativeBoundLevel = conditional
