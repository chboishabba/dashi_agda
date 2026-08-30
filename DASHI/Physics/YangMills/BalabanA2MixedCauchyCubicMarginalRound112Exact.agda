{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA2MixedCauchyCubicMarginalRound112Exact where

------------------------------------------------------------------------
-- ROUND112 A2: THE MARGINAL SAME-HISTORY SENSITIVITY IS ALREADY PAID
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- BIDI role.
--
-- Round103 left A2 as an abstract shellwise same-history sensitivity.  The
-- repository already owns both quantitative pieces needed for the MARGINAL
-- coupling contribution:
--
--   * the normalized mixed-Cauchy package gives a cutoff-independent
--       |d_g beta_int| <= L_int;
--   * the inverse-square coordinate u = g^{-2} contributes the canonical
--       |d g / d u| = g^3 / 2;
--   * the positive-beta flow supplies the cutoff-uniform cubic telescope.
--
-- Hence the marginal shell coefficient is literally
--
--       q_marg(j) = (L_int / 2) g_j^3,
--
-- and the existing cubic-telescope theorem proves
--
--       sum_{j<K} q_marg(j) < 1
--
-- from the SAME small-coupling gate L_int * gamma < b_*.
--
-- This module deliberately does not assign geometric forgetting to the
-- marginal coupling.  After this theorem the surviving A2 source task is only
-- the genuinely irrelevant/history response plus the exact decomposition of
-- the physical CMP109 beta difference into marginal + irrelevant pieces.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕP
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4CubicCouplingDriftTelescopeExact as Cubic
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Shoot
import DASHI.Physics.YangMills.BalabanYM4RowACauchySourceToCanonicalGateExact as Cauchy

open Cubic using (halfℚ; sumCubes)

record MixedCauchyMarginalSensitivityData (cutoff : Nat) : Set₁ where
  field
    -- The literal normalized interaction package.  Its local derivative
    -- constant is definitionally the one proved from G0/G1/G2 Cauchy data.
    source : Cauchy.RowACauchySourceConstants

    marginConstant tubeWidth : ℚ
    coupling : Nat → ℚ

    marginPositive : 0ℚ < marginConstant

    -- Same physical positive-beta trajectory used by the Row-A tube.
    cubicSumBound :
      ∀ K → K ℕ.≤ cutoff →
      marginConstant * sumCubes coupling K ≤
        Cubic.twoℚ * tubeWidth

    -- This is exactly the canonical marginal smallness gate; no new L is
    -- introduced here.
    marginalContractionGate :
      Cauchy.sourceLocalDerivativeConstant source * tubeWidth
      < marginConstant

open MixedCauchyMarginalSensitivityData public

marginalSensitivity :
  ∀ {cutoff} → MixedCauchyMarginalSensitivityData cutoff → Nat → ℚ
marginalSensitivity dataSet j =
  (halfℚ * Cauchy.sourceLocalDerivativeConstant (source dataSet))
    * (coupling dataSet j * coupling dataSet j * coupling dataSet j)

asCumulativeSensitivityData :
  ∀ {cutoff} →
  MixedCauchyMarginalSensitivityData cutoff →
  Shoot.CumulativeSensitivityData cutoff
asCumulativeSensitivityData dataSet = record
  { Shoot.CumulativeSensitivityData.marginConstant = marginConstant dataSet
  ; Shoot.CumulativeSensitivityData.derivativeBound =
      Cauchy.sourceLocalDerivativeConstant (source dataSet)
  ; Shoot.CumulativeSensitivityData.tubeWidth = tubeWidth dataSet
  ; Shoot.CumulativeSensitivityData.coupling = coupling dataSet
  ; Shoot.CumulativeSensitivityData.sensitivity = marginalSensitivity dataSet
  ; Shoot.CumulativeSensitivityData.marginPositive = marginPositive dataSet
  ; Shoot.CumulativeSensitivityData.derivativeNonNegative =
      Cauchy.sourceLocalDerivativeConstantNonnegative (source dataSet)
  ; Shoot.CumulativeSensitivityData.cubicSumBound = cubicSumBound dataSet
  ; Shoot.CumulativeSensitivityData.sensitivityCubic = λ _ → ℚP.≤-refl
  ; Shoot.CumulativeSensitivityData.contractionGate = marginalContractionGate dataSet
  }

marginalCumulativeSensitivityBelowOne :
  ∀ {cutoff}
    (dataSet : MixedCauchyMarginalSensitivityData cutoff)
    K → K ℕ.≤ cutoff →
  Shoot.sum₀ (marginalSensitivity dataSet) K < 1ℚ
marginalCumulativeSensitivityBelowOne dataSet K K≤cutoff =
  let
    module Paid = Shoot.Sensitivity (asCumulativeSensitivityData dataSet)
  in
  Paid.cumulativeSensitivityBelowOne K K≤cutoff

marginalFullPrefixBelowOne :
  ∀ {cutoff}
    (dataSet : MixedCauchyMarginalSensitivityData cutoff) →
  Shoot.sum₀ (marginalSensitivity dataSet) cutoff < 1ℚ
marginalFullPrefixBelowOne {cutoff} dataSet =
  marginalCumulativeSensitivityBelowOne dataSet cutoff ℕP.≤-refl

------------------------------------------------------------------------
-- Authority boundary
------------------------------------------------------------------------

a2MixedCauchyMarginalSensitivityLevel : ProofLevel
a2MixedCauchyMarginalSensitivityLevel = machineChecked

-- The local/marginal derivative constant and its cubic summation are no longer
-- open A2 leaves.  The remaining physical statement is the SAME-history
-- decomposition of the literal CMP109 beta response into this marginal piece
-- and the already-localized irrelevant response.
literalCMP109MarginalPlusIrrelevantDecompositionLevel : ProofLevel
literalCMP109MarginalPlusIrrelevantDecompositionLevel = conditional
