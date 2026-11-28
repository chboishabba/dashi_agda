module DASHI.Physics.YangMills.YMClayCMP102OriginalAbsoluteRateReceiverExact where

------------------------------------------------------------------------
-- CMP102 direct absolute-error receiver on the ACTUAL original Bishop
-- G_COUNT and SAME represented CMP109 A/B limit.
--
-- Reuses the already-written BishopVanishingDifferenceConvergenceExact
-- instead of requiring two independent signed squeeze hypotheses.
-- The only nontrivial remaining input is ONE original finite magnitude
-- certificate at every count, not a new convergence oracle.
--
-- No new real carrier, no postulate, no claim of native elaboration.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Real as R
import RealProperties as P
import Sequence as Seq

import DASHI.Analysis.BishopVanishingDifferenceConvergenceExact as Vanish
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original
import DASHI.Physics.YangMills.YMClayCMP102OriginalGeometricSqueezeReceiverExact as Rate
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half

-- Preserve the literal subtraction and absolute value of the pinned
-- Bishop Sequence vanishing-difference theorem. Neither a polynomial
-- replacement nor a hidden numerical approximation enters this bound.
originalAbsoluteRateBound :
  R.ℝ → Set
originalAbsoluteRateBound X =
  ∀ count →
    R._≤_
      (R.∣ R._-_ (Original.originalGPrefix X count) R.0ℝ ∣)
      (R.∣ Rate.originalGeometricRate count ∣)

-- The actual Bishop convergence proof is now obtained directly from
-- the ONE finite original-bound constructor. Every other analytic
-- receiver input is already supplied by its original owner.
originalGPrefixZeroFromAbsoluteRate :
  ∀ X →
  originalAbsoluteRateBound X →
  Seq._ConvergesTo_ (Original.originalGPrefix X) R.0ℝ
originalGPrefixZeroFromAbsoluteRate X finiteBound =
  Vanish.vanishingDifferenceConvergence
    (Original.constantConverges R.0ℝ)
    Rate.originalGeometricRateZero
    finiteBound

-- Original CMP109 same-source infinite series and uniqueness of the
-- actual Bishop limit, not a separate formal power-series equation.
originalGZeroFromAbsoluteRate :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  originalAbsoluteRateBound X →
  R._≃_ (Original.originalG X inside) R.0ℝ
originalGZeroFromAbsoluteRate X inside finiteBound =
  Original.originalGZeroFromOriginalPrefixConvergence
    X inside
    (originalGPrefixZeroFromAbsoluteRate X finiteBound)
