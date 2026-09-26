{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityUnitThresholdClosesSU2NoGoExact where

open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Decidable using (toWitness)

import DASHI.Physics.Foundations.CMP119AntigravityTraceCoefficientInverseCouplingFirewallExact as Coeff

------------------------------------------------------------------------
-- 11/24 < 1
--
-- Once the physical anomaly normalization is bounded by the repository's
-- selected rational SU(2) threshold 11/24, any history proof u_* >= 1 is more
-- than sufficient for the active-scale weak-coupling no-go.
------------------------------------------------------------------------

su2NormalizedNoGoThresholdBelowOne :
  Coeff.selectedWeakCouplingNoGoThresholdRational < 1ℚ
su2NormalizedNoGoThresholdBelowOne =
  toWitness
    {a? =
      Coeff.selectedWeakCouplingNoGoThresholdRational
        ℚP.<? 1ℚ}
    _

su2NormalizedNoGoThresholdAtMostOne :
  Coeff.selectedWeakCouplingNoGoThresholdRational ≤ 1ℚ
su2NormalizedNoGoThresholdAtMostOne =
  ℚP.<⇒≤ su2NormalizedNoGoThresholdBelowOne

unitInverseThresholdPaysNormalizedSU2Threshold :
  ∀ {inverseThreshold : ℚ} →
  1ℚ ≤ inverseThreshold →
  Coeff.selectedWeakCouplingNoGoThresholdRational
  ≤ inverseThreshold
unitInverseThresholdPaysNormalizedSU2Threshold oneBelow =
  ℚP.≤-trans
    su2NormalizedNoGoThresholdAtMostOne
    oneBelow
