{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCMP109WilsonDifferenceOrientationExact where

-- Reuse CMP109's actual UV-oriented source recurrence.  The physical beta
-- is u_k - u_(k+1), NOT u_(k+1)-u_k and NOT the absolute Wilson coefficient.
-- This module does not postulate the identity: the first theorem follows
-- directly from the source recurrence and rational normalization.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

sourceBetaIsBackwardDifference :
  (trajectory : Flow.SourceNormalizedCouplingTrajectory) →
  ∀ k →
  Flow.beta trajectory (suc k)
  ≡ Flow.inverseCoupling trajectory k
    - Flow.inverseCoupling trajectory (suc k)
sourceBetaIsBackwardDifference trajectory k =
  sym (trans
    (cong (_- Flow.inverseCoupling trajectory (suc k))
      (Flow.sourceRecurrence trajectory k))
    (ℚRing.solve-∀
      (Flow.inverseCoupling trajectory (suc k))
      (Flow.beta trajectory (suc k))))

-- The same result can be transported to the CMP119 Wilson coefficient
-- after identifying THAT coefficient's difference with the SAME inverse
-- coupling history. This uses a node-level interpretation, not a new
-- increment axiom.

sourceBetaIsWilsonCoefficientDifference :
  (trajectory : Flow.SourceNormalizedCouplingTrajectory)
  (wilsonCoefficient : Nat → ℚ)
  (wilsonIsSourceInverse : ∀ k →
    wilsonCoefficient k ≡ Flow.inverseCoupling trajectory k) →
  ∀ k →
  Flow.beta trajectory (suc k)
  ≡ wilsonCoefficient k - wilsonCoefficient (suc k)
sourceBetaIsWilsonCoefficientDifference trajectory wilsonCoefficient
    wilsonIsSourceInverse k =
  trans
    (sourceBetaIsBackwardDifference trajectory k)
    (cong₂ _-_
      (sym (wilsonIsSourceInverse k))
      (sym (wilsonIsSourceInverse (suc k))))
  where
    open import Relation.Binary.PropositionalEquality using (cong₂)

-- The Wilson coefficient of the complete source action is a NODE
-- coordinate. A selected T4 one-step action is a separate EDGE object;
-- Eq. (2.23) alone does not make them definitionally equal.
