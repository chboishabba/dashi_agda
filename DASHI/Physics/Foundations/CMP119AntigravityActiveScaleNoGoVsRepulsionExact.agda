{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityActiveScaleNoGoVsRepulsionExact where

------------------------------------------------------------------------
-- Physical max-cut: on the SAME CMP109 active-scale coupling and Lorentzian
-- E^2+B^2 readout, the weak-coupling trace-energy decomposition yields
-- nonnegative active stress. Therefore strict negative active stress cannot
-- simultaneously hold for that same selected source.
--
-- A counterexample must violate at least one premise: source attachment,
-- Lorentzian continuation, threshold, or nonstandard stress contribution.
-- This is not a proof of repulsion; it is a source-level incompatibility.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

import DASHI.Physics.Foundations.CMP119AntigravityActiveScaleInverseCouplingNoGoExact as Active
import DASHI.Physics.Foundations.CMP119AntigravityLorentzianF2ContinuationExact as Lorentz
import DASHI.Physics.Foundations.CMP119AntigravityWeakCouplingTraceEnergyNoGoExact as NoGo
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as Finite
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

sameActiveSourceCannotBeStrictlyNegative :
  ∀ {trajectory Mode Atom betaData}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    (continuation : Lorentz.LorentzianF2ContinuationReceipt)
    (certificate : Active.ActiveScaleTraceThresholdCertificate history)
    (scale : Nat)
    (active : History.ActiveScale history scale)
    (sourceActiveStress : ℚ) →
    sourceActiveStress ≡
      NoGo.activeStress
        (Active.activeScaleNoGoData
          continuation certificate scale active) →
    ¬ (sourceActiveStress < 0ℚ)
sameActiveSourceCannotBeStrictlyNegative
    continuation certificate scale active sourceActiveStress sameObject negative =
  ℚP.<⇒≱
    (subst
      (λ value → value < 0ℚ)
      sameObject negative)
    (Active.activeCMP119ScaleTraceAnomalyNoGo
      continuation certificate scale active)
