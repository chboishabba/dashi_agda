module DASHI.Physics.Closure.NSTriadKNQuadraticCompanionSignedHeatToBarrierRound423Exact where

------------------------------------------------------------------------
-- ROUND423 / HIGHEST-ALPHA SAME-OBJECT TARGET:
-- QUADRATIC COMPANION FORCING -> SIGNED HEAT CROSS -> CRITICAL BARRIER
--
-- R200 fixes the homogeneity issue: the A-facing companion is the quadratic
-- R167/R145 slot kernel, not the higher-degree dynamic energy owner.  R420
-- identifies the literal R329 nested outer slot as forcing inserted into that
-- SAME quadratic companion.  R415 says a cutoff-uniform bound on the signed
-- pre-norm heat cross pays the literal R406 remainder.  R421 then sends that
-- same payment directly to the Round104 uniform critical barrier.
--
-- This owner removes the last naming ambiguity between those lanes.  The
-- discovery theorem is allowed to prove a cutoff-uniform bound on a signed
-- quadratic-companion forcing cross.  It must then prove pointwise equality
-- with R415's integrated signed heat cross on the same cutoff/time.  No
-- positive Wiener envelope, no alternate companion and no second remainder
-- estimate are accepted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNHeatNestedForcesQuadraticCompanionRound420Exact as R420
import DASHI.Physics.Closure.NSTriadKNSignedHeatCrossToR410Round415Exact as R415
import DASHI.Physics.Closure.NSTriadKNSignedHeatCrossDirectToCriticalBarrierRound421Exact as R421
import DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact as R414
import DASHI.Physics.Closure.NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact as Signed
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299

F : C3.RealField _
F = Rational.rationalRealField

module QuadraticCompanionBarrier
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Heat = R415.SignedHeatCross
    Time initialTime integrateTo DerivativeOf
  module Barrier = R421.DirectBarrier
    Time initialTime integrateTo DerivativeOf
  module Unified = R414.Unified
    Time initialTime integrateTo DerivativeOf

  record QuadraticCompanionSignedPayment
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      -- The analytic producer should define this directly from the signed
      -- forcing of the homogeneity-correct R167/R420 quadratic companion.
      integratedQuadraticCompanionCross : Nat → Time → ℚ
      cutoffIndependentCompanionBound : Time → ℚ

      -- Same-object weld to the pre-norm R299 heat-cross representation.
      integratedSignedHeatCross : Nat → Time → ℚ
      heatCrossIsQuadraticCompanionCross :
        (cutoff : Nat) (terminal : Time) →
        integratedSignedHeatCross cutoff terminal
        ≡ integratedQuadraticCompanionCross cutoff terminal

      -- Literal R406 remainder identity.  This is the existing R415 boundary,
      -- retained here so the final theorem cannot silently change remainder.
      literalR406RemainderIsFourSignedCross :
        (cutoff : Nat) (terminal : Time) →
        Heat.literalRemainderIntegral T R cutoff terminal
        ≡ R299.four * integratedSignedHeatCross cutoff terminal

      -- The novel cutoff-uniform estimate is stated on the quadratic
      -- companion cross, before any Wiener/l1 majorization.
      quadraticCompanionSignedBudget :
        (cutoff : Nat) (terminal : Time) →
        R299.four * integratedQuadraticCompanionCross cutoff terminal
        ≤ cutoffIndependentCompanionBound terminal

  open QuadraticCompanionSignedPayment public

  toIntegratedSignedHeatCrossPayment :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    QuadraticCompanionSignedPayment T R →
    Heat.IntegratedSignedHeatCrossPayment T R
  toIntegratedSignedHeatCrossPayment T R P = record
    { Heat.integratedSignedAggregateCross = integratedSignedHeatCross P
    ; Heat.cutoffIndependentCrossBound = cutoffIndependentCompanionBound P
    ; Heat.literalR406RemainderIsFourSignedCross =
        literalR406RemainderIsFourSignedCross P
    ; Heat.signedCrossBudget = λ cutoff terminal →
        subst
          (λ x → R299.four * x ≤ cutoffIndependentCompanionBound P terminal)
          (sym (heatCrossIsQuadraticCompanionCross P cutoff terminal))
          (quadraticCompanionSignedBudget P cutoff terminal)
    }

  record QuadraticCompanionCriticalData
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (terminal : Time) : Set₁ where
    field
      companionPayment : QuadraticCompanionSignedPayment T R
      sliceData :
        (cutoff : Nat) →
        Unified.CriticalSliceOnLiteralR406 T R terminal cutoff
      uniformInitialCeiling : ℚ
      uniformInitialCritical :
        (cutoff : Nat) →
        Unified.initialCritical (sliceData cutoff) ≤ uniformInitialCeiling

  open QuadraticCompanionCriticalData public

  toR421SignedHeatCriticalData :
    ∀ {T R terminal} →
    QuadraticCompanionCriticalData T R terminal →
    Barrier.SignedHeatCriticalData T R terminal
  toR421SignedHeatCriticalData {T} {R} D = record
    { Barrier.heatCrossPayment =
        toIntegratedSignedHeatCrossPayment T R (companionPayment D)
    ; Barrier.sliceData = sliceData D
    ; Barrier.uniformInitialCeiling = uniformInitialCeiling D
    ; Barrier.uniformInitialCritical = uniformInitialCritical D
    }

  quadraticCompanionPaymentBuildsUniformCriticalFamily :
    ∀ {T R terminal} →
    QuadraticCompanionCriticalData T R terminal →
    Signed.UniformSignedCriticalProductionFamily
  quadraticCompanionPaymentBuildsUniformCriticalFamily D =
    Barrier.signedHeatCrossBuildsUniformCriticalFamily
      (toR421SignedHeatCriticalData D)

  quadraticCompanionPaymentBuildsUniformCriticalBarrier :
    ∀ {T R terminal} →
    (D : QuadraticCompanionCriticalData T R terminal) →
    (cutoff : Nat) →
    let family = quadraticCompanionPaymentBuildsUniformCriticalFamily D in
    Signed.terminalCritical (Signed.slice family cutoff)
      + Signed.retainedViscosity (Signed.slice family cutoff)
          * Signed.criticalDissipation (Signed.slice family cutoff)
    ≤ Signed.uniformCriticalCeiling family
  quadraticCompanionPaymentBuildsUniformCriticalBarrier D cutoff =
    Barrier.signedHeatCrossBuildsUniformCriticalBarrier
      (toR421SignedHeatCriticalData D) cutoff

round423HomogeneityCorrectCompanionIsR167R420Lane : Bool
round423HomogeneityCorrectCompanionIsR167R420Lane = true

round423SignedHeatCrossMustEqualQuadraticCompanionCross : Bool
round423SignedHeatCrossMustEqualQuadraticCompanionCross = true

round423PositiveWienerEnvelopeRequired : Bool
round423PositiveWienerEnvelopeRequired = false

round423SecondRemainderEstimateRequired : Bool
round423SecondRemainderEstimateRequired = false

round423QuadraticCompanionSignedPaymentFeedsCriticalBarrier : Bool
round423QuadraticCompanionSignedPaymentFeedsCriticalBarrier = true

round423RemainingNovelProducerIsCutoffUniformSignedCompanionBudget : Bool
round423RemainingNovelProducerIsCutoffUniformSignedCompanionBudget = true

round423PositiveWienerEnvelopeRequiredIsFalse :
  round423PositiveWienerEnvelopeRequired ≡ false
round423PositiveWienerEnvelopeRequiredIsFalse = refl

round423QuadraticCompanionSignedPaymentFeedsCriticalBarrierIsTrue :
  round423QuadraticCompanionSignedPaymentFeedsCriticalBarrier ≡ true
round423QuadraticCompanionSignedPaymentFeedsCriticalBarrierIsTrue = refl
