module DASHI.Physics.Closure.NSTriadKNInitialCriticalRealizationToR421Round512Exact where

------------------------------------------------------------------------
-- ROUND512 / INITIAL-CRITICAL REALIZATION -> R421 CEILING
--
-- R509-R511 isolate the third consumer-visible coordinate omitted by R508:
-- R421 needs a cutoff-uniform initial-critical ceiling, while R240 supplies only
-- one common initial Fourier datum.  This owner installs the smallest safe
-- compiler between those surfaces.
--
-- No canonical H^(1/2) weight is invented here.  A caller must provide:
--
--   * one explicit initial-data critical functional on each cutoff;
--   * a SAME-OBJECT theorem identifying the R414 slice's `initialCritical`
--     with that functional;
--   * one cutoff-independent ceiling for that functional.
--
-- Only then may the R421 `uniformInitialCritical` field be inhabited.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNSignedHeatCrossToR410Round415Exact as R415
import DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact as R414
import DASHI.Physics.Closure.NSTriadKNSignedHeatCrossDirectToCriticalBarrierRound421Exact as R421

F : C3.RealField _
F = Rational.rationalRealField

module InitialCritical
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
  module Unified = R414.Unified
    Time initialTime integrateTo DerivativeOf
  module Barrier = R421.DirectBarrier
    Time initialTime integrateTo DerivativeOf

  record InitialCriticalRealization
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (terminal : Time)
      (sliceData :
        (cutoff : Nat) →
        Unified.CriticalSliceOnLiteralR406 T R terminal cutoff) : Set where
    constructor initial-critical-realization
    field
      initialDatumCritical : Nat → ℚ
      initialCriticalSameObject :
        (cutoff : Nat) →
        Unified.initialCritical (sliceData cutoff)
        ≡ initialDatumCritical cutoff
      cutoffIndependentInitialCeiling : ℚ
      initialDatumCriticalBound :
        (cutoff : Nat) →
        initialDatumCritical cutoff ≤ cutoffIndependentInitialCeiling

  open InitialCriticalRealization public

  realizationPaysUniformInitialCritical :
    ∀ {T R terminal sliceData} →
    (I : InitialCriticalRealization T R terminal sliceData) →
    (cutoff : Nat) →
    Unified.initialCritical (sliceData cutoff)
    ≤ cutoffIndependentInitialCeiling I
  realizationPaysUniformInitialCritical {sliceData = sliceData} I cutoff =
    subst
      (λ x → x ≤ cutoffIndependentInitialCeiling I)
      (sym (initialCriticalSameObject I cutoff))
      (initialDatumCriticalBound I cutoff)

  attachInitialCriticalRealization :
    ∀ {T R terminal}
      (heatCrossPayment : Heat.IntegratedSignedHeatCrossPayment T R)
      (sliceData :
        (cutoff : Nat) →
        Unified.CriticalSliceOnLiteralR406 T R terminal cutoff) →
      InitialCriticalRealization T R terminal sliceData →
      Barrier.SignedHeatCriticalData T R terminal
  attachInitialCriticalRealization heatCrossPayment sliceData I = record
    { Barrier.heatCrossPayment = heatCrossPayment
    ; Barrier.sliceData = sliceData
    ; Barrier.uniformInitialCeiling = cutoffIndependentInitialCeiling I
    ; Barrier.uniformInitialCritical = realizationPaysUniformInitialCritical I
    }

round512InitialCriticalSameObjectReceiptRequired : Bool
round512InitialCriticalSameObjectReceiptRequired = true

round512CommonInitialDatumAloneAcceptedAsCeiling : Bool
round512CommonInitialDatumAloneAcceptedAsCeiling = false

round512CompilerIntroducesNewPDEEstimate : Bool
round512CompilerIntroducesNewPDEEstimate = false

round512InitialCriticalRealizationClosed : Bool
round512InitialCriticalRealizationClosed = false

round512ClayPromotion : Bool
round512ClayPromotion = false

round512InitialCriticalSameObjectReceiptRequiredIsTrue :
  round512InitialCriticalSameObjectReceiptRequired ≡ true
round512InitialCriticalSameObjectReceiptRequiredIsTrue = refl

round512CommonInitialDatumAloneAcceptedAsCeilingIsFalse :
  round512CommonInitialDatumAloneAcceptedAsCeiling ≡ false
round512CommonInitialDatumAloneAcceptedAsCeilingIsFalse = refl

round512CompilerIntroducesNewPDEEstimateIsFalse :
  round512CompilerIntroducesNewPDEEstimate ≡ false
round512CompilerIntroducesNewPDEEstimateIsFalse = refl

round512ClayPromotionIsFalse : round512ClayPromotion ≡ false
round512ClayPromotionIsFalse = refl
