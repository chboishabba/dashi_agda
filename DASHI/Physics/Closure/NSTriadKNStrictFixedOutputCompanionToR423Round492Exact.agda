module DASHI.Physics.Closure.NSTriadKNStrictFixedOutputCompanionToR423Round492Exact where

------------------------------------------------------------------------
-- ROUND492 / STRICT FIXED-OUTPUT -> R423 SAME-OBJECT FIREWALL
--
-- R487 is a correct scalar aggregation compiler, but R423's record stores its
-- `integratedQuadraticCompanionCross` as a field.  Therefore assigning the
-- fixed-output aggregate to that field by name alone is not enough to prove
-- that the scalar is the literal R420/R439 quadratic-companion observable.
--
-- This owner restores that missing same-object receipt.  A strict producer
-- supplies:
--
--   * the R487 fixed-output scalar/budget producer;
--   * the externally selected literal integrated quadratic-companion scalar;
--   * a theorem identifying the R487 aggregate with that literal scalar.
--
-- Only then do we construct the Clay-facing R423 payment.  The budget is
-- transported across the same-object equality; no new estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNQuadraticCompanionSignedHeatToBarrierRound423Exact as R423
import DASHI.Physics.Closure.NSTriadKNFixedOutputPaymentsToR423Round487Exact as R487

F : C3.RealField _
F = Rational.rationalRealField

module StrictFixedOutputToR423
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Base = R487.FixedOutputToR423
    Time initialTime integrateTo DerivativeOf
  module Clay = R423.QuadraticCompanionBarrier
    Time initialTime integrateTo DerivativeOf

  record StrictFixedOutputR423Producer
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      scalarProducer : Base.FixedOutputR423Producer T R

      literalIntegratedQuadraticCompanionCross : Nat → Time → ℚ

      fixedOutputAggregateIsLiteralCompanion :
        (cutoff : Nat) (terminal : Time) →
        Base.integratedFixedOutputCross scalarProducer cutoff terminal
        ≡ literalIntegratedQuadraticCompanionCross cutoff terminal

  open StrictFixedOutputR423Producer public

  strictProducerBuildsR423 :
    ∀ {T R} →
    StrictFixedOutputR423Producer T R →
    Clay.QuadraticCompanionSignedPayment T R
  strictProducerBuildsR423 P = record
    { Clay.integratedQuadraticCompanionCross =
        literalIntegratedQuadraticCompanionCross P
    ; Clay.cutoffIndependentCompanionBound =
        Base.cutoffIndependentCompanionBound (scalarProducer P)
    ; Clay.integratedSignedHeatCross =
        Base.integratedFixedOutputCross (scalarProducer P)
    ; Clay.heatCrossIsQuadraticCompanionCross =
        fixedOutputAggregateIsLiteralCompanion P
    ; Clay.literalR406RemainderIsFourSignedCross =
        Base.literalRemainderIsFourIntegratedFixedOutputCross
          (scalarProducer P)
    ; Clay.quadraticCompanionSignedBudget = λ cutoff terminal →
        subst
          (λ selected →
            R299.four * selected
            ≤ Base.cutoffIndependentCompanionBound
                (scalarProducer P) terminal)
          (fixedOutputAggregateIsLiteralCompanion P cutoff terminal)
          (Base.fixedOutputCrossBudget
            (scalarProducer P) cutoff terminal)
    }

------------------------------------------------------------------------
-- Trust / status boundary.
------------------------------------------------------------------------

round492R487ScalarAggregationCompilerReused : Bool
round492R487ScalarAggregationCompilerReused = true

round492ExternalSameObjectCompanionReceiptRequired : Bool
round492ExternalSameObjectCompanionReceiptRequired = true

round492CompilerIntroducesNewEstimate : Bool
round492CompilerIntroducesNewEstimate = false

round492LiteralIntegratedCompanionWeldClosed : Bool
round492LiteralIntegratedCompanionWeldClosed = false

round492PhysicalSignedSpacetimeEstimateClosed : Bool
round492PhysicalSignedSpacetimeEstimateClosed = false

round492CutoffUniformBudgetSumClosed : Bool
round492CutoffUniformBudgetSumClosed = false

round492R423SignedCompanionBudgetClosed : Bool
round492R423SignedCompanionBudgetClosed = false

round492ClayPromotion : Bool
round492ClayPromotion = false

round492R487ScalarAggregationCompilerReusedIsTrue :
  round492R487ScalarAggregationCompilerReused ≡ true
round492R487ScalarAggregationCompilerReusedIsTrue = refl

round492ExternalSameObjectCompanionReceiptRequiredIsTrue :
  round492ExternalSameObjectCompanionReceiptRequired ≡ true
round492ExternalSameObjectCompanionReceiptRequiredIsTrue = refl

round492CompilerIntroducesNewEstimateIsFalse :
  round492CompilerIntroducesNewEstimate ≡ false
round492CompilerIntroducesNewEstimateIsFalse = refl

round492ClayPromotionIsFalse : round492ClayPromotion ≡ false
round492ClayPromotionIsFalse = refl
