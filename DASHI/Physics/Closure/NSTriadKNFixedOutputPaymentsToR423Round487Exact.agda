module DASHI.Physics.Closure.NSTriadKNFixedOutputPaymentsToR423Round487Exact where

------------------------------------------------------------------------
-- ROUND487 / FIXED-OUTPUT SIGNED PAYMENTS -> EXACT R423 CLAY CONSUMER
--
-- R432 already proves the cardinality-free finite compiler
--
--   C_k <= B_k for each fixed output k
--     ==> sum_k C_k <= sum_k B_k.
--
-- R423 is the canonical shortest Clay-facing consumer: one cutoff-uniform
-- integrated signed quadratic-companion heat payment.  This file closes the
-- previously narrative seam between those two owners.
--
-- A producer supplies, for every cutoff and terminal time:
--
--   * the literal R406 remainder decomposed as 4 * sum_k C_k;
--   * theorem-bearing fixed-output payments C_k <= B_k;
--   * one cutoff-independent payment 4 * sum_k B_k <= B(T).
--
-- The compiler constructs the exact R423 QuadraticCompanionSignedPayment.
-- No cross-output coherence theorem, output-count factor, absolute value,
-- Schur/Wiener envelope, Cauchy operator bound, or R284 decomposition is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNSignedHeatCrossToR410Round415Exact as R415
import DASHI.Physics.Closure.NSTriadKNQuadraticCompanionSignedHeatToBarrierRound423Exact as R423
import DASHI.Physics.Closure.NSTriadKNFixedOutputSignedCrossAggregationRound432Exact as R432

F : C3.RealField _
F = Rational.rationalRealField

module FixedOutputToR423
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
  module Clay = R423.QuadraticCompanionBarrier
    Time initialTime integrateTo DerivativeOf

  record FixedOutputR423Producer
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      decomposition :
        Nat → Time → R432.FixedOutputRemainderDecomposition

      literalRemainderIsDecomposition :
        (cutoff : Nat) (terminal : Time) →
        Heat.literalRemainderIntegral T R cutoff terminal
        ≡ R432.globalWeightedRemainder (decomposition cutoff terminal)

      cutoffIndependentCompanionBound : Time → ℚ

      summedFibreBudgetsPaid :
        (cutoff : Nat) (terminal : Time) →
        R299.four
          * R432.sumFibreBudget
              (R432.payments (decomposition cutoff terminal))
        ≤ cutoffIndependentCompanionBound terminal

  open FixedOutputR423Producer public

  integratedFixedOutputCross :
    ∀ {T R} →
    FixedOutputR423Producer T R → Nat → Time → ℚ
  integratedFixedOutputCross P cutoff terminal =
    R432.sumSignedCross (R432.payments (decomposition P cutoff terminal))

  literalRemainderIsFourIntegratedFixedOutputCross :
    ∀ {T R}
      (P : FixedOutputR423Producer T R)
      (cutoff : Nat) (terminal : Time) →
    Heat.literalRemainderIntegral T R cutoff terminal
    ≡ R299.four * integratedFixedOutputCross P cutoff terminal
  literalRemainderIsFourIntegratedFixedOutputCross P cutoff terminal =
    trans
      (literalRemainderIsDecomposition P cutoff terminal)
      (R432.globalRemainderIsFourFibreCrosses
        (decomposition P cutoff terminal))

  fixedOutputCrossBudget :
    ∀ {T R}
      (P : FixedOutputR423Producer T R)
      (cutoff : Nat) (terminal : Time) →
    R299.four * integratedFixedOutputCross P cutoff terminal
    ≤ cutoffIndependentCompanionBound P terminal
  fixedOutputCrossBudget P cutoff terminal =
    let
      D = decomposition P cutoff terminal
      aggregate = R432.fixedOutputPaymentsBoundGlobalRemainder D
      asFourCross :
        R299.four * integratedFixedOutputCross P cutoff terminal
        ≤ R299.four * R432.sumFibreBudget (R432.payments D)
      asFourCross =
        subst
          (λ lower →
            lower ≤ R299.four * R432.sumFibreBudget (R432.payments D))
          (R432.globalRemainderIsFourFibreCrosses D)
          aggregate
    in
    ℚP.≤-trans asFourCross (summedFibreBudgetsPaid P cutoff terminal)

  fixedOutputProducerBuildsR423 :
    ∀ {T R} →
    FixedOutputR423Producer T R →
    Clay.QuadraticCompanionSignedPayment T R
  fixedOutputProducerBuildsR423 P = record
    { Clay.integratedQuadraticCompanionCross = integratedFixedOutputCross P
    ; Clay.cutoffIndependentCompanionBound =
        cutoffIndependentCompanionBound P
    ; Clay.integratedSignedHeatCross = integratedFixedOutputCross P
    ; Clay.heatCrossIsQuadraticCompanionCross = λ cutoff terminal → refl
    ; Clay.literalR406RemainderIsFourSignedCross =
        literalRemainderIsFourIntegratedFixedOutputCross P
    ; Clay.quadraticCompanionSignedBudget = fixedOutputCrossBudget P
    }

------------------------------------------------------------------------
-- Current producer frontier.
------------------------------------------------------------------------

round487R432ToR423CompilerClosed : Bool
round487R432ToR423CompilerClosed = true

round487CrossOutputCoherenceRequired : Bool
round487CrossOutputCoherenceRequired = false

round487OutputCardinalityFactorIntroduced : Bool
round487OutputCardinalityFactorIntroduced = false

round487AbsoluteValueInserted : Bool
round487AbsoluteValueInserted = false

round487SchurOrCauchyRouteMandatory : Bool
round487SchurOrCauchyRouteMandatory = false

round487R284DecompositionMandatory : Bool
round487R284DecompositionMandatory = false

round487PhysicalFixedOutputPaymentsClosed : Bool
round487PhysicalFixedOutputPaymentsClosed = false

round487CutoffUniformFibreBudgetSumClosed : Bool
round487CutoffUniformFibreBudgetSumClosed = false

round487R423SignedCompanionBudgetClosed : Bool
round487R423SignedCompanionBudgetClosed = false

round487PackageAClosed : Bool
round487PackageAClosed = false

round487ClayPromotion : Bool
round487ClayPromotion = false

round487CrossOutputCoherenceRequiredIsFalse :
  round487CrossOutputCoherenceRequired ≡ false
round487CrossOutputCoherenceRequiredIsFalse = refl

round487OutputCardinalityFactorIntroducedIsFalse :
  round487OutputCardinalityFactorIntroduced ≡ false
round487OutputCardinalityFactorIntroducedIsFalse = refl

round487SchurOrCauchyRouteMandatoryIsFalse :
  round487SchurOrCauchyRouteMandatory ≡ false
round487SchurOrCauchyRouteMandatoryIsFalse = refl

round487R284DecompositionMandatoryIsFalse :
  round487R284DecompositionMandatory ≡ false
round487R284DecompositionMandatoryIsFalse = refl

round487R423SignedCompanionBudgetClosedIsFalse :
  round487R423SignedCompanionBudgetClosed ≡ false
round487R423SignedCompanionBudgetClosedIsFalse = refl

round487ClayPromotionIsFalse : round487ClayPromotion ≡ false
round487ClayPromotionIsFalse = refl
