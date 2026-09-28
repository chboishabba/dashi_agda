{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (ℚ; _+_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteCMP109UVSameObjectExact as Same
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- PREFERRED SAME-OBJECT CONSTRUCTOR
--
-- Start with the CMP109 source trajectory and the literal coefficient packets.
-- Define the plaquette running data on EDGE k by
--
--   current_k := u_(k+1)
--   next_k    := u_k.
--
-- The only physical identity required is
--
--   beta_(k+1)
--     = vacuumPolarizationPlaquetteCoefficient_k + totalRemainder_k.
--
-- The running recurrence and all coordinate identifications then follow.
------------------------------------------------------------------------

record CMP109LiteralPlaquetteCoefficientWeld
    (trajectory : Flow.SourceNormalizedCouplingTrajectory) : Set₁ where
  field
    oneLoop : Plaquette.OneLoopVacuumPolarizationData Nat
    remainder : Plaquette.PlaquetteRemainderData Nat

    sourceBetaIsLiteralPlaquetteCoefficient :
      ∀ step →
      Flow.beta trajectory (suc step)
      ≡
      Plaquette.vacuumPolarizationPlaquetteCoefficient oneLoop step
        + Plaquette.totalRemainder remainder step

open CMP109LiteralPlaquetteCoefficientWeld public

asPhysicalRunningCouplingData :
  ∀ {trajectory} →
  CMP109LiteralPlaquetteCoefficientWeld trajectory →
  Plaquette.PhysicalRunningCouplingData Nat
asPhysicalRunningCouplingData {trajectory} weld = record
  { Plaquette.PhysicalRunningCouplingData.oneLoop =
      oneLoop weld
  ; Plaquette.PhysicalRunningCouplingData.remainder =
      remainder weld
  ; Plaquette.PhysicalRunningCouplingData.inverseCouplingSq =
      λ step → Flow.inverseCoupling trajectory (suc step)
  ; Plaquette.PhysicalRunningCouplingData.nextInverseCouplingSq =
      Flow.inverseCoupling trajectory
  ; Plaquette.PhysicalRunningCouplingData.physicalRunningCouplingRecursion =
      λ step →
        let
          uNext = Flow.inverseCoupling trajectory (suc step)
          one =
            Plaquette.vacuumPolarizationPlaquetteCoefficient
              (oneLoop weld) step
          rem =
            Plaquette.totalRemainder (remainder weld) step

          source =
            Flow.sourceRecurrence trajectory step

          coefficient =
            sourceBetaIsLiteralPlaquetteCoefficient weld step

          reassociate :
            uNext + (one + rem)
            ≡ (uNext + one) + rem
          reassociate = ℚRing.solve-∀ uNext one rem
        in
        trans
          source
          (trans
            (cong (uNext +_) coefficient)
            reassociate)
  }

constructedCurrentIsSourceSuccessor :
  ∀ {trajectory}
    (weld : CMP109LiteralPlaquetteCoefficientWeld trajectory)
    step →
  Plaquette.inverseCouplingSq
    (asPhysicalRunningCouplingData weld) step
  ≡ Flow.inverseCoupling trajectory (suc step)
constructedCurrentIsSourceSuccessor weld step = refl

constructedNextIsSourceCurrent :
  ∀ {trajectory}
    (weld : CMP109LiteralPlaquetteCoefficientWeld trajectory)
    step →
  Plaquette.nextInverseCouplingSq
    (asPhysicalRunningCouplingData weld) step
  ≡ Flow.inverseCoupling trajectory step
constructedNextIsSourceCurrent weld step = refl

constructedLiteralBetaIsSourceBeta :
  ∀ {trajectory}
    (weld : CMP109LiteralPlaquetteCoefficientWeld trajectory)
    step →
  Literal.literalBetaStep
    (asPhysicalRunningCouplingData weld) step
  ≡ Flow.beta trajectory (suc step)
constructedLiteralBetaIsSourceBeta weld step =
  sym (sourceBetaIsLiteralPlaquetteCoefficient weld step)

asLiteralPlaquetteCMP109UVSameObject :
  ∀ {trajectory}
    (weld : CMP109LiteralPlaquetteCoefficientWeld trajectory) →
  Same.LiteralPlaquetteCMP109UVSameObject
    (asPhysicalRunningCouplingData weld)
    trajectory
asLiteralPlaquetteCMP109UVSameObject weld = record
  { Same.LiteralPlaquetteCMP109UVSameObject.currentAtStepIsSourceSuccessor =
      constructedCurrentIsSourceSuccessor weld
  ; Same.LiteralPlaquetteCMP109UVSameObject.nextAtStepIsSourceCurrent =
      constructedNextIsSourceCurrent weld
  ; Same.LiteralPlaquetteCMP109UVSameObject.literalBetaAtStepIsSourceSuccessorBeta =
      constructedLiteralBetaIsSourceBeta weld
  }

postHocCurrentCoordinateWeldRequired : Bool
postHocCurrentCoordinateWeldRequired = false

postHocNextCoordinateWeldRequired : Bool
postHocNextCoordinateWeldRequired = false

postHocBetaCoordinateWeldRequired : Bool
postHocBetaCoordinateWeldRequired = false

sourceBetaCoefficientIdentityStillRequired : Bool
sourceBetaCoefficientIdentityStillRequired = true

postHocCurrentCoordinateWeldRequiredIsFalse :
  postHocCurrentCoordinateWeldRequired ≡ false
postHocCurrentCoordinateWeldRequiredIsFalse = refl

postHocNextCoordinateWeldRequiredIsFalse :
  postHocNextCoordinateWeldRequired ≡ false
postHocNextCoordinateWeldRequiredIsFalse = refl

postHocBetaCoordinateWeldRequiredIsFalse :
  postHocBetaCoordinateWeldRequired ≡ false
postHocBetaCoordinateWeldRequiredIsFalse = refl

sourceBetaCoefficientIdentityStillRequiredIsTrue :
  sourceBetaCoefficientIdentityStillRequired ≡ true
sourceBetaCoefficientIdentityStillRequiredIsTrue = refl

cmp109TrajectoryPlaquetteConstructorLevel : ProofLevel
cmp109TrajectoryPlaquetteConstructorLevel = machineChecked

literalSourceBetaCoefficientIdentityLevel : ProofLevel
literalSourceBetaCoefficientIdentityLevel = conditional
