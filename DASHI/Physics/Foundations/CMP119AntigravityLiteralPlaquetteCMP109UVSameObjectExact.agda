{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteCMP109UVSameObjectExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (_+_)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- EDGE-INDEXED LITERAL PLAQUETTE PRODUCER = NODE-INDEXED CMP109 HISTORY
--
-- CMP109 Eq. (2.15):
--
--   u_k = u_(k+1) + beta_(k+1)(g_k).
--
-- Therefore literal producer step k must be read as the EDGE k -> k+1:
--
--   producer current inverse coupling = u_(k+1)
--   producer next inverse coupling    = u_k
--   producer beta step                = beta_(k+1).
--
-- This is the source-faithful orientation and removes the earlier off-by-one
-- reading in which producer scale suc k was attached to source step k+1.
------------------------------------------------------------------------

record LiteralPlaquetteCMP109UVSameObject
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory) : Set₁ where
  field
    currentAtStepIsSourceSuccessor :
      ∀ step →
      Plaquette.inverseCouplingSq dataSet step
      ≡ Flow.inverseCoupling trajectory (suc step)

    nextAtStepIsSourceCurrent :
      ∀ step →
      Plaquette.nextInverseCouplingSq dataSet step
      ≡ Flow.inverseCoupling trajectory step

    literalBetaAtStepIsSourceSuccessorBeta :
      ∀ step →
      Literal.literalBetaStep dataSet step
      ≡ Flow.beta trajectory (suc step)

open LiteralPlaquetteCMP109UVSameObject public

literalProducerDerivesCMP109SourceRecurrence :
  ∀ {dataSet trajectory}
    (weld : LiteralPlaquetteCMP109UVSameObject dataSet trajectory)
    step →
  Flow.inverseCoupling trajectory step
  ≡
  Flow.inverseCoupling trajectory (suc step)
    + Flow.beta trajectory (suc step)
literalProducerDerivesCMP109SourceRecurrence
    {dataSet = dataSet} weld step =
  trans
    (sym (nextAtStepIsSourceCurrent weld step))
    (trans
      (Literal.literalRunningCouplingStepIsBetaSplit dataSet step)
      (cong₂
        _+_
        (currentAtStepIsSourceSuccessor weld step)
        (literalBetaAtStepIsSourceSuccessorBeta weld step)))

edgeIndexedProducerReadingRequired : Bool
edgeIndexedProducerReadingRequired = true

producerScaleSucShiftRequired : Bool
producerScaleSucShiftRequired = false

edgeIndexedProducerReadingRequiredIsTrue :
  edgeIndexedProducerReadingRequired ≡ true
edgeIndexedProducerReadingRequiredIsTrue = refl

producerScaleSucShiftRequiredIsFalse :
  producerScaleSucShiftRequired ≡ false
producerScaleSucShiftRequiredIsFalse = refl

literalPlaquetteCMP109UVCompilerLevel : ProofLevel
literalPlaquetteCMP109UVCompilerLevel = machineChecked

literalPlaquetteCMP109UVSameObjectLevel : ProofLevel
literalPlaquetteCMP109UVSameObjectLevel = conditional
