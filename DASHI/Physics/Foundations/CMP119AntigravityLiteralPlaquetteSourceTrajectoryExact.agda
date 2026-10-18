{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteSourceTrajectoryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteCMP109UVSameObjectExact as Same
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CONSTRUCT THE NODE-INDEXED CMP109 TRAJECTORY FROM EDGE-INDEXED PLAQUETTE DATA
--
-- Define
--
--   u_0       := producer.nextInverseCouplingSq 0
--   u_(k+1)   := producer.inverseCouplingSq k
--   beta_0    := 0
--   beta_(k+1):= producer.literalBetaStep k.
--
-- The only inter-edge coherence needed is
--
--   producer.nextInverseCouplingSq (k+1)
--     = producer.inverseCouplingSq k.
--
-- Then every source recurrence u_k = u_(k+1) + beta_(k+1) is exactly one
-- literal plaquette update, including k=0.
------------------------------------------------------------------------

record LiteralPlaquetteUVChainCoherence
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat) : Set₁ where
  field
    nextSuccessorIsPreviousCurrent :
      ∀ step →
      Plaquette.nextInverseCouplingSq dataSet (suc step)
      ≡ Plaquette.inverseCouplingSq dataSet step

open LiteralPlaquetteUVChainCoherence public

sourceInverseCoupling :
  Plaquette.PhysicalRunningCouplingData Nat → Nat → ℚ
sourceInverseCoupling dataSet zero =
  Plaquette.nextInverseCouplingSq dataSet zero
sourceInverseCoupling dataSet (suc step) =
  Plaquette.inverseCouplingSq dataSet step

sourceBeta :
  Plaquette.PhysicalRunningCouplingData Nat → Nat → ℚ
sourceBeta dataSet zero = 0ℚ
sourceBeta dataSet (suc step) =
  Literal.literalBetaStep dataSet step

canonicalSourceTrajectory :
  (dataSet : Plaquette.PhysicalRunningCouplingData Nat) →
  LiteralPlaquetteUVChainCoherence dataSet →
  Flow.SourceNormalizedCouplingTrajectory
canonicalSourceTrajectory dataSet coherence = record
  { Flow.SourceNormalizedCouplingTrajectory.inverseCoupling =
      sourceInverseCoupling dataSet
  ; Flow.SourceNormalizedCouplingTrajectory.beta =
      sourceBeta dataSet
  ; Flow.SourceNormalizedCouplingTrajectory.sourceRecurrence =
      sourceRecurrence
  }
  where
  sourceRecurrence :
    ∀ step →
    sourceInverseCoupling dataSet step
    ≡
    sourceInverseCoupling dataSet (suc step)
      + sourceBeta dataSet (suc step)
  sourceRecurrence zero =
    Literal.literalRunningCouplingStepIsBetaSplit dataSet zero
  sourceRecurrence (suc step) =
    trans
      (sym (nextSuccessorIsPreviousCurrent coherence step))
      (Literal.literalRunningCouplingStepIsBetaSplit dataSet (suc step))

canonicalTrajectoryCurrentIsSourceSuccessor :
  ∀ dataSet coherence step →
  Plaquette.inverseCouplingSq dataSet step
  ≡ Flow.inverseCoupling
      (canonicalSourceTrajectory dataSet coherence) (suc step)
canonicalTrajectoryCurrentIsSourceSuccessor dataSet coherence step = refl

canonicalTrajectoryNextIsSourceCurrent :
  ∀ dataSet coherence step →
  Plaquette.nextInverseCouplingSq dataSet step
  ≡ Flow.inverseCoupling
      (canonicalSourceTrajectory dataSet coherence) step
canonicalTrajectoryNextIsSourceCurrent dataSet coherence zero = refl
canonicalTrajectoryNextIsSourceCurrent dataSet coherence (suc step) =
  nextSuccessorIsPreviousCurrent coherence step

canonicalTrajectoryBetaIsLiteral :
  ∀ dataSet coherence step →
  Literal.literalBetaStep dataSet step
  ≡ Flow.beta
      (canonicalSourceTrajectory dataSet coherence) (suc step)
canonicalTrajectoryBetaIsLiteral dataSet coherence step = refl

canonicalTrajectoryAsUVSameObject :
  ∀ dataSet coherence →
  Same.LiteralPlaquetteCMP109UVSameObject
    dataSet
    (canonicalSourceTrajectory dataSet coherence)
canonicalTrajectoryAsUVSameObject dataSet coherence = record
  { Same.LiteralPlaquetteCMP109UVSameObject.currentAtStepIsSourceSuccessor =
      canonicalTrajectoryCurrentIsSourceSuccessor dataSet coherence
  ; Same.LiteralPlaquetteCMP109UVSameObject.nextAtStepIsSourceCurrent =
      canonicalTrajectoryNextIsSourceCurrent dataSet coherence
  ; Same.LiteralPlaquetteCMP109UVSameObject.literalBetaAtStepIsSourceSuccessorBeta =
      canonicalTrajectoryBetaIsLiteral dataSet coherence
  }

postHocInverseCouplingEqualityRequired : Bool
postHocInverseCouplingEqualityRequired = false

postHocBetaEqualityRequired : Bool
postHocBetaEqualityRequired = false

uvChainCoherenceStillRequired : Bool
uvChainCoherenceStillRequired = true

postHocInverseCouplingEqualityRequiredIsFalse :
  postHocInverseCouplingEqualityRequired ≡ false
postHocInverseCouplingEqualityRequiredIsFalse = refl

postHocBetaEqualityRequiredIsFalse :
  postHocBetaEqualityRequired ≡ false
postHocBetaEqualityRequiredIsFalse = refl

uvChainCoherenceStillRequiredIsTrue :
  uvChainCoherenceStillRequired ≡ true
uvChainCoherenceStillRequiredIsTrue = refl

literalPlaquetteSourceTrajectoryCompilerLevel : ProofLevel
literalPlaquetteSourceTrajectoryCompilerLevel = machineChecked

literalPlaquetteUVChainCoherenceLevel : ProofLevel
literalPlaquetteUVChainCoherenceLevel = conditional
