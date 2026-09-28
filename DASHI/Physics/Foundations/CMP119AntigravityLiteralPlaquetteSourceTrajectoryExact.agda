{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteSourceTrajectoryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteCMP109UVSameObjectExact as Same
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CONSTRUCT CMP109 TRAJECTORY FROM THE LITERAL PLAQUETTE PRODUCER
--
-- Define, rather than post-hoc identify,
--
--   u_k       := plaquette.inverseCouplingSq k
--   beta_0    := 0
--   beta_(k+1):= literalBetaStep plaquette (k+1).
--
-- The only non-definitional source coherence is then
--
--   plaquette.nextInverseCouplingSq (k+1)
--     = plaquette.inverseCouplingSq k.
--
-- This is precisely the UV-predecessor interpretation forced by the orientation
-- firewall.  Once supplied, the CMP109 source recurrence follows from the
-- literal plaquette recurrence.
------------------------------------------------------------------------

record LiteralPlaquetteUVChainCoherence
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat) : Set₁ where
  field
    nextAtSuccessorIsPreviousCurrent :
      ∀ depth →
      Plaquette.nextInverseCouplingSq dataSet (suc depth)
      ≡ Plaquette.inverseCouplingSq dataSet depth

open LiteralPlaquetteUVChainCoherence public

sourceBeta :
  Plaquette.PhysicalRunningCouplingData Nat → Nat → ℚ
sourceBeta dataSet zero = 0ℚ
sourceBeta dataSet (suc depth) =
  Literal.literalBetaStep dataSet (suc depth)

canonicalSourceTrajectory :
  (dataSet : Plaquette.PhysicalRunningCouplingData Nat) →
  LiteralPlaquetteUVChainCoherence dataSet →
  Flow.SourceNormalizedCouplingTrajectory
canonicalSourceTrajectory dataSet coherence = record
  { Flow.SourceNormalizedCouplingTrajectory.inverseCoupling =
      Plaquette.inverseCouplingSq dataSet
  ; Flow.SourceNormalizedCouplingTrajectory.beta =
      sourceBeta dataSet
  ; Flow.SourceNormalizedCouplingTrajectory.sourceRecurrence =
      λ depth →
        trans
          (sym (nextAtSuccessorIsPreviousCurrent coherence depth))
          (Literal.literalRunningCouplingStepIsBetaSplit
            dataSet (suc depth))
  }

canonicalTrajectoryInverseCouplingIsLiteral :
  ∀ dataSet coherence depth →
  Flow.inverseCoupling
    (canonicalSourceTrajectory dataSet coherence) depth
  ≡ Plaquette.inverseCouplingSq dataSet depth
canonicalTrajectoryInverseCouplingIsLiteral dataSet coherence depth = refl

canonicalTrajectoryBetaIsLiteral :
  ∀ dataSet coherence depth →
  Flow.beta
    (canonicalSourceTrajectory dataSet coherence) (suc depth)
  ≡ Literal.literalBetaStep dataSet (suc depth)
canonicalTrajectoryBetaIsLiteral dataSet coherence depth = refl

canonicalTrajectoryAsUVSameObject :
  ∀ dataSet coherence →
  Same.LiteralPlaquetteCMP109UVSameObject
    dataSet
    (canonicalSourceTrajectory dataSet coherence)
canonicalTrajectoryAsUVSameObject dataSet coherence = record
  { Same.LiteralPlaquetteCMP109UVSameObject.currentInverseCouplingSame =
      λ _ → refl
  ; Same.LiteralPlaquetteCMP109UVSameObject.nextAtCoarseIsSourcePredecessor =
      nextAtSuccessorIsPreviousCurrent coherence
  ; Same.LiteralPlaquetteCMP109UVSameObject.literalBetaIsSourceBeta =
      λ _ → refl
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
