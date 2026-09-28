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
-- LITERAL PLAQUETTE PRODUCER = CMP109 SOURCE HISTORY, WITH UV ORIENTATION
--
-- The literal producer's next inverse-coupling value must not be read as source
-- depth suc(scale).  On the source-faithful UV-directed reading,
--
--   producer scale = suc k
--   producer current inverse coupling = u_(k+1)
--   producer next inverse coupling    = u_k
--   producer beta step                = beta_(k+1).
--
-- Its plus-sign recurrence then becomes exactly
--
--   u_k = u_(k+1) + beta_(k+1).
------------------------------------------------------------------------

record LiteralPlaquetteCMP109UVSameObject
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory) : Set₁ where
  field
    currentInverseCouplingSame :
      ∀ depth →
      Plaquette.inverseCouplingSq dataSet depth
      ≡ Flow.inverseCoupling trajectory depth

    nextAtCoarseIsSourcePredecessor :
      ∀ depth →
      Plaquette.nextInverseCouplingSq dataSet (suc depth)
      ≡ Flow.inverseCoupling trajectory depth

    literalBetaIsSourceBeta :
      ∀ depth →
      Literal.literalBetaStep dataSet (suc depth)
      ≡ Flow.beta trajectory (suc depth)

open LiteralPlaquetteCMP109UVSameObject public

literalProducerDerivesCMP109SourceRecurrence :
  ∀ {dataSet trajectory}
    (weld : LiteralPlaquetteCMP109UVSameObject dataSet trajectory)
    depth →
  Flow.inverseCoupling trajectory depth
  ≡
  Flow.inverseCoupling trajectory (suc depth)
    + Flow.beta trajectory (suc depth)
literalProducerDerivesCMP109SourceRecurrence
    {dataSet = dataSet} weld depth =
  trans
    (sym (nextAtCoarseIsSourcePredecessor weld depth))
    (trans
      (Literal.literalRunningCouplingStepIsBetaSplit
        dataSet (suc depth))
      (cong₂
        _+_
        (currentInverseCouplingSame weld (suc depth))
        (literalBetaIsSourceBeta weld depth)))

naiveSuccessorReadingRequired : Bool
naiveSuccessorReadingRequired = false

uvPredecessorReadingRequired : Bool
uvPredecessorReadingRequired = true

naiveSuccessorReadingRequiredIsFalse :
  naiveSuccessorReadingRequired ≡ false
naiveSuccessorReadingRequiredIsFalse = refl

uvPredecessorReadingRequiredIsTrue :
  uvPredecessorReadingRequired ≡ true
uvPredecessorReadingRequiredIsTrue = refl

literalPlaquetteCMP109UVCompilerLevel : ProofLevel
literalPlaquetteCMP109UVCompilerLevel = machineChecked

-- Remaining physical same-object payment: inhabit the three coordinate
-- identifications above for the actual literal plaquette producer/history.
literalPlaquetteCMP109UVSameObjectLevel : ProofLevel
literalPlaquetteCMP109UVSameObjectLevel = conditional
