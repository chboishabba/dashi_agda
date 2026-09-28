{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (0ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Carrier
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- SAME-OBJECT ORIENTATION BRIDGE
--
-- CMP109 source indexing:
--
--   u_k = u_(k+1) + beta_(k+1)
--
-- with increasing k toward the coarser lattice.
--
-- P3's positive-increment recurrence runs current -> next.  The correct
-- UV-directed view therefore takes nextScale = predecessor:
--
--   suc k -> k.
--
-- This module embeds the exact rational source history into Bishop reals and
-- proves the recurrence under Bishop's native setoid equality.
------------------------------------------------------------------------

embed = Carrier.bishopRationalEmbed

uvNext : Nat → Nat
uvNext zero = zero
uvNext (suc depth) = depth

uvInverseCoupling :
  Flow.SourceNormalizedCouplingTrajectory → Nat → Bishop.ℝ
uvInverseCoupling trajectory depth =
  embed (Flow.inverseCoupling trajectory depth)

uvIncrement :
  Flow.SourceNormalizedCouplingTrajectory → Nat → Bishop.ℝ
uvIncrement trajectory zero = Bishop.0ℝ
uvIncrement trajectory (suc depth) =
  embed (Flow.beta trajectory (suc depth))

uvRecurrenceSetoid :
  (trajectory : Flow.SourceNormalizedCouplingTrajectory) →
  ∀ depth →
  Bishop._≃_
    (uvInverseCoupling trajectory (uvNext depth))
    (Bishop._+_
      (uvInverseCoupling trajectory depth)
      (uvIncrement trajectory depth))
uvRecurrenceSetoid trajectory zero =
  BishopP.≃-symm
    (BishopP.+-identityʳ
      (uvInverseCoupling trajectory zero))
uvRecurrenceSetoid trajectory (suc depth) =
  let
    current = Flow.inverseCoupling trajectory (suc depth)
    increment = Flow.beta trajectory (suc depth)

    embeddedAdd :
      Bishop._≃_
        (embed (current Data.Rational.Base.+ increment))
        (Bishop._+_ (embed current) (embed increment))
    embeddedAdd =
      Carrier.bishopEmbedAdd current increment
  in
  subst
    (λ selected →
      Bishop._≃_
        (embed selected)
        (Bishop._+_ (embed current) (embed increment)))
    (sym (Flow.sourceRecurrence trajectory depth))
    embeddedAdd

------------------------------------------------------------------------
-- P3 recursion represents this exact source history iff these three same-object
-- identifications hold.  This is the minimal carrier bridge; no sign or scale
-- orientation is left implicit.
------------------------------------------------------------------------

record P3RepresentsSourceUVView
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (recursion : P3.RunningCouplingRecursion Nat Bishop.ℝ) : Set₁ where
  field
    inverseCouplingSame :
      ∀ depth →
      Bishop._≃_
        (P3.inverseCouplingSq recursion depth)
        (uvInverseCoupling trajectory depth)

    nextScaleIsUVPredecessor :
      ∀ depth →
      P3.nextScale recursion depth ≡ uvNext depth

    totalIncrementSame :
      ∀ depth →
      Bishop._≃_
        (Bishop._+_
          (P3.betaLogBlocking recursion depth)
          (P3.remainder recursion depth))
        (uvIncrement trajectory depth)

open P3RepresentsSourceUVView public

sourceHistoryBishopUVRecurrenceLevel : ProofLevel
sourceHistoryBishopUVRecurrenceLevel = machineChecked

-- This bridge is the actual same-object payment between the rational CMP109
-- beta history and any Bishop-valued P3/running-coupling convention.
p3SourceHistorySameObjectLevel : ProofLevel
p3SourceHistorySameObjectLevel = conditional
