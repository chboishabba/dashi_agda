module DASHI.Cognition.PNF.X369OriginalSourceArbitraryWordResidualExact where

-- Geometry-forward closure: source-owned actual arbitrary finite future
-- history, separately signed task reference, exact retained byte defect.
-- Original Leech-LILA: Anatolii Kornienko. DASHI new formal bridge.
--
-- The original X369InputIndexedFutureConsumerExact already proves future
-- sufficiency after ONE-STEP observation/transition factorization.
-- This module does not replace that theorem or assume neural
-- equivariance: raw original bytes remain retained in every packet.
-- Kernel deliberately deferred.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as Future

module SourceWordResidual
  (Bytes Input Output Mark : Set)
  (_xor_ : Bytes → Bytes → Bytes)
  (xorCancelRight : (actual canonical : Bytes) →
    (actual xor canonical) xor canonical ≡ actual)
  (actualStep : Input → Bytes → Bytes)
  (actualObserve : Input → Bytes → Output)
  (taskStep : Input → Mark → Mark)
  (canonicalSeed : Mark → Bytes) where

  -- Reuse the genuine input-indexed source semantics, chronological.
  realWord : List Input → Bytes → Bytes
  realWord [] h = h
  realWord (u ∷ rest) h = realWord rest (actualStep u h)

  taskWord : List Input → Mark → Mark
  taskWord [] m = m
  taskWord (u ∷ rest) m = taskWord rest (taskStep u m)

  record SourceWordPacket : Set where
    constructor sourceWordPacket
    field
      realOriginalHistory : Bytes
      independentTaskHistory : Bytes
      retainedSourceDefect : Bytes
      originalObservedTrace : List Output
  open SourceWordPacket public

  pack : List Input → Mark → Bytes → SourceWordPacket
  pack word mark original =
    let learned = realWord word original
        reference = canonicalSeed (taskWord word mark)
    in sourceWordPacket
       learned reference (learned xor reference)
       (Future.trace actualStep actualObserve word original)

  reopen : SourceWordPacket → Bytes
  reopen packet =
    retainedSourceDefect packet xor independentTaskHistory packet

  fullOriginalHistoryReopens :
    (word : List Input) (mark : Mark) (original : Bytes) →
    reopen (pack word mark original) ≡ realWord word original
  fullOriginalHistoryReopens word mark original =
    xorCancelRight
      (realWord word original)
      (canonicalSeed (taskWord word mark))

  originalConsumerTraceReopens :
    (word : List Input) (mark : Mark) (original : Bytes) →
    originalObservedTrace (pack word mark original) ≡
      Future.trace actualStep actualObserve word original
  originalConsumerTraceReopens word mark original = refl

  emptyWordSourceReopens :
    (mark : Mark) (original : Bytes) →
    reopen (pack [] mark original) ≡ original
  emptyWordSourceReopens mark original =
    xorCancelRight original (canonicalSeed mark)

  chronologicalSourceWord :
    (u : Input) (rest : List Input) (original : Bytes) →
    realWord (u ∷ rest) original ≡
      realWord rest (actualStep u original)
  chronologicalSourceWord u rest original = refl

  chronologicalIndependentTaskWord :
    (u : Input) (rest : List Input) (mark : Mark) →
    taskWord (u ∷ rest) mark ≡ taskWord rest (taskStep u mark)
  chronologicalIndependentTaskWord u rest mark = refl

  -- The actual learned history and independently transported task mark
  -- form a SINGLE retained hyperfabric fibre; there is no inference
  -- that task mark alone determines the learned next state or output.
  JointState : Set
  JointState = Mark × Bytes

  jointStep : Input → JointState → JointState
  jointStep u (m , h) = taskStep u m , actualStep u h

  jointObserve : Input → JointState → Output
  jointObserve u (_ , h) = actualObserve u h

  realProjection : JointState → Bytes
  realProjection = proj₂

  jointRealStepSquare : (u : Input) (joint : JointState) →
    realProjection (jointStep u joint) ≡
      actualStep u (realProjection joint)
  jointRealStepSquare u (m , h) = refl

  jointRealObservationSquare : (u : Input) (joint : JointState) →
    jointObserve u joint ≡
      actualObserve u (realProjection joint)
  jointRealObservationSquare u (m , h) = refl

  -- This is REAL exact source trace preservation for arbitrary input
  -- words, because the ORIGINAL Bytes remain in the joint fibre.
  -- It is not yet a compression: dropping that Bytes component
  -- requires a separate consumer descent/transition certificate.
  jointFutureRealTrace :
    (word : List Input) (m : Mark) (original : Bytes) →
    Future.trace jointStep jointObserve word (m , original) ≡
      Future.trace actualStep actualObserve word original
  jointFutureRealTrace [] m original = refl
  jointFutureRealTrace (u ∷ rest) m original =
    Future.cong
      (λ tail → actualObserve u original ∷ tail)
      (jointFutureRealTrace rest (taskStep u m) (actualStep u original))

  -- The exact same source history can have many different independent
  -- TASK marks; no semantic quotient is forced by this joint packet.
  sourceBytesIdentityFibre : (m n : Mark) (h : Bytes) →
    realProjection (m , h) ≡ realProjection (n , h)
  sourceBytesIdentityFibre m n h = refl

-- Remaining source-specific obligations are exactly the existing
-- inputIndexedTraceDescent one-step assumptions, original Stage13
-- source-owned semantic valuations, and typed pants five-field
-- signatures. Do NOT claim neural group equivariance or Leech
-- lattice membership from these XOR reconstruction identities.
