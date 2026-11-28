module DASHI.Cognition.PNF.X369OriginalSourceResidualTransportExact where

-- Original Leech-LILA: Anatolii Kornienko; DASHI exact sourced weld.
-- The independent signed S3 task target and the actually trained
-- recurrent source are DIFFERENT transformations in general.
--
-- Exact byte XOR does not need the actual learned source action to
-- commute with S3: always retain an original-source residual.
-- This is a source-/representation-independent reconstruction theorem,
-- not a neural equivariance, training, metric or Leech automorphism.
-- Agda kernel deferred by user request.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
import DASHI.Cognition.PNF.X369OriginalMarkedSeedHypervoxelSourceExact as Marked
import DASHI.Cognition.PNF.X369OriginalSignedSourceGridAutomorphismExact as Geometry

-- An exact byte carrier with XOR self-cancellation on the RIGHT is
-- sufficient; no external law about neural transitions is assumed.
module SourceBytes
  (Bytes Input Output : Set)
  (_xor_ : Bytes → Bytes → Bytes)
  (rightCancellation : (a b : Bytes) →
    (a xor b) xor b ≡ a)
  (nativeStep : Input → Bytes → Bytes)
  (nativeObserve : Input → Bytes → Output)
  (signedExpectedSeed : Input → Bytes → Bytes) where

  record StepReceipt : Set where
    constructor sourceReceipt
    field
      actualOriginal : Bytes
      canonicalExpected : Bytes
      retainedDefect : Bytes
      sourceObservation : Output
  open StepReceipt public

  originalSourceReceipt : Input → Bytes → StepReceipt
  originalSourceReceipt input before =
    sourceReceipt
      (nativeStep input before)
      (signedExpectedSeed input before)
      (nativeStep input before xor signedExpectedSeed input before)
      (nativeObserve input before)

  reconstruct : StepReceipt → Bytes
  reconstruct receipt =
    retainedDefect receipt xor canonicalExpected receipt

  oneStepOriginalSourceBidi : (input : Input) (before : Bytes) →
    reconstruct (originalSourceReceipt input before) ≡
      nativeStep input before
  oneStepOriginalSourceBidi input before =
    rightCancellation (nativeStep input before)
      (signedExpectedSeed input before)

  -- Original consumer observations travel with the SOURCE receipt,
  -- never from the independent expected signed task label.
  oneStepOriginalObservationBidi : (input : Input) (before : Bytes) →
    sourceObservation (originalSourceReceipt input before)
      ≡ nativeObserve input before
  oneStepOriginalObservationBidi input before = refl

  -- The AFTER of the first native step is the actual starting point
  -- of the next native step; one cannot silently advance a canonical
  -- signed seed and discard the neural source residual.
  record TwoStepReceipt : Set where
    constructor twoStepReceipt
    field
      firstSourceStep : StepReceipt
      secondSourceStep : StepReceipt
  open TwoStepReceipt public

  sourceTwoStep : Input → Input → Bytes → TwoStepReceipt
  sourceTwoStep first second original =
    twoStepReceipt
      (originalSourceReceipt first original)
      (originalSourceReceipt second (nativeStep first original))

  secondStepOriginalSourceBidi :
    (first second : Input) (original : Bytes) →
    reconstruct (secondSourceStep (sourceTwoStep first second original))
      ≡ nativeStep second (nativeStep first original)
  secondStepOriginalSourceBidi first second original =
    oneStepOriginalSourceBidi second (nativeStep first original)

  -- The raw source observation at the second step is NOT an action
  -- label and need not factor through the signed initial seed chart.
  secondStepObservationBidi :
    (first second : Input) (original : Bytes) →
    sourceObservation (secondSourceStep (sourceTwoStep first second original))
      ≡ nativeObserve second (nativeStep first original)
  secondStepObservationBidi first second original = refl

  -- Exact original per-input one-step closure of a proposed chart and
  -- consumer is a *separate* premise of X369InputIndexedFutureConsumer.
  -- The existence of a reversible defect receipt proves NO such
  -- factorisation; it only prevents original information loss.

-- Source-owned marked initial nine-trit states and full 369 graph
-- signed actions already live in OriginalMarkedSeedHypervoxelSourceExact
-- and OriginalSignedSourceGridAutomorphismExact. This module provides
-- exactly their ORIGINAL learned-history residual socket, with no new
-- group or hyperfabric definitions.
