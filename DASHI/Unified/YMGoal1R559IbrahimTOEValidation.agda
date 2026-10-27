{-# OPTIONS --safe #-}
module DASHI.Unified.YMGoal1R559IbrahimTOEValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier
import DASHI.Unified.BalabanR559TOEMaxCutExact as YM
import DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact as Ibrahim

------------------------------------------------------------------------
-- Integration-only validation.
-- The imported modules remain the theorem owners.
------------------------------------------------------------------------

toeR559ReceiptMatchesOwner :
  TOE.toeBalabanR559MaxCutReceipt
  ≡ YM.canonicalBalabanR559TOEMaxCutReceipt
toeR559ReceiptMatchesOwner = refl

unifierR559ReceiptMatchesOwner :
  Unifier.unifiedBalabanR559MaxCutReceipt
  ≡ YM.canonicalBalabanR559TOEMaxCutReceipt
unifierR559ReceiptMatchesOwner = refl

toeRecognitionParetoMatchesOwner :
  TOE.toeIbrahimRecognitionParetoBoundary
  ≡ Ibrahim.ibrahimRecognitionParetoBoundary
toeRecognitionParetoMatchesOwner = refl

unifierRecognitionParetoMatchesOwner :
  Unifier.unifierIbrahimRecognitionParetoBoundary
  ≡ Ibrahim.ibrahimRecognitionParetoBoundary
unifierRecognitionParetoMatchesOwner = refl

toeCharacterExecutionMatchesOwner :
  TOE.toeIbrahimCharacterExecutionFrontier
  ≡ Ibrahim.ibrahimCharacterExecutionFrontier
toeCharacterExecutionMatchesOwner = refl

unifierCharacterExecutionMatchesOwner :
  Unifier.unifierIbrahimCharacterExecutionFrontier
  ≡ Ibrahim.ibrahimCharacterExecutionFrontier
unifierCharacterExecutionMatchesOwner = refl

toePhaseResolutionMatchesOwner :
  TOE.toeIbrahimPhaseResolutionFrontier
  ≡ Ibrahim.ibrahimPhaseResolutionFrontier
toePhaseResolutionMatchesOwner = refl

unifierPhaseResolutionMatchesOwner :
  Unifier.unifierIbrahimPhaseResolutionFrontier
  ≡ Ibrahim.ibrahimPhaseResolutionFrontier
unifierPhaseResolutionMatchesOwner = refl

toeHistoricalDiscriminatorMatchesOwner :
  TOE.toeIbrahimHistoricalDiscriminatorBoundary
  ≡ Ibrahim.ibrahimHistoricalDiscriminatorBoundary
toeHistoricalDiscriminatorMatchesOwner = refl

unifierHistoricalDiscriminatorMatchesOwner :
  Unifier.unifierIbrahimHistoricalDiscriminatorBoundary
  ≡ Ibrahim.ibrahimHistoricalDiscriminatorBoundary
unifierHistoricalDiscriminatorMatchesOwner = refl

toeScaleTransferPromotionStillImpossible :
  YM.ScaleTransferPromotion → ⊥
toeScaleTransferPromotionStillImpossible =
  TOE.toeBalabanScaleTransferNonPromotion

unifierScaleTransferPromotionStillImpossible :
  YM.ScaleTransferPromotion → ⊥
unifierScaleTransferPromotionStillImpossible =
  Unifier.unifiedBalabanScaleTransferNonPromotion

toeSearchPriorityStillNotProof :
  Ibrahim.SearchPriorityCreatesProof → ⊥
toeSearchPriorityStillNotProof =
  TOE.toeIbrahimSearchPriorityDoesNotCreateProof

unifierSearchPriorityStillNotProof :
  Ibrahim.SearchPriorityCreatesProof → ⊥
unifierSearchPriorityStillNotProof =
  Unifier.unifierIbrahimSearchPriorityDoesNotCreateProof

toeProducerSourceStillNotExecution :
  Ibrahim.ProducerSourceCreatesRunReceipt → ⊥
toeProducerSourceStillNotExecution =
  TOE.toeIbrahimProducerSourceDoesNotCreateRunReceipt

unifierProducerSourceStillNotExecution :
  Ibrahim.ProducerSourceCreatesRunReceipt → ⊥
unifierProducerSourceStillNotExecution =
  Unifier.unifierIbrahimProducerSourceDoesNotCreateRunReceipt

------------------------------------------------------------------------
-- Canonical 27-state proofs remain the same functions in both TOE roots.
-- No carrier identity between the recoverable code and the face model follows.
------------------------------------------------------------------------

toeTernary27NonDescentIsSameOwner :
  TOE.toeTernary27FaceCannotDescend ≡ Unifier.toeTernary27FaceCannotDescend
toeTernary27NonDescentIsSameOwner = refl

toeTernary27ConsumerRecoveryIsSameOwner :
  TOE.toeTernary27DependentCodePreservesConsumer
  ≡ Unifier.toeTernary27DependentCodePreservesConsumer
toeTernary27ConsumerRecoveryIsSameOwner = refl
