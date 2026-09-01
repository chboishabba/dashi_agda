module DASHI.Governance.SexedHistoricalBraidQuotientResidualExact where

------------------------------------------------------------------------
-- CONSUMER-SAFE BRAID QUOTIENT + EXACT ORDER RESIDUAL
--
-- If two ordered braid histories are equivalent for the immediate-action
-- consumer, that consumer may safely use a quotient that forgets their order.
-- If a later provenance/future consumer needs the fine representative again,
-- an explicit residual reconstructs which order was carried.
--
-- This is a finite DASHI instance of the repo-wide quotient/residual grammar:
-- quotient safety and representative reopening are separate obligations.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.ContestableCompressionResidualExact as Contestable
import DASHI.Governance.SexedHistoricalBraidedStratifiedConsumerKernelExact as Kernel

------------------------------------------------------------------------
-- 1. Two fine ordered histories collapsed by an immediate-action quotient.
------------------------------------------------------------------------

data FineBraidState : Set where
  evidenceThenFidelity
  fidelityThenEvidence
  : FineBraidState

data ImmediateQuotientCode : Set where
  sameImmediateClass : ImmediateQuotientCode

data OrderResidual : Set where
  evidenceFirstResidual
  fidelityFirstResidual
  : OrderResidual

immediateClass : FineBraidState → ImmediateQuotientCode
immediateClass _ = sameImmediateClass

orderResidual : FineBraidState → OrderResidual
orderResidual evidenceThenFidelity = evidenceFirstResidual
orderResidual fidelityThenEvidence = fidelityFirstResidual

reopenExact : ImmediateQuotientCode → OrderResidual → FineBraidState
reopenExact sameImmediateClass evidenceFirstResidual = evidenceThenFidelity
reopenExact sameImmediateClass fidelityFirstResidual = fidelityThenEvidence

reopenEvidenceFirstExact :
  reopenExact (immediateClass evidenceThenFidelity)
    (orderResidual evidenceThenFidelity)
  ≡ evidenceThenFidelity
reopenEvidenceFirstExact = refl

reopenFidelityFirstExact :
  reopenExact (immediateClass fidelityThenEvidence)
    (orderResidual fidelityThenEvidence)
  ≡ fidelityThenEvidence
reopenFidelityFirstExact = refl

------------------------------------------------------------------------
-- 2. Quotient alone cannot recover representative; quotient + residual can.
------------------------------------------------------------------------

sameImmediateClassProof :
  immediateClass evidenceThenFidelity ≡ immediateClass fidelityThenEvidence
sameImmediateClassProof = refl

fineStatesDiffer : evidenceThenFidelity ≡ fidelityThenEvidence → ⊥
fineStatesDiffer ()

immediateQuotientCannotRecoverFineOrder :
  (decoder : ImmediateQuotientCode → FineBraidState) →
  ((state : FineBraidState) → decoder (immediateClass state) ≡ state) → ⊥
immediateQuotientCannotRecoverFineOrder decoder exact =
  fineStatesDiffer
    (transEq
      (symEq (exact evidenceThenFidelity))
      (exact fidelityThenEvidence))
  where
    symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    symEq refl = refl

    transEq : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    transEq refl refl = refl

classAndResidualDetermineFineState :
  {left right : FineBraidState} →
  immediateClass left ≡ immediateClass right →
  orderResidual left ≡ orderResidual right →
  left ≡ right
classAndResidualDetermineFineState {evidenceThenFidelity} {evidenceThenFidelity} _ _ = refl
classAndResidualDetermineFineState {evidenceThenFidelity} {fidelityThenEvidence} _ ()
classAndResidualDetermineFineState {fidelityThenEvidence} {evidenceThenFidelity} _ ()
classAndResidualDetermineFineState {fidelityThenEvidence} {fidelityThenEvidence} _ _ = refl

------------------------------------------------------------------------
-- 3. Consumer safety is relative: the quotient is safe for immediate action,
-- but the provenance consumer rejects the same collapse.
------------------------------------------------------------------------

data ImmediateActionReading : Set where sameAction : ImmediateActionReading

data ProvenanceReading : Set where evidenceFirst fidelityFirst : ProvenanceReading

immediateReading : FineBraidState → ImmediateActionReading
immediateReading _ = sameAction

provenanceReading : FineBraidState → ProvenanceReading
provenanceReading evidenceThenFidelity = evidenceFirst
provenanceReading fidelityThenEvidence = fidelityFirst

immediateConsumerSafeCollapse :
  immediateReading evidenceThenFidelity ≡ immediateReading fidelityThenEvidence
immediateConsumerSafeCollapse = refl

provenanceConsumerRejectsCollapse :
  provenanceReading evidenceThenFidelity
  ≡ provenanceReading fidelityThenEvidence → ⊥
provenanceConsumerRejectsCollapse ()

------------------------------------------------------------------------
-- 4. Continuity with actual braid-kernel fixture.
------------------------------------------------------------------------

kernelImmediateSwapSafetyStillAvailable :
  Kernel.SwapSafeImmediate Kernel.evidenceFidelityWord
kernelImmediateSwapSafetyStillAvailable =
  Kernel.evidenceFidelitySwapImmediateSafe

kernelProvenanceSwapSafetyStillRejected :
  Kernel.SwapSafeProvenance Kernel.evidenceFidelityWord → ⊥
kernelProvenanceSwapSafetyStillRejected =
  Kernel.evidenceFidelitySwapNotProvenanceSafe

------------------------------------------------------------------------
-- 5. Repo-wide quotient/residual boundary reused as calibration.
------------------------------------------------------------------------

contestableExactResidualBoundary : Contestable.ContestableCompressionReceipt
contestableExactResidualBoundary = Contestable.canonicalExactContestabilityReceipt

contestableRelevantResidualBoundary : Contestable.ContestableCompressionReceipt
contestableRelevantResidualBoundary = Contestable.canonicalRelevantContestabilityReceipt

------------------------------------------------------------------------
-- 6. No-promotion boundaries.
------------------------------------------------------------------------

data SafeForImmediateMeansSafeForProvenance : Set where

data QuotientSafetyImpliesFineRecovery : Set where

data ResidualMeansCollapsedStateWasFalse : Set where

data ResidualMustBePubliclyDisclosed : Set where

data BraidQuotientIsCryptographicCompressionScheme : Set where

data ResidualCreatesHistoricalAuthority : Set where

safeForImmediateDoesNotMeanSafeForProvenance :
  SafeForImmediateMeansSafeForProvenance → ⊥
safeForImmediateDoesNotMeanSafeForProvenance ()

quotientSafetyDoesNotImplyFineRecovery : QuotientSafetyImpliesFineRecovery → ⊥
quotientSafetyDoesNotImplyFineRecovery ()

residualDoesNotMeanCollapsedStateWasFalse : ResidualMeansCollapsedStateWasFalse → ⊥
residualDoesNotMeanCollapsedStateWasFalse ()

residualNeedDoesNotImplyPublicDisclosure : ResidualMustBePubliclyDisclosed → ⊥
residualNeedDoesNotImplyPublicDisclosure ()

braidQuotientIsNotCryptographicCompressionScheme :
  BraidQuotientIsCryptographicCompressionScheme → ⊥
braidQuotientIsNotCryptographicCompressionScheme ()

residualDoesNotCreateHistoricalAuthority : ResidualCreatesHistoricalAuthority → ⊥
residualDoesNotCreateHistoricalAuthority ()

record BraidQuotientResidualBoundary : Set where
  constructor braid-quotient-residual-boundary
  field
    immediateQuotientCollapsesOrder : Bool
    exactResidualReopensOrder : Bool
    quotientPlusResidualDeterminesFineState : Bool
    provenanceConsumerRejectsImmediateCollapse : Bool
    quotientSafetyImpliesFineRecovery : Bool
    residualMeansOldStateFalse : Bool
    cryptographicCompressionSchemeClaimed : Bool

canonicalBraidQuotientResidualBoundary : BraidQuotientResidualBoundary
canonicalBraidQuotientResidualBoundary =
  braid-quotient-residual-boundary true true true true false false false
