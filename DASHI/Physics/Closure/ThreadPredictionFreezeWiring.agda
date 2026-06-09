module DASHI.Physics.Closure.ThreadPredictionFreezeWiring where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataObservableDefinitionReceipt as Observable
import DASHI.Physics.Closure.HEPDataRatioTableArtifactReceipt as Artifact
import DASHI.Physics.Closure.HEPDataPredictionFreezePolicyRequest as Freeze
import DASHI.Physics.Closure.HEPDataComparisonLawReceiptRequest as Compare

------------------------------------------------------------------------
-- Thread prediction-freeze wiring.
--
-- The "Quantum Time Superposition" thread describes a prediction ladder:
-- choose the observable, make the carrier exact, expose the energy functional,
-- freeze inputs before comparison, guard artifacts/provenance, then compare.
-- This module turns that into a finite, ordered, non-promoting Agda receipt
-- and connects the HEPData-facing rungs to existing prediction-freeze
-- surfaces.  It deliberately does not construct a comparison law or promote
-- W3/W4/W5/W8.

data ThreadPredictionFreezeStatus : Set where
  predictionLadderWiredNoPromotion :
    ThreadPredictionFreezeStatus

data ThreadPredictionGate : Set where
  gateSelectedObservable :
    ThreadPredictionGate
  gateCarrierExactness :
    ThreadPredictionGate
  gateEnergyFunctionalAvailable :
    ThreadPredictionGate
  gateFrozenInputsBeforeComparison :
    ThreadPredictionGate
  gateArtifactProvenanceGuard :
    ThreadPredictionGate
  gateComparisonLawMissingNonPromoting :
    ThreadPredictionGate

canonicalThreadPredictionGateOrder :
  List ThreadPredictionGate
canonicalThreadPredictionGateOrder =
  gateSelectedObservable
  ∷ gateCarrierExactness
  ∷ gateEnergyFunctionalAvailable
  ∷ gateFrozenInputsBeforeComparison
  ∷ gateArtifactProvenanceGuard
  ∷ gateComparisonLawMissingNonPromoting
  ∷ []

data ThreadCarrierExactnessStatus : Set where
  exactCarrierRequiredBeforePredictionComparison :
    ThreadCarrierExactnessStatus

data ThreadEnergyFunctionalStatus : Set where
  energyFunctionalAvailableAsInputRequirement :
    ThreadEnergyFunctionalStatus

data ThreadFrozenInputStatus : Set where
  cleanFreezeRequiredBeforeComparisonLaw :
    ThreadFrozenInputStatus

data ThreadArtifactProvenanceStatus : Set where
  checksumAndDigestGuardRequired :
    ThreadArtifactProvenanceStatus

data ThreadComparisonLawStatus : Set where
  comparisonLawStillMissingAndNonPromoting :
    ThreadComparisonLawStatus

data ThreadPredictionFreezeBoundary : Set where
  noCarrierExactnessProofConstructedHere :
    ThreadPredictionFreezeBoundary
  noEnergyFunctionalConstructedHere :
    ThreadPredictionFreezeBoundary
  noCleanFreezeAcceptedHere :
    ThreadPredictionFreezeBoundary
  noProjectionRunAcceptedHere :
    ThreadPredictionFreezeBoundary
  noComparisonLawConstructedHere :
    ThreadPredictionFreezeBoundary
  noEmpiricalPromotionHere :
    ThreadPredictionFreezeBoundary

canonicalThreadPredictionFreezeBoundaries :
  List ThreadPredictionFreezeBoundary
canonicalThreadPredictionFreezeBoundaries =
  noCarrierExactnessProofConstructedHere
  ∷ noEnergyFunctionalConstructedHere
  ∷ noCleanFreezeAcceptedHere
  ∷ noProjectionRunAcceptedHere
  ∷ noComparisonLawConstructedHere
  ∷ noEmpiricalPromotionHere
  ∷ []

data ThreadEmpiricalPromotionReceipt : Set where

threadEmpiricalPromotionImpossibleHere :
  ThreadEmpiricalPromotionReceipt →
  ⊥
threadEmpiricalPromotionImpossibleHere ()

record ThreadPredictionFreezeWiringReceipt : Setω where
  field
    status :
      ThreadPredictionFreezeStatus

    gateOrder :
      List ThreadPredictionGate

    gateOrderIsCanonical :
      gateOrder ≡ canonicalThreadPredictionGateOrder

    gateOrderText :
      List String

    selectedObservableReceipt :
      Observable.HEPDataObservableDefinitionReceipt

    selectedObservableKeyword :
      String

    selectedObservableKeywordIsCanonical :
      selectedObservableKeyword ≡ "DSIG/DPHISTAR / DSIG/DPHISTAR"

    selectedObservableValidated :
      Bool

    selectedObservableValidatedIsTrue :
      selectedObservableValidated ≡ true

    carrierExactnessStatus :
      ThreadCarrierExactnessStatus

    carrierExactnessText :
      String

    energyFunctionalStatus :
      ThreadEnergyFunctionalStatus

    energyFunctionalText :
      String

    freezePolicyRequest :
      Freeze.HEPDataPredictionFreezePolicyRequest

    frozenInputsBeforeComparison :
      ThreadFrozenInputStatus

    freezeSequence :
      List Freeze.HEPDataCleanFreezeStep

    freezeSequenceIsCanonical :
      freezeSequence ≡ Freeze.canonicalHEPDataCleanFreezeSequence

    artifactReceipt :
      Artifact.HEPDataRatioTableArtifactReceipt

    artifactProvenanceStatus :
      ThreadArtifactProvenanceStatus

    artifactProvenanceGuardText :
      List String

    comparisonLawRequest :
      Compare.HEPDataComparisonLawReceiptRequest

    comparisonLawStatus :
      ThreadComparisonLawStatus

    comparisonLawRequestStillBlocked :
      Compare.HEPDataComparisonLawReceiptRequest.status comparisonLawRequest
      ≡
      Compare.blockedAwaitingComparisonLawReceiptArtifacts

    promotesEmpiricalGate :
      Bool

    promotesEmpiricalGateIsFalse :
      promotesEmpiricalGate ≡ false

    boundaries :
      List ThreadPredictionFreezeBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalThreadPredictionFreezeBoundaries

    empiricalPromotionBlocked :
      ThreadEmpiricalPromotionReceipt →
      ⊥

canonicalThreadPredictionFreezeWiringReceipt :
  ThreadPredictionFreezeWiringReceipt
canonicalThreadPredictionFreezeWiringReceipt =
  record
    { status =
        predictionLadderWiredNoPromotion
    ; gateOrder =
        canonicalThreadPredictionGateOrder
    ; gateOrderIsCanonical =
        refl
    ; gateOrderText =
        "selected observable: consume the existing t43/t44/t45/t46 header receipt and select the DSIG/DPHISTAR ratio convention"
        ∷ "carrier exactness: require an exact carrier before any prediction comparison"
        ∷ "energy functional availability: require the energy functional as an input to the prediction ladder"
        ∷ "frozen inputs before comparison: consume the clean-freeze policy order before any comparison-law receipt"
        ∷ "artifact/provenance guard: consume checksum-bound t43/t44 artifacts and require a digest-bound projection artifact"
        ∷ "comparison law: current receipt is still a blocked request and cannot promote an empirical gate"
        ∷ []
    ; selectedObservableReceipt =
        Observable.canonicalHEPDataObservableDefinitionReceipt
    ; selectedObservableKeyword =
        Observable.HEPDataObservableDefinitionReceipt.observableKeyword
          Observable.canonicalHEPDataObservableDefinitionReceipt
    ; selectedObservableKeywordIsCanonical =
        refl
    ; selectedObservableValidated =
        Observable.HEPDataObservableDefinitionReceipt.localHeaderFactsValidated
          Observable.canonicalHEPDataObservableDefinitionReceipt
    ; selectedObservableValidatedIsTrue =
        refl
    ; carrierExactnessStatus =
        exactCarrierRequiredBeforePredictionComparison
    ; carrierExactnessText =
        "The thread ladder cannot compare predictions until the chosen carrier is exact; this module records the gate but does not fabricate that proof."
    ; energyFunctionalStatus =
        energyFunctionalAvailableAsInputRequirement
    ; energyFunctionalText =
        "The thread ladder requires an available energy functional before prediction comparison; this module records the requirement without constructing a new energy space."
    ; freezePolicyRequest =
        Freeze.canonicalHEPDataPredictionFreezePolicyRequest
    ; frozenInputsBeforeComparison =
        cleanFreezeRequiredBeforeComparisonLaw
    ; freezeSequence =
        Freeze.canonicalHEPDataCleanFreezeSequence
    ; freezeSequenceIsCanonical =
        refl
    ; artifactReceipt =
        Artifact.canonicalHEPDataRatioTableArtifactReceipt
    ; artifactProvenanceStatus =
        checksumAndDigestGuardRequired
    ; artifactProvenanceGuardText =
        "t43 SHA-256 is checksum-bound by the existing artifact receipt"
        ∷ "t44 SHA-256 is checksum-bound by the existing artifact receipt"
        ∷ "the projection artifact digest remains required before comparison"
        ∷ "artifact provenance is a guard, not a comparison-law proof"
        ∷ []
    ; comparisonLawRequest =
        Compare.canonicalHEPDataComparisonLawReceiptRequest
    ; comparisonLawStatus =
        comparisonLawStillMissingAndNonPromoting
    ; comparisonLawRequestStillBlocked =
        refl
    ; promotesEmpiricalGate =
        false
    ; promotesEmpiricalGateIsFalse =
        refl
    ; boundaries =
        canonicalThreadPredictionFreezeBoundaries
    ; boundariesAreCanonical =
        refl
    ; empiricalPromotionBlocked =
        threadEmpiricalPromotionImpossibleHere
    }

canonicalThreadPredictionGateOrderProved :
  ThreadPredictionFreezeWiringReceipt.gateOrder
    canonicalThreadPredictionFreezeWiringReceipt
  ≡
  canonicalThreadPredictionGateOrder
canonicalThreadPredictionGateOrderProved = refl

canonicalThreadFrozenInputsBeforeComparison :
  ThreadPredictionFreezeWiringReceipt.frozenInputsBeforeComparison
    canonicalThreadPredictionFreezeWiringReceipt
  ≡
  cleanFreezeRequiredBeforeComparisonLaw
canonicalThreadFrozenInputsBeforeComparison = refl

canonicalThreadComparisonLawNonPromoting :
  ThreadPredictionFreezeWiringReceipt.promotesEmpiricalGate
    canonicalThreadPredictionFreezeWiringReceipt
  ≡
  false
canonicalThreadComparisonLawNonPromoting = refl
