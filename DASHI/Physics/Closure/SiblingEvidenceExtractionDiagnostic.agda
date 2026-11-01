module DASHI.Physics.Closure.SiblingEvidenceExtractionDiagnostic where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.SiblingEvidenceInventory as Inventory

------------------------------------------------------------------------
-- SIB-R2: sibling evidence extraction diagnostic.
--
-- SIB-R1 records that sibling artifacts exist.  SIB-R2 records what the
-- bounded workers found when they inspected those artifacts.  The findings are
-- deliberately negative/preservative: they narrow the path without promoting
-- any W3/W4/W5/W6/W8/W9 gate.

data SiblingExtractionStatus : Set where
  extractionCompletedNoAcceptedPromotionReceipts :
    SiblingExtractionStatus

data SiblingExtractionFinding : Set where
  dashifineHasCoefficientFlowNoAcceptedPhiStarRatioAPI :
    SiblingExtractionFinding
  dashifineProofDossierRequiresTrueTMap :
    SiblingExtractionFinding
  lyapunovSummaryIsAggregateSupportOnly :
    SiblingExtractionFinding
  e8MorphemeVocabIsTokenizerNotRootEnumeration :
    SiblingExtractionFinding
  leanMoonshineFilesSupportArithmeticNotThetaJ :
    SiblingExtractionFinding

canonicalSiblingExtractionFindings :
  List SiblingExtractionFinding
canonicalSiblingExtractionFindings =
  dashifineHasCoefficientFlowNoAcceptedPhiStarRatioAPI
  ∷ dashifineProofDossierRequiresTrueTMap
  ∷ lyapunovSummaryIsAggregateSupportOnly
  ∷ e8MorphemeVocabIsTokenizerNotRootEnumeration
  ∷ leanMoonshineFilesSupportArithmeticNotThetaJ
  ∷ []

record SiblingExtractionWorkerResult : Set where
  field
    workerLane :
      String

    workerOwner :
      String

    inspectedSurface :
      String

    finding :
      SiblingExtractionFinding

    gateEffect :
      String

dashifinePredictionRouteResult :
  SiblingExtractionWorkerResult
dashifinePredictionRouteResult =
  record
    { workerLane =
        "HEP-R35 sibling projection route scan"
    ; workerOwner =
        "W0 local extraction"
    ; inspectedSurface =
        "../dashifine and ../dashiQ phi-star/t43/projection scripts and artifacts"
    ; finding =
        dashifineHasCoefficientFlowNoAcceptedPhiStarRatioAPI
    ; gateEffect =
        "HEP-R33 remains blocked: no accepted sigma_DASHI phi-star ratio callable was found"
    }

dashifineTrueTMapGapResult :
  SiblingExtractionWorkerResult
dashifineTrueTMapGapResult =
  record
    { workerLane =
        "HEP-R35 true T-map gap"
    ; workerOwner =
        "W0 local extraction"
    ; inspectedSurface =
        "../dashifine/26_hepdata_proof_dossier.py"
    ; finding =
        dashifineProofDossierRequiresTrueTMap
    ; gateEffect =
        "Sibling dossier is diagnostic only: it says to replace the proxy map with the true DASHI T-map"
    }

lyapunovSummaryResult :
  SiblingExtractionWorkerResult
lyapunovSummaryResult =
  record
    { workerLane =
        "LYAP-W2W9"
    ; workerOwner =
        "Jason the 2nd"
    ; inspectedSurface =
        "../dashifine/hepdata_lyapunov_test_out_all/overall_certification.json"
    ; finding =
        lyapunovSummaryIsAggregateSupportOnly
    ; gateEffect =
        "W2/W9 get support pointers only: no carrier-state hash, pass certificate, or checksum-bound in-repo receipt"
    }

e8VocabularyResult :
  SiblingExtractionWorkerResult
e8VocabularyResult =
  record
    { workerLane =
        "E8VOCAB-R2"
    ; workerOwner =
        "Maxwell the 2nd"
    ; inspectedSurface =
        "../DASHIg/LeechTransformer/vocab/e8_morpheme_.vocab and .model"
    ; finding =
        e8MorphemeVocabIsTokenizerNotRootEnumeration
    ; gateEffect =
        "LILA-R2 remains blocked: 2048-entry SentencePiece/BPE tokenizer artifact, not 240 E8 roots"
    }

leanMoonshineResult :
  SiblingExtractionWorkerResult
leanMoonshineResult =
  record
    { workerLane =
        "LEAN-R4"
    ; workerOwner =
        "Sagan the 2nd"
    ; inspectedSurface =
        "../dashi_lean4/MoonshineEarn.lean; MoonshineFractran.lean; DashiPerf/Audit.lean"
    ; finding =
        leanMoonshineFilesSupportArithmeticNotThetaJ
    ; gateEffect =
        "LILA-R4 remains blocked: no E8 theta, E4, Delta, or formal j(E4,Delta) theorem found"
    }

canonicalSiblingExtractionWorkerResults :
  List SiblingExtractionWorkerResult
canonicalSiblingExtractionWorkerResults =
  dashifinePredictionRouteResult
  ∷ dashifineTrueTMapGapResult
  ∷ lyapunovSummaryResult
  ∷ e8VocabularyResult
  ∷ leanMoonshineResult
  ∷ []

data SiblingExtractionMissingReceipt : Set where
  missingTrueDASHITMapOrPhiStarRatioAPI :
    SiblingExtractionMissingReceipt
  missingCarrierStateBoundLyapunovReceipt :
    SiblingExtractionMissingReceipt
  missingConstructiveE8RootEnumeration :
    SiblingExtractionMissingReceipt
  missingThetaJModularFormsAdapter :
    SiblingExtractionMissingReceipt
  missingCleanFreezeAndProjectionRun :
    SiblingExtractionMissingReceipt

canonicalSiblingExtractionMissingReceipts :
  List SiblingExtractionMissingReceipt
canonicalSiblingExtractionMissingReceipts =
  missingTrueDASHITMapOrPhiStarRatioAPI
  ∷ missingCarrierStateBoundLyapunovReceipt
  ∷ missingConstructiveE8RootEnumeration
  ∷ missingThetaJModularFormsAdapter
  ∷ missingCleanFreezeAndProjectionRun
  ∷ []

data SiblingExtractionPromotedReceipt : Set where

siblingExtractionPromotionImpossibleHere :
  SiblingExtractionPromotedReceipt →
  ⊥
siblingExtractionPromotionImpossibleHere ()

record SiblingEvidenceExtractionDiagnostic : Setω where
  field
    inventory :
      Inventory.SiblingEvidenceInventory

    status :
      SiblingExtractionStatus

    promotesAnyGate :
      Bool

    promotesAnyGateIsFalse :
      promotesAnyGate ≡ false

    findings :
      List SiblingExtractionFinding

    findingsAreCanonical :
      findings ≡ canonicalSiblingExtractionFindings

    workerResults :
      List SiblingExtractionWorkerResult

    workerResultsAreCanonical :
      workerResults ≡ canonicalSiblingExtractionWorkerResults

    missingReceipts :
      List SiblingExtractionMissingReceipt

    missingReceiptsAreCanonical :
      missingReceipts ≡ canonicalSiblingExtractionMissingReceipts

    nextAcceptedRoute :
      List String

    nonPromotionBoundary :
      List String

    promotedReceiptBlocked :
      SiblingExtractionPromotedReceipt →
      ⊥

canonicalSiblingEvidenceExtractionDiagnostic :
  SiblingEvidenceExtractionDiagnostic
canonicalSiblingEvidenceExtractionDiagnostic =
  record
    { inventory =
        Inventory.canonicalSiblingEvidenceInventory
    ; status =
        extractionCompletedNoAcceptedPromotionReceipts
    ; promotesAnyGate =
        false
    ; promotesAnyGateIsFalse =
        refl
    ; findings =
        canonicalSiblingExtractionFindings
    ; findingsAreCanonical =
        refl
    ; workerResults =
        canonicalSiblingExtractionWorkerResults
    ; workerResultsAreCanonical =
        refl
    ; missingReceipts =
        canonicalSiblingExtractionMissingReceipts
    ; missingReceiptsAreCanonical =
        refl
    ; nextAcceptedRoute =
        "Define or locate the true in-repo DASHI T-map for t43 bin records"
        ∷ "Expose it as module:function returning sigma_DASHI(50-76)/sigma_DASHI(76-106)"
        ∷ "Bind the function before comparison with a clean predictionFixedAt hash"
        ∷ "Run the existing digest-bound t43/t44 runner against that accepted API"
        ∷ []
    ; nonPromotionBoundary =
        "No sibling artifact found here constructs an accepted DASHI phi-star prediction API"
        ∷ "No sibling artifact found here constructs a constructive E8 root receipt"
        ∷ "No sibling artifact found here constructs a theta/J Agda adapter receipt"
        ∷ "No sibling artifact found here constructs W3/W4/W5/W6/W8/W9 promotion"
        ∷ []
    ; promotedReceiptBlocked =
        siblingExtractionPromotionImpossibleHere
    }

canonicalSiblingEvidenceExtractionStatus :
  SiblingExtractionStatus
canonicalSiblingEvidenceExtractionStatus =
  SiblingEvidenceExtractionDiagnostic.status
    canonicalSiblingEvidenceExtractionDiagnostic
