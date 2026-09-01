module DASHI.Cognition.PNF.SensibLawLegalSemanticAdmissionFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.PackedNormativeSparseAdmissionExact as Sparse
import DASHI.Cognition.PNF.PackedNormativeDeltaAuthorityBridgeExact as Authority

------------------------------------------------------------------------
-- Post expanded-GWB-v0.2 frontier.
--
-- Runtime feasibility/parity is no longer the dominant uncertainty.  The next
-- boundary is semantic adequacy + explicit admission authority:
--
-- parser observation -> candidate fibre -> resolution/admission receipt
-- -> admitted local normative delta -> later authority materialization.
--
-- This owner deliberately does not introduce publication authority.
------------------------------------------------------------------------

record LegalSemanticGoldSurface : Set where
  constructor legalSemanticGoldSurface
  field
    coveredFixtureCount : Nat
    producerGapCount : Nat
    exactConsumerObjectExpected : Bool
    unresolvedMayBeCorrectAnswer : Bool

open LegalSemanticGoldSurface public

legalSemanticGoldV01 : LegalSemanticGoldSurface
legalSemanticGoldV01 =
  legalSemanticGoldSurface 10 6 true true

coveredFixtureCountIsTen :
  coveredFixtureCount legalSemanticGoldV01 ≡ 10
coveredFixtureCountIsTen = refl

producerGapCountIsSix :
  producerGapCount legalSemanticGoldV01 ≡ 6
producerGapCountIsSix = refl

------------------------------------------------------------------------
-- Admission receipt currency.
------------------------------------------------------------------------

data ResolutionAuthority : Set where
  deterministicReviewedPolicy humanReview : ResolutionAuthority

data CandidateScope : Set where
  syntacticallyLocal scopeUnresolved attachmentUnresolved contextRequired : CandidateScope

data ResolvedScope : Set where
  localSyntactic scopeResolved attachmentResolved contextResolved : ResolvedScope

record StableCandidateKey : Set where
  constructor stableCandidateKey
  field
    sentenceId : Nat
    localOrdinal : Nat
    sourceStart : Nat
    sourceEnd : Nat
    semanticKind : String
    candidateScope : CandidateScope

open StableCandidateKey public

record SemanticAdmissionReceipt (candidate : StableCandidateKey) : Set where
  constructor semanticAdmissionReceipt
  field
    resolvedScope : ResolvedScope
    authority : ResolutionAuthority
    policyReference : String
    resolverReference : String
    exactCandidateIdentity : StableCandidateKey
    sameCandidate : exactCandidateIdentity ≡ candidate

open SemanticAdmissionReceipt public

record AdmittedLocalNormativeDelta (candidate : StableCandidateKey) : Set where
  constructor admittedLocalNormativeDelta
  field
    admissionReceipt : SemanticAdmissionReceipt candidate

open AdmittedLocalNormativeDelta public

admitWithReceipt :
  (candidate : StableCandidateKey) →
  SemanticAdmissionReceipt candidate →
  AdmittedLocalNormativeDelta candidate
admitWithReceipt candidate receipt =
  admittedLocalNormativeDelta receipt

------------------------------------------------------------------------
-- Residual-frontier measurements are work-selection evidence only.
------------------------------------------------------------------------

data ResidualKind : Set where
  negationScopeUnresolved
  modalityScopeUnresolved
  temporalAnchorUnresolved
  conditionalScopeUnresolved
  clauseInterpretationAmbiguous
  referenceAttachmentUnresolved
  qualifierAttachmentUnresolved
  unsupportedDependency : ResidualKind

record ResidualFrontierObservation : Set where
  constructor residualFrontierObservation
  field
    count : ResidualKind → Nat

open ResidualFrontierObservation public

record ResidualPriorityPolicy : Set where
  constructor residualPriorityPolicy
  field
    legalImportance : ResidualKind → Nat
    resolvability : ResidualKind → Nat

open ResidualPriorityPolicy public

------------------------------------------------------------------------
-- Direct bridges to the already-owned sparse-admission / authority laws.
------------------------------------------------------------------------

sparseAdmissionStillCannotCreateAuthority :
  Sparse.SparseAdmissionChangesSemanticAuthority → ⊥
sparseAdmissionStillCannotCreateAuthority =
  Sparse.sparseAdmissionDoesNotCreateAuthority

rejectedAdmissionStillDoesNotDeleteParserEvidence :
  Sparse.RejectedNormativeFibreDeletesParserEvidence → ⊥
rejectedAdmissionStillDoesNotDeleteParserEvidence =
  Sparse.rejectionDoesNotDeleteParserEvidence

materializationParityStillCannotCreateSecondAuthority :
  Authority.MaterializationParityAuthorizesSecondSemanticAuthority → ⊥
materializationParityStillCannotCreateSecondAuthority =
  Authority.materializationParityDoesNotCreateAuthority

------------------------------------------------------------------------
-- Hard non-promotions.
------------------------------------------------------------------------

data ParserCandidateAloneAuthorizesAdmission : Set where

data ResidualFrequencyIsSemanticQuality : Set where

data ResidualPriorityScoreIsTruthConfidence : Set where

data GoldConformanceV01ProvesUniversalLegalCorrectness : Set where

data AdmissionReceiptPublishesGeneration : Set where

parserCandidateAloneCannotAuthorizeAdmission :
  ParserCandidateAloneAuthorizesAdmission → ⊥
parserCandidateAloneCannotAuthorizeAdmission ()

residualFrequencyIsNotSemanticQuality :
  ResidualFrequencyIsSemanticQuality → ⊥
residualFrequencyIsNotSemanticQuality ()

residualPriorityIsNotTruthConfidence :
  ResidualPriorityScoreIsTruthConfidence → ⊥
residualPriorityIsNotTruthConfidence ()

goldV01DoesNotProveUniversalLegalCorrectness :
  GoldConformanceV01ProvesUniversalLegalCorrectness → ⊥
goldV01DoesNotProveUniversalLegalCorrectness ()

admissionReceiptDoesNotPublishGeneration :
  AdmissionReceiptPublishesGeneration → ⊥
admissionReceiptDoesNotPublishGeneration ()

------------------------------------------------------------------------
-- Current implementation frontier.
------------------------------------------------------------------------

data LegalSemanticAdmissionFrontier : Set where
  implementationAwaitingCompileGoldAndResidualReceipt : LegalSemanticAdmissionFrontier
  goldAndResidualValidatedAwaitingLegalCorpusAdmission : LegalSemanticAdmissionFrontier

currentLegalSemanticAdmissionFrontier : LegalSemanticAdmissionFrontier
currentLegalSemanticAdmissionFrontier =
  implementationAwaitingCompileGoldAndResidualReceipt
