module DASHI.Wikimedia.MaboPersistenceAuthorityNormalizationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.MaboReviewedEvidencePaymentExact as Reviewed
import DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact as TwoOrder

------------------------------------------------------------------------
-- Formal parity for PERSISTENCE-AUTHORITY-1.
--
-- The runtime authority surface is a stable persisted reviewed-evidence ref.
-- Persistence records a review/payment coordinate; it does not manufacture
-- truth, applicability, legal authority, or a cross-order coercion.
------------------------------------------------------------------------

data NormativeOrderAgreement : TwoOrder.LegalOrderKind → TwoOrder.LegalOrderKind → Set where
  crown-agrees :
    NormativeOrderAgreement
      TwoOrder.crownMunicipalLegalOrder
      TwoOrder.crownMunicipalLegalOrder
  indigenous-agrees :
    NormativeOrderAgreement
      TwoOrder.indigenousNormativeLegalOrder
      TwoOrder.indigenousNormativeLegalOrder

crownCannotSilentlyConsumeIndigenous :
  NormativeOrderAgreement
    TwoOrder.crownMunicipalLegalOrder
    TwoOrder.indigenousNormativeLegalOrder → ⊥
crownCannotSilentlyConsumeIndigenous ()

indigenousCannotSilentlyConsumeCrown :
  NormativeOrderAgreement
    TwoOrder.indigenousNormativeLegalOrder
    TwoOrder.crownMunicipalLegalOrder → ⊥
indigenousCannotSilentlyConsumeCrown ()

record PersistedReviewedEvidenceAuthority : Set where
  constructor persisted-reviewed-evidence-authority
  field
    reviewedEvidenceReference : String
    reviewedEvidence : Reviewed.ReviewedEvidenceCoordinate
    normativeOrder : TwoOrder.LegalOrderKind
    normativeOrderReference : String
    persisted : Bool
    persistedIsTrue : persisted ≡ true
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false
    persistenceCreatesLegalAuthority : Bool
    persistenceCreatesLegalAuthorityIsFalse : persistenceCreatesLegalAuthority ≡ false

open PersistedReviewedEvidenceAuthority public

maboCrownReviewedEvidence : PersistedReviewedEvidenceAuthority
maboCrownReviewedEvidence =
  persisted-reviewed-evidence-authority
    "reviewed-evidence:mabo:P710:Q975866"
    Reviewed.maboParticipantIdentityReview
    TwoOrder.crownMunicipalLegalOrder
    (TwoOrder.LegalOrderFibre.orderReference TwoOrder.crownOrderFibre)
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Ref-authoritative legal-IR materialisation.
--
-- The caller supplies a persisted reference and expected normative order.
-- The materialiser must reopen the persisted coordinate and produce an exact
-- order-agreement witness. A raw observation or reconstructed support packet is
-- not represented as an authority-bearing constructor here.
------------------------------------------------------------------------

record LegalIrFromReviewedEvidenceRef : Set where
  constructor legal-ir-from-reviewed-evidence-ref
  field
    reviewedEvidenceReference : String
    expectedNormativeOrder : TwoOrder.LegalOrderKind
    persistedNormativeOrder : TwoOrder.LegalOrderKind
    normativeOrderAgreement :
      NormativeOrderAgreement expectedNormativeOrder persistedNormativeOrder
    reopensPersistedReviewedEvidence : Bool
    reopensPersistedReviewedEvidenceIsTrue : reopensPersistedReviewedEvidence ≡ true
    callerReconstructsSemanticPayload : Bool
    callerReconstructsSemanticPayloadIsFalse : callerReconstructsSemanticPayload ≡ false
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open LegalIrFromReviewedEvidenceRef public

maboCrownLegalIrMaterialisation : LegalIrFromReviewedEvidenceRef
maboCrownLegalIrMaterialisation =
  legal-ir-from-reviewed-evidence-ref
    (PersistedReviewedEvidenceAuthority.reviewedEvidenceReference maboCrownReviewedEvidence)
    TwoOrder.crownMunicipalLegalOrder
    (PersistedReviewedEvidenceAuthority.normativeOrder maboCrownReviewedEvidence)
    crown-agrees
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Durable acceptance controls remain validation/control assertions.
------------------------------------------------------------------------

record DurableAcceptanceControl : Set where
  constructor durable-acceptance-control
  field
    controlReference : String
    persisted : Bool
    persistedIsTrue : persisted ≡ true
    acceptanceOnly : Bool
    acceptanceOnlyIsTrue : acceptanceOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false
    expectationCausesWorldTransition : Bool
    expectationCausesWorldTransitionIsFalse : expectationCausesWorldTransition ≡ false

open DurableAcceptanceControl public

maboInvAcceptanceControl : DurableAcceptanceControl
maboInvAcceptanceControl =
  durable-acceptance-control
    "acceptance:inv:mabo:1"
    true refl
    true refl
    false refl
    false refl
    false refl

relCorpusAcceptanceControl : DurableAcceptanceControl
relCorpusAcceptanceControl =
  durable-acceptance-control
    "acceptance:rel:corpus-1"
    true refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data PersistedReviewEqualsClaimTruth : Set where
data AcceptanceExpectationCausesSemanticFact : Set where
data ReviewedEvidenceRefEqualsLegalAuthority : Set where
data NormativeOrderRefImpliesCrossOrderPriority : Set where

persistedReviewDoesNotEqualClaimTruth : PersistedReviewEqualsClaimTruth → ⊥
persistedReviewDoesNotEqualClaimTruth ()

acceptanceExpectationDoesNotCauseSemanticFact : AcceptanceExpectationCausesSemanticFact → ⊥
acceptanceExpectationDoesNotCauseSemanticFact ()

reviewedEvidenceRefDoesNotEqualLegalAuthority : ReviewedEvidenceRefEqualsLegalAuthority → ⊥
reviewedEvidenceRefDoesNotEqualLegalAuthority ()

normativeOrderRefDoesNotImplyCrossOrderPriority : NormativeOrderRefImpliesCrossOrderPriority → ⊥
normativeOrderRefDoesNotImplyCrossOrderPriority ()
