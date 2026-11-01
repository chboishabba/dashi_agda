module DASHI.Law.SensibLawProviderPinnedEphemeralMaterialisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawMaboDistributedLegalCorpusMaterialisationExact as Distributed
import DASHI.Cognition.PNF.SensibLawOALCPostgresPersistenceExact as OALC

------------------------------------------------------------------------
-- PROVIDER-PINNED EPHEMERAL MATERIALISATION
-- Runtime parity owner for SOURCE-MATERIALISATION-1.
------------------------------------------------------------------------

selectedDistributedBoundary : Distributed.DistributedLegalCorpusBoundary
selectedDistributedBoundary = Distributed.canonicalDistributedLegalCorpusBoundary

selectedOALCPersistenceBoundary : OALC.OALCPostgresPersistenceBoundary
selectedOALCPersistenceBoundary = OALC.canonicalOALCPostgresPersistenceBoundary

record ImmutableProviderPin : Set where
  constructor immutable-provider-pin
  field
    providerRef : String
    datasetRef : String
    datasetRevisionRef : String
    splitRef : String
    externalVersionRef : String
    citationRef : String
    sourceRef : String
    jurisdictionRef : String
open ImmutableProviderPin public

record DurableProviderSkeleton : Set where
  constructor durable-provider-skeleton
  field
    pin : ImmutableProviderPin
    externalSourceRevisionRef : String
    canonicalDocumentRef : String
    canonicalDigestRef : String
    canonicalByteLengthRef : String
    acquisitionReceiptRef : String
open DurableProviderSkeleton public

data ByteResidency : Set where
  bytesResident bytesEvicted : ByteResidency

data DigestAgreement : Set where
  exactStoredDigest changedDigest : DigestAgreement

record ProviderRuntimeState : Set where
  constructor provider-runtime-state
  field
    skeleton : DurableProviderSkeleton
    residency : ByteResidency
    digestAgreement : DigestAgreement
open ProviderRuntimeState public

evict : ProviderRuntimeState → ProviderRuntimeState
evict (provider-runtime-state durable currentResidency currentDigest) =
  provider-runtime-state durable bytesEvicted currentDigest

evictionPreservesSkeleton :
  (state : ProviderRuntimeState) → skeleton (evict state) ≡ skeleton state
evictionPreservesSkeleton (provider-runtime-state durable currentResidency currentDigest) = refl

rehydrate : ProviderRuntimeState → DigestAgreement → ProviderRuntimeState
rehydrate (provider-runtime-state durable currentResidency currentDigest) exactStoredDigest =
  provider-runtime-state durable bytesResident exactStoredDigest
rehydrate (provider-runtime-state durable currentResidency currentDigest) changedDigest =
  provider-runtime-state durable bytesEvicted changedDigest

strictActionEligible : ProviderRuntimeState → Bool
strictActionEligible (provider-runtime-state durable bytesResident exactStoredDigest) = true
strictActionEligible (provider-runtime-state durable bytesResident changedDigest) = false
strictActionEligible (provider-runtime-state durable bytesEvicted currentDigest) = false

residentExactDigestIsEligible :
  (durable : DurableProviderSkeleton) →
  strictActionEligible (provider-runtime-state durable bytesResident exactStoredDigest) ≡ true
residentExactDigestIsEligible durable = refl

evictedBytesAreIneligible :
  (durable : DurableProviderSkeleton) →
  (agreement : DigestAgreement) →
  strictActionEligible (provider-runtime-state durable bytesEvicted agreement) ≡ false
evictedBytesAreIneligible durable agreement = refl

changedDigestCannotRehydrateEligibility :
  (state : ProviderRuntimeState) →
  strictActionEligible (rehydrate state changedDigest) ≡ false
changedDigestCannotRehydrateEligibility (provider-runtime-state durable currentResidency currentDigest) = refl

exactDigestRehydrationPreservesSkeleton :
  (state : ProviderRuntimeState) →
  skeleton (rehydrate state exactStoredDigest) ≡ skeleton state
exactDigestRehydrationPreservesSkeleton (provider-runtime-state durable currentResidency currentDigest) = refl

------------------------------------------------------------------------
-- Exact provider legal slice -> curated legal source -> M12 statement -> PNF.
-- Provider/legal spans retain UTF-8 byte offsets; generic long-document spans
-- use Unicode character offsets. Those coordinate contracts do not collapse.
------------------------------------------------------------------------

data SourceCoordinateContract : Set where
  providerLegalUtf8ByteOffsets : SourceCoordinateContract
  genericLongDocumentCharacterOffsets : SourceCoordinateContract

record ProviderExactSliceCandidatePnfHandoff : Set where
  constructor provider-exact-slice-candidate-pnf-handoff
  field
    materialisationReference : String
    externalSourceRevisionReference : String
    legalSourceRevisionReference : String
    sourceSliceReference : String
    exactSpanReference : String
    sourceStatementReference : String
    parserReceiptReference : String
    candidatePnfReference : String
    coordinateContract : SourceCoordinateContract
    providerDigestReopenedExactly : Bool
    providerDigestReopenedExactlyIsTrue : providerDigestReopenedExactly ≡ true
    legalSourceRegistrationReopenedExactly : Bool
    legalSourceRegistrationReopenedExactlyIsTrue :
      legalSourceRegistrationReopenedExactly ≡ true
    exactSliceDigestChecked : Bool
    exactSliceDigestCheckedIsTrue : exactSliceDigestChecked ≡ true
    sourceStatementReopenedExactly : Bool
    sourceStatementReopenedExactlyIsTrue : sourceStatementReopenedExactly ≡ true
    candidatePnfReopenedExactly : Bool
    candidatePnfReopenedExactlyIsTrue : candidatePnfReopenedExactly ≡ true
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    propositionSupportPaid : Bool
    propositionSupportPaidIsFalse : propositionSupportPaid ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false
open ProviderExactSliceCandidatePnfHandoff public

record ProviderCandidatePnfBoundary : Set where
  constructor provider-candidate-pnf-boundary
  field
    strictProviderDigestRequired : Bool
    strictProviderDigestRequiredIsTrue : strictProviderDigestRequired ≡ true
    legalSourceRegistrationRequired : Bool
    legalSourceRegistrationRequiredIsTrue : legalSourceRegistrationRequired ≡ true
    exactSliceDigestRequired : Bool
    exactSliceDigestRequiredIsTrue : exactSliceDigestRequired ≡ true
    providerLegalByteCoordinateContractPreserved : Bool
    providerLegalByteCoordinateContractPreservedIsTrue :
      providerLegalByteCoordinateContractPreserved ≡ true
    silentByteToCharacterRelabellingAllowed : Bool
    silentByteToCharacterRelabellingAllowedIsFalse :
      silentByteToCharacterRelabellingAllowed ≡ false
    sourceStatementPersistenceRequired : Bool
    sourceStatementPersistenceRequiredIsTrue : sourceStatementPersistenceRequired ≡ true
    candidatePnfPersistenceRequired : Bool
    candidatePnfPersistenceRequiredIsTrue : candidatePnfPersistenceRequired ≡ true
    reviewAutomaticallyPaid : Bool
    reviewAutomaticallyPaidIsFalse : reviewAutomaticallyPaid ≡ false
    normativeOrderAutomaticallyAssigned : Bool
    normativeOrderAutomaticallyAssignedIsFalse : normativeOrderAutomaticallyAssigned ≡ false
open ProviderCandidatePnfBoundary public

canonicalProviderCandidatePnfBoundary : ProviderCandidatePnfBoundary
canonicalProviderCandidatePnfBoundary =
  provider-candidate-pnf-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl

record ProviderMaterialisationBoundary : Set where
  constructor provider-materialisation-boundary
  field
    immutableProviderRevisionRequired : Bool
    immutableProviderRevisionRequiredIsTrue : immutableProviderRevisionRequired ≡ true
    skeletonMayRemainWithoutResidentBytes : Bool
    skeletonMayRemainWithoutResidentBytesIsTrue : skeletonMayRemainWithoutResidentBytes ≡ true
    exactDigestRequiredForRehydration : Bool
    exactDigestRequiredForRehydrationIsTrue : exactDigestRequiredForRehydration ≡ true
    strictActionRequiresResidentBytes : Bool
    strictActionRequiresResidentBytesIsTrue : strictActionRequiresResidentBytes ≡ true
    evictionPreservesProviderIdentity : Bool
    evictionPreservesProviderIdentityIsTrue : evictionPreservesProviderIdentity ≡ true
    silentLatestSubstitutionAllowed : Bool
    silentLatestSubstitutionAllowedIsFalse : silentLatestSubstitutionAllowed ≡ false
    residencyCreatesSemanticAuthority : Bool
    residencyCreatesSemanticAuthorityIsFalse : residencyCreatesSemanticAuthority ≡ false
    residencyCreatesLegalAuthority : Bool
    residencyCreatesLegalAuthorityIsFalse : residencyCreatesLegalAuthority ≡ false
    residencyPromotesApplicability : Bool
    residencyPromotesApplicabilityIsFalse : residencyPromotesApplicability ≡ false
    residencyPromotesClaimTruth : Bool
    residencyPromotesClaimTruthIsFalse : residencyPromotesClaimTruth ≡ false
open ProviderMaterialisationBoundary public

canonicalProviderMaterialisationBoundary : ProviderMaterialisationBoundary
canonicalProviderMaterialisationBoundary =
  provider-materialisation-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

data ByteResidencyCreatesSemanticAuthority : Set where
data ByteResidencyCreatesLegalAuthority : Set where
data ByteResidencyCreatesApplicability : Set where
data ByteResidencyCreatesClaimTruth : Set where
data ProviderAvailabilityEqualsSourcePossession : Set where
data ChangedDigestMaySubstitutePinnedSource : Set where
data ProviderLegalByteOffsetEqualsGenericCharacterOffset : Set where
data ProviderCandidatePnfPaysReview : Set where
data ProviderCandidatePnfAssignsNormativeOrder : Set where

byteResidencyDoesNotCreateSemanticAuthority : ByteResidencyCreatesSemanticAuthority → ⊥
byteResidencyDoesNotCreateSemanticAuthority ()

byteResidencyDoesNotCreateLegalAuthority : ByteResidencyCreatesLegalAuthority → ⊥
byteResidencyDoesNotCreateLegalAuthority ()

byteResidencyDoesNotCreateApplicability : ByteResidencyCreatesApplicability → ⊥
byteResidencyDoesNotCreateApplicability ()

byteResidencyDoesNotCreateClaimTruth : ByteResidencyCreatesClaimTruth → ⊥
byteResidencyDoesNotCreateClaimTruth ()

providerAvailabilityDoesNotEqualSourcePossession : ProviderAvailabilityEqualsSourcePossession → ⊥
providerAvailabilityDoesNotEqualSourcePossession ()

changedDigestCannotSubstitutePinnedSource : ChangedDigestMaySubstitutePinnedSource → ⊥
changedDigestCannotSubstitutePinnedSource ()

providerLegalByteOffsetDoesNotEqualGenericCharacterOffset :
  ProviderLegalByteOffsetEqualsGenericCharacterOffset → ⊥
providerLegalByteOffsetDoesNotEqualGenericCharacterOffset ()

providerCandidatePnfDoesNotPayReview : ProviderCandidatePnfPaysReview → ⊥
providerCandidatePnfDoesNotPayReview ()

providerCandidatePnfDoesNotAssignNormativeOrder : ProviderCandidatePnfAssignsNormativeOrder → ⊥
providerCandidatePnfDoesNotAssignNormativeOrder ()
