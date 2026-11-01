module DASHI.Interop.SensibLawNatSourcePropositionVerificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.Trit as Trit
import DASHI.Interop.SensibLawWikidataBalancedTernaryAdmissibilityHyperfabricExact as Ternary
import DASHI.Interop.SensibLawNatSourceSupportAcquisitionExact as Source

------------------------------------------------------------------------
-- SOURCE PROPOSITION VERIFICATION
--
-- A fetched P854 artifact is only a source candidate.  Payment of the exact
-- source-support residual requires an explicit, same-proposition verification
-- receipt over the preserved P5991 -> P14143 statement bundle.
------------------------------------------------------------------------

data SourceDisposition : Set where
  contradicted : SourceDisposition
  unresolved : SourceDisposition
  supported : SourceDisposition

dispositionTrit : SourceDisposition → Trit.Trit
dispositionTrit contradicted = Trit.neg
dispositionTrit unresolved = Trit.zer
dispositionTrit supported = Trit.pos

dispositionAdmissibility : SourceDisposition → Ternary.AdmissibilityState
dispositionAdmissibility contradicted = Ternary.rejected
dispositionAdmissibility unresolved = Ternary.open
dispositionAdmissibility supported = Ternary.admitted

supportPaid : SourceDisposition → Bool
supportPaid contradicted = false
supportPaid unresolved = false
supportPaid supported = true

record SourceVerificationDemand
    (residual : Source.NatSourceSupportResidual) : Set where
  constructor sourceVerificationDemand
  field
    exactResidualReference : String
    exactResidualReferenceIsExact :
      exactResidualReference ≡ Source.residualReference residual
    migrationCandidateDigest : String
    sourceClaimDigest : String
    targetClaimDigest : String
    sourceArtifactReceiptReference : String
    transformationContractReference : String
    demandReference : String
open SourceVerificationDemand public

record SourceVerificationReceipt
    {residual : Source.NatSourceSupportResidual}
    (demand : SourceVerificationDemand residual) : Set where
  constructor sourceVerificationReceipt
  field
    observedDemandReference : String
    observedDemandIsExact : observedDemandReference ≡ demandReference demand
    observedSourceClaimDigest : String
    observedSourceClaimIsExact :
      observedSourceClaimDigest ≡ sourceClaimDigest demand
    observedTargetClaimDigest : String
    observedTargetClaimIsExact :
      observedTargetClaimDigest ≡ targetClaimDigest demand
    observedSourceArtifactReceiptReference : String
    observedSourceArtifactIsExact :
      observedSourceArtifactReceiptReference ≡
      sourceArtifactReceiptReference demand
    disposition : SourceDisposition
    evidenceLocator : String
    verifierReference : String
    authorityEvaluated : Bool
    authorityEvaluatedIsFalse : authorityEvaluated ≡ false
open SourceVerificationReceipt public

record SourceSupportAdmission
    {residual : Source.NatSourceSupportResidual}
    {demand : SourceVerificationDemand residual}
    (receipt : SourceVerificationReceipt demand) : Set where
  constructor sourceSupportAdmission
  field
    supportState : Ternary.AdmissibilityState
    supportStateIsDisposition :
      supportState ≡ dispositionAdmissibility (disposition receipt)
    supportTrit : Trit.Trit
    supportTritIsDisposition : supportTrit ≡ dispositionTrit (disposition receipt)
    sourceSupportPaid : Bool
    sourceSupportPaidIsDisposition : sourceSupportPaid ≡ supportPaid (disposition receipt)
    authorityState : Ternary.AdmissibilityState
    authorityStillOpen : authorityState ≡ Ternary.open
    semanticPromotionPerformed : Bool
    semanticPromotionPerformedIsFalse : semanticPromotionPerformed ≡ false
    migrationAuthority : Bool
    migrationAuthorityIsFalse : migrationAuthority ≡ false
open SourceSupportAdmission public

admitSourceSupport :
  {residual : Source.NatSourceSupportResidual} →
  {demand : SourceVerificationDemand residual} →
  (receipt : SourceVerificationReceipt demand) →
  SourceSupportAdmission receipt
admitSourceSupport receipt =
  sourceSupportAdmission
    (dispositionAdmissibility (disposition receipt))
    refl
    (dispositionTrit (disposition receipt))
    refl
    (supportPaid (disposition receipt))
    refl
    Ternary.open
    refl
    false
    refl
    false
    refl

supportedPaysSourceSupport : supportPaid supported ≡ true
supportedPaysSourceSupport = refl

contradictedRejectsSourceSupport : dispositionTrit contradicted ≡ Trit.neg
contradictedRejectsSourceSupport = refl

unresolvedPreservesOpenCentre : dispositionTrit unresolved ≡ Trit.zer
unresolvedPreservesOpenCentre = refl

------------------------------------------------------------------------
-- FIREWALLS
------------------------------------------------------------------------

data FailedFetchImpliesContradiction : Set where
data UnresolvedImpliesContradiction : Set where
data SourceSupportImpliesAuthority : Set where
data SourceSupportCreatesMigrationAuthority : Set where
data SameArtifactMergesConsumerResiduals : Set where

failedFetchDoesNotCreateNegativeEvidence : FailedFetchImpliesContradiction → ⊥
failedFetchDoesNotCreateNegativeEvidence ()

unresolvedDoesNotCreateNegativeEvidence : UnresolvedImpliesContradiction → ⊥
unresolvedDoesNotCreateNegativeEvidence ()

sourceSupportDoesNotCreateAuthority : SourceSupportImpliesAuthority → ⊥
sourceSupportDoesNotCreateAuthority ()

sourceSupportDoesNotCreateMigrationAuthority :
  SourceSupportCreatesMigrationAuthority → ⊥
sourceSupportDoesNotCreateMigrationAuthority ()

sameArtifactDoesNotMergeConsumerResiduals : SameArtifactMergesConsumerResiduals → ⊥
sameArtifactDoesNotMergeConsumerResiduals ()

record NatSourcePropositionVerificationBoundary : Set where
  constructor nat-source-proposition-verification-boundary
  field
    exactResidualBindingRequired : Bool
    exactSourceClaimDigestRequired : Bool
    exactTargetClaimDigestRequired : Bool
    exactSourceArtifactRequired : Bool
    supportedMapsPositive : Bool
    contradictedMapsNegative : Bool
    unresolvedMapsZero : Bool
    failedFetchCreatesContradiction : Bool
    unresolvedCreatesContradiction : Bool
    sourceSupportCreatesAuthority : Bool
    sourceSupportCreatesMigrationAuthority : Bool
    sameArtifactMergesResiduals : Bool

canonicalNatSourcePropositionVerificationBoundary :
  NatSourcePropositionVerificationBoundary
canonicalNatSourcePropositionVerificationBoundary =
  nat-source-proposition-verification-boundary
    true true true true true true true false false false false false
