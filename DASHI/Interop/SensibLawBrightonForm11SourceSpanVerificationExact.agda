module DASHI.Interop.SensibLawBrightonForm11SourceSpanVerificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.Trit as Trit
import DASHI.Interop.SensibLawNatSourceSupportAcquisitionExact as Source
import DASHI.Interop.SensibLawNatSourcePropositionVerificationExact as Verify

------------------------------------------------------------------------
-- BRIGHTON FORM 11 PRIVATE-SOURCE SPAN VERIFICATION
--
-- The original completed matter document remains private and is not committed
-- to this repository.  This module commits only privacy-bounded verification
-- metadata needed to identify the reviewed artifact and exact source span.
--
-- Selected proposition scope is deliberately narrow: the completed Form 11
-- supports that an unresolved mould / associated roof-repair condition was
-- asserted in the matter carrier as at 24 January 2023.  This receipt does not
-- verify health causation, retaliatory motive, statutory breach, liability or
-- remedy entitlement.
------------------------------------------------------------------------

form11ArtifactSha256 : String
form11ArtifactSha256 =
  "sha256:bb998cb9c2777165d19339db91db798e00e66e838a162a14e2fe8de67599e982"

form11ArtifactReceiptReference : String
form11ArtifactReceiptReference =
  "private Brighton completed Form11 artifact @ " <> form11ArtifactSha256

form11EvidenceLocator : String
form11EvidenceLocator =
  "page 1 / breach-details narrative field / unresolved condition-and-repair assertion"

form11TargetClaimDigest : String
form11TargetClaimDigest =
  "sha256:4dd2e76f4ce92138f1cbb53df951a10e9ab7427db11e4db7e324c4de3ab934bc"

form11Residual : Source.NatSourceSupportResidual
form11Residual =
  Source.natSourceSupportResidual
    "private Brighton matter row"
    "not-a-Wikidata-QID"
    "completed Form11 matter statement"
    "Brighton s185 single-matter regression"
    "Brighton 24-Jan-2023 Form11 unresolved-condition factual support residual"

form11Demand : Verify.SourceVerificationDemand form11Residual
form11Demand =
  Verify.sourceVerificationDemand
    "Brighton 24-Jan-2023 Form11 unresolved-condition factual support residual"
    refl
    form11ArtifactSha256
    form11TargetClaimDigest
    form11TargetClaimDigest
    form11ArtifactReceiptReference
    "identity transformation: exact reviewed span -> same bounded matter proposition"
    "Brighton Form11 exact source-span verification demand v1"

form11Receipt : Verify.SourceVerificationReceipt form11Demand
form11Receipt =
  Verify.sourceVerificationReceipt
    "Brighton Form11 exact source-span verification demand v1"
    refl
    form11TargetClaimDigest
    refl
    form11TargetClaimDigest
    refl
    form11ArtifactReceiptReference
    refl
    Verify.supported
    form11EvidenceLocator
    "manual exact-source review; private artifact retained outside repository"
    false
    refl

form11Admission : Verify.SourceSupportAdmission form11Receipt
form11Admission = Verify.admitSourceSupport form11Receipt

form11SourceSupportPaid :
  Verify.sourceSupportPaid form11Admission ≡ true
form11SourceSupportPaid = refl

form11SupportTritPositive :
  Verify.supportTrit form11Admission ≡ Trit.pos
form11SupportTritPositive = refl

form11AuthorityStillOpen :
  Verify.authorityState form11Admission
  ≡ DASHI.Interop.SensibLawWikidataBalancedTernaryAdmissibilityHyperfabricExact.open
form11AuthorityStillOpen = refl

------------------------------------------------------------------------
-- Privacy / semantic firewalls.
------------------------------------------------------------------------

data SourceSpanReceiptPublishesPrivateDocumentBody : Set where
data SourceSpanSupportEstablishesHealthCausation : Set where
data SourceSpanSupportEstablishesRetaliatoryMotive : Set where
data SourceSpanSupportEstablishesStatutoryBreach : Set where
data SourceSpanSupportCreatesLegalAuthority : Set where

sourceSpanReceiptDoesNotPublishPrivateDocumentBody :
  SourceSpanReceiptPublishesPrivateDocumentBody → ⊥
sourceSpanReceiptDoesNotPublishPrivateDocumentBody ()

sourceSpanSupportDoesNotEstablishHealthCausation :
  SourceSpanSupportEstablishesHealthCausation → ⊥
sourceSpanSupportDoesNotEstablishHealthCausation ()

sourceSpanSupportDoesNotEstablishRetaliatoryMotive :
  SourceSpanSupportEstablishesRetaliatoryMotive → ⊥
sourceSpanSupportDoesNotEstablishRetaliatoryMotive ()

sourceSpanSupportDoesNotEstablishStatutoryBreach :
  SourceSpanSupportEstablishesStatutoryBreach → ⊥
sourceSpanSupportDoesNotEstablishStatutoryBreach ()

sourceSpanSupportDoesNotCreateLegalAuthority :
  SourceSpanSupportCreatesLegalAuthority → ⊥
sourceSpanSupportDoesNotCreateLegalAuthority ()

record BrightonForm11SourceSpanBoundary : Set where
  constructor brighton-form11-source-span-boundary
  field
    privateArtifactRemainsOutOfRepo : Bool
    artifactDigestPinned : Bool
    exactEvidenceLocatorPinned : Bool
    exactTargetClaimDigestPinned : Bool
    supportedDispositionPaid : Bool
    positiveSupportTritPaid : Bool
    authorityRemainsSeparate : Bool
    publishesPrivateBody : Bool
    establishesHealthCausation : Bool
    establishesRetaliatoryMotive : Bool
    establishesStatutoryBreach : Bool

canonicalBrightonForm11SourceSpanBoundary : BrightonForm11SourceSpanBoundary
canonicalBrightonForm11SourceSpanBoundary =
  brighton-form11-source-span-boundary
    true true true true true true true
    false false false false
