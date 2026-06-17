module DASHI.Crypto.RSAEntropySourceStatisticalBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdapterCanonicalityCore as Adapter
import DASHI.Core.AuthorityBoundary as CoreAuthorityBoundary
import DASHI.Core.AuthorityNonPromotionCore as AuthorityNA
import DASHI.Core.BridgeRequirementCore as Bridge
import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.HiddenLiftProjectionCore as HiddenLift
import DASHI.Core.SourceProcessEvidenceCore as SourceProcessEvidence
import DASHI.Core.StatisticalEvidenceCore as StatisticalEvidence
import DASHI.Promotion.AuthorityBoundaryCore as PromotionAuthorityBoundary
import DASHI.Crypto.RSAVulnerabilityBoundary as RSAVulnerabilityBoundary

------------------------------------------------------------------------
-- RSA same-source entropy / generator statistical boundary.
--
-- This module records a candidate-only receipt surface for same-source
-- entropy and generator diagnostics.  It keeps the evidence vocabulary
-- local, consumes the reusable core receipts, and fail-closes every
-- authority-bearing interpretation.  A statistical anomaly is treated as a
-- candidate only: it is not a cryptographic break, not factor recovery, not
-- causal proof, not source compromise, and not advisory or promotion
-- authority.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Vocabulary.

data RSAEntropySourceStatisticalKind : Set where
  entropySourceCandidateKind :
    RSAEntropySourceStatisticalKind

  generatorHealthModelKind :
    RSAEntropySourceStatisticalKind

  modulusDistributionStatisticKind :
    RSAEntropySourceStatisticalKind

  pairwiseGcdStatisticKind :
    RSAEntropySourceStatisticalKind

  residueDistributionStatisticKind :
    RSAEntropySourceStatisticalKind

  anomalyScoreKind :
    RSAEntropySourceStatisticalKind

  nullHypothesisKind :
    RSAEntropySourceStatisticalKind

  sourceWeaknessHypothesisKind :
    RSAEntropySourceStatisticalKind

  statisticalSourceWeaknessCandidateKind :
    RSAEntropySourceStatisticalKind

  namedRSAEntropySourceStatisticalKind :
    String →
    RSAEntropySourceStatisticalKind

canonicalRSAEntropySourceStatisticalKinds :
  List RSAEntropySourceStatisticalKind
canonicalRSAEntropySourceStatisticalKinds =
  entropySourceCandidateKind
  ∷ generatorHealthModelKind
  ∷ modulusDistributionStatisticKind
  ∷ pairwiseGcdStatisticKind
  ∷ residueDistributionStatisticKind
  ∷ anomalyScoreKind
  ∷ nullHypothesisKind
  ∷ sourceWeaknessHypothesisKind
  ∷ statisticalSourceWeaknessCandidateKind
  ∷ []

canonicalRSAEntropySourceStatisticalKindCount : Nat
canonicalRSAEntropySourceStatisticalKindCount =
  listCount canonicalRSAEntropySourceStatisticalKinds

canonicalRSAEntropySourceStatisticalLabels :
  List String
canonicalRSAEntropySourceStatisticalLabels =
  "entropy source candidate"
  ∷ "generator health model"
  ∷ "modulus distribution statistic"
  ∷ "pairwise gcd statistic"
  ∷ "residue distribution statistic"
  ∷ "anomaly score"
  ∷ "null hypothesis"
  ∷ "source weakness hypothesis"
  ∷ "statistical source weakness candidate"
  ∷ []

canonicalRSAEntropySourceStatisticalLabelCount : Nat
canonicalRSAEntropySourceStatisticalLabelCount =
  listCount canonicalRSAEntropySourceStatisticalLabels

canonicalRSAEntropySourceStatisticalBoundaryClaims :
  List PromotionAuthorityBoundary.AuthorityBoundaryClaimKind
canonicalRSAEntropySourceStatisticalBoundaryClaims =
  PromotionAuthorityBoundary.canonicalBlockedAuthorityClaims

canonicalRSAEntropySourceStatisticalBoundaryClaimCount : Nat
canonicalRSAEntropySourceStatisticalBoundaryClaimCount =
  listCount canonicalRSAEntropySourceStatisticalBoundaryClaims

canonicalRSAEntropySourceStatisticalBoundaryStatement :
  String
canonicalRSAEntropySourceStatisticalBoundaryStatement =
  "same-source RSA entropy and generator diagnostics are candidate-only statistical evidence"

canonicalRSAEntropySourceStatisticalBoundaryRemainingGap :
  String
canonicalRSAEntropySourceStatisticalBoundaryRemainingGap =
  "the anomaly remains a statistical source-weakness candidate; no cryptographic break, factor recovery, causal proof, source compromise, advisory authority, or promotion authority is supplied"

canonicalRSAEntropySourceStatisticalBoundaryLabel :
  String
canonicalRSAEntropySourceStatisticalBoundaryLabel =
  "RSA entropy-source statistical boundary"

canonicalRSAEntropySourceStatisticalBoundaryOwner :
  String
canonicalRSAEntropySourceStatisticalBoundaryOwner =
  "DASHI.Crypto.RSAEntropySourceStatisticalBoundary"

canonicalRSAEntropySourceStatisticalBoundarySurfaceName :
  String
canonicalRSAEntropySourceStatisticalBoundarySurfaceName =
  "canonicalRSAEntropySourceStatisticalBoundary"

------------------------------------------------------------------------
-- Canonical nested receipts.

canonicalRSAEntropySourceCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalRSAEntropySourceCandidateRow =
  CandidateOnly.mkCandidateOnlyRow
    "RSA entropy-source statistical candidate"
    canonicalRSAEntropySourceStatisticalBoundaryOwner
    "canonicalRSAEntropySourceCandidateRow"
    (CandidateOnly.namedCandidateKind
      "rsa entropy-source statistical candidate")
    (CandidateOnly.namedCandidateOnlyStatus
      "rsa entropy-source statistical candidate status")
    "same-source entropy and generator statistics are candidate-only evidence"
    canonicalRSAEntropySourceStatisticalBoundaryRemainingGap

canonicalRSAEntropySourceCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt canonicalRSAEntropySourceCandidateRow
canonicalRSAEntropySourceCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalRSAEntropySourceCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalRSAEntropySourceCitationAuthorityBoundary :
  CoreAuthorityBoundary.CitationAuthorityNoArtifact
canonicalRSAEntropySourceCitationAuthorityBoundary =
  CoreAuthorityBoundary.mkCitationAuthorityNoArtifact
    (CoreAuthorityBoundary.mkAuthorityBoundary
      CoreAuthorityBoundary.CitationAuthority
      refl
      "RSA entropy-source statistical boundary citation"
      canonicalRSAEntropySourceStatisticalBoundaryOwner
      true
      false
      false
      []
    )
    refl
    refl
    refl

canonicalRSAEntropySourcePromotionAuthorityBundle :
  AuthorityNA.AuthorityNonPromotionBundle
canonicalRSAEntropySourcePromotionAuthorityBundle =
  AuthorityNA.canonicalAuthorityNonPromotionBundle

canonicalRSAEntropySourceBridgeRequirementReceipt :
  Bridge.BridgeRequirementCoreReceipt
canonicalRSAEntropySourceBridgeRequirementReceipt =
  Bridge.canonicalBridgeRequirementCoreReceipt

canonicalRSAEntropySourceStatisticalEvidenceReceipt :
  StatisticalEvidence.StatisticalEvidenceReceipt
    StatisticalEvidence.canonicalStatisticalEvidenceSurface
canonicalRSAEntropySourceStatisticalEvidenceReceipt =
  StatisticalEvidence.canonicalStatisticalEvidenceReceipt

canonicalRSAEntropySourceProjectionShadowAdapterReceipt :
  Adapter.AdapterCanonicalityReceipt
    HiddenLift.ProjectionShadow
    HiddenLift.shadowedProjection
canonicalRSAEntropySourceProjectionShadowAdapterReceipt =
  Adapter.mkCanonicalAdapterReceipt
    "RSA entropy-source projection shadow adapter"
    canonicalRSAEntropySourceStatisticalBoundaryOwner
    "canonicalRSAEntropySourceProjectionShadowAdapterReceipt"
    (Adapter.namedAdapterKind "projection shadow")
    HiddenLift.shadowedProjection

canonicalRSAEntropySourceRSAVulnerabilityBoundary :
  RSAVulnerabilityBoundary.RSAVulnerabilityBoundary
canonicalRSAEntropySourceRSAVulnerabilityBoundary =
  RSAVulnerabilityBoundary.canonicalRSAVulnerabilityBoundary

canonicalRSAEntropySourceGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalRSAEntropySourceGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    canonicalRSAEntropySourceStatisticalBoundaryLabel
    canonicalRSAEntropySourceStatisticalBoundaryOwner
    canonicalRSAEntropySourceStatisticalBoundarySurfaceName
    canonicalRSAEntropySourceStatisticalBoundaryStatement
    canonicalRSAEntropySourceStatisticalBoundaryRemainingGap
    "agda -i . DASHI/Crypto/RSAEntropySourceStatisticalBoundary.agda"

------------------------------------------------------------------------
-- Boundary surface.

record RSAEntropySourceStatisticalBoundarySurface : Set where
  constructor mkRSAEntropySourceStatisticalBoundarySurface
  field
    boundaryLabel :
      String

    boundaryOwner :
      String

    boundarySurfaceName :
      String

    boundaryGenericReceipt :
      GenericReceipt.GenericReceipt

    boundaryCandidateRow :
      CandidateOnly.CandidateOnlyRow

    boundaryCandidateReceipt :
      CandidateOnly.CandidateOnlyReceipt boundaryCandidateRow

    boundaryCitationAuthorityBoundary :
      CoreAuthorityBoundary.CitationAuthorityNoArtifact

    boundaryPromotionAuthorityBundle :
      AuthorityNA.AuthorityNonPromotionBundle

    boundaryBridgeRequirementReceipt :
      Bridge.BridgeRequirementCoreReceipt

    boundaryStatisticalEvidenceReceipt :
      StatisticalEvidence.StatisticalEvidenceReceipt
        StatisticalEvidence.canonicalStatisticalEvidenceSurface

    boundarySourceProcessEvidenceReceipt :
      SourceProcessEvidence.SourceProcessEvidenceReceipt
        SourceProcessEvidence.canonicalSourceProcessEvidenceSurface

    boundaryProjectionShadowAdapterReceipt :
      Adapter.AdapterCanonicalityReceipt
        HiddenLift.ProjectionShadow
        HiddenLift.shadowedProjection

    boundaryRSAVulnerabilityBoundary :
      RSAVulnerabilityBoundary.RSAVulnerabilityBoundary

    boundaryKinds :
      List RSAEntropySourceStatisticalKind

    boundaryKindsAreCanonical :
      boundaryKinds ≡ canonicalRSAEntropySourceStatisticalKinds

    boundaryLabels :
      List String

    boundaryLabelsAreCanonical :
      boundaryLabels ≡ canonicalRSAEntropySourceStatisticalLabels

    boundaryClaims :
      List PromotionAuthorityBoundary.AuthorityBoundaryClaimKind

    boundaryClaimsAreCanonical :
      boundaryClaims ≡ canonicalRSAEntropySourceStatisticalBoundaryClaims

    cryptographicBreakClaim :
      Bool

    cryptographicBreakClaimIsFalse :
      cryptographicBreakClaim ≡ false

    factorRecoveryClaim :
      Bool

    factorRecoveryClaimIsFalse :
      factorRecoveryClaim ≡ false

    causalProofClaim :
      Bool

    causalProofClaimIsFalse :
      causalProofClaim ≡ false

    sourceCompromiseClaim :
      Bool

    sourceCompromiseClaimIsFalse :
      sourceCompromiseClaim ≡ false

    advisoryAuthorityClaim :
      Bool

    advisoryAuthorityClaimIsFalse :
      advisoryAuthorityClaim ≡ false

    promotionAuthorityClaim :
      Bool

    promotionAuthorityClaimIsFalse :
      promotionAuthorityClaim ≡ false

    boundaryStatement :
      String

    boundaryRemainingGap :
      String

open RSAEntropySourceStatisticalBoundarySurface public

------------------------------------------------------------------------
-- Boundary receipt.

record RSAEntropySourceStatisticalBoundaryReceipt
  (surface : RSAEntropySourceStatisticalBoundarySurface) :
  Set where
  constructor mkRSAEntropySourceStatisticalBoundaryReceipt
  field
    receiptCandidateOnlyIsTrue :
      CandidateOnly.candidateOnly
        (boundaryCandidateRow surface)
      ≡
      true

    receiptPromotedIsFalse :
      CandidateOnly.promoted
        (boundaryCandidateRow surface)
      ≡
      false

    receiptNoTruthAuthority :
      CandidateOnly.carriesTruthAuthority
        (boundaryCandidateRow surface)
      ≡
      false

    receiptNoSupportAuthority :
      CandidateOnly.carriesSupportAuthority
        (boundaryCandidateRow surface)
      ≡
      false

    receiptNoAdmissibilityAuthority :
      CandidateOnly.carriesAdmissibilityAuthority
        (boundaryCandidateRow surface)
      ≡
      false

    receiptNoTradingAuthority :
      CandidateOnly.carriesTradingAuthority
        (boundaryCandidateRow surface)
      ≡
      false

    receiptNoRuntimeAuthority :
      CandidateOnly.carriesRuntimeAuthority
        (boundaryCandidateRow surface)
      ≡
      false

    receiptNoTheoremAuthority :
      CandidateOnly.carriesTheoremAuthority
        (boundaryCandidateRow surface)
      ≡
      false

    receiptGenericReceiptNonPromoting :
      GenericReceipt.promotesClaim
        (boundaryGenericReceipt surface)
      ≡
      false

    receiptCitationAuthorityAcceptedIsTrue :
      CoreAuthorityBoundary.authorityAccepted
        (CoreAuthorityBoundary.citationBoundary
          (boundaryCitationAuthorityBoundary surface))
      ≡
      true

    receiptCitationArtifactAuthorityIsFalse :
      CoreAuthorityBoundary.artifactAuthority
        (CoreAuthorityBoundary.citationBoundary
          (boundaryCitationAuthorityBoundary surface))
      ≡
      false

    receiptCitationMachineReadableArtifactPresentIsFalse :
      CoreAuthorityBoundary.machineReadableArtifactPresent
        (CoreAuthorityBoundary.citationBoundary
          (boundaryCitationAuthorityBoundary surface))
      ≡
      false

    receiptPromotionAuthorityBundlePromotesAnyAuthorityIsFalse :
      AuthorityNA.promotesAnyAuthority
        (boundaryPromotionAuthorityBundle surface)
      ≡
      false

    receiptSourceProcessEvidenceReceipt :
      SourceProcessEvidence.SourceProcessEvidenceReceipt
        SourceProcessEvidence.canonicalSourceProcessEvidenceSurface

    receiptStatisticalAnomalyCandidateOnlyIsTrue :
      SourceProcessEvidence.statisticalAnomalyCandidateOnly
        SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
      ≡
      true

    receiptStatisticalAnomalySourceCompromiseAuthorityIsFalse :
      SourceProcessEvidence.statisticalAnomalySourceCompromiseAuthority
        SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
      ≡
      false

    receiptSourceWideEscalationAuthorityIsFalse :
      SourceProcessEvidence.sourceWideEscalationAuthority
        SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
      ≡
      false

    receiptKindsAreCanonical :
      boundaryKinds surface
      ≡
      canonicalRSAEntropySourceStatisticalKinds

    receiptLabelsAreCanonical :
      boundaryLabels surface
      ≡
      canonicalRSAEntropySourceStatisticalLabels

    receiptClaimsAreCanonical :
      boundaryClaims surface
      ≡
      canonicalRSAEntropySourceStatisticalBoundaryClaims

    receiptCryptographicBreakClaimIsFalse :
      cryptographicBreakClaim surface ≡ false

    receiptFactorRecoveryClaimIsFalse :
      factorRecoveryClaim surface ≡ false

    receiptCausalProofClaimIsFalse :
      causalProofClaim surface ≡ false

    receiptSourceCompromiseClaimIsFalse :
      sourceCompromiseClaim surface ≡ false

    receiptAdvisoryAuthorityClaimIsFalse :
      advisoryAuthorityClaim surface ≡ false

    receiptPromotionAuthorityClaimIsFalse :
      promotionAuthorityClaim surface ≡ false

    receiptBoundaryStatementIsCanonical :
      boundaryStatement surface ≡
      canonicalRSAEntropySourceStatisticalBoundaryStatement

    receiptBoundaryRemainingGapIsCanonical :
      boundaryRemainingGap surface ≡
      canonicalRSAEntropySourceStatisticalBoundaryRemainingGap

open RSAEntropySourceStatisticalBoundaryReceipt public

------------------------------------------------------------------------
-- Canonical boundary surface and receipt.

canonicalRSAEntropySourceStatisticalBoundarySurface :
  RSAEntropySourceStatisticalBoundarySurface
canonicalRSAEntropySourceStatisticalBoundarySurface =
  mkRSAEntropySourceStatisticalBoundarySurface
    canonicalRSAEntropySourceStatisticalBoundaryLabel
    canonicalRSAEntropySourceStatisticalBoundaryOwner
    canonicalRSAEntropySourceStatisticalBoundarySurfaceName
    canonicalRSAEntropySourceGenericReceipt
    canonicalRSAEntropySourceCandidateRow
    canonicalRSAEntropySourceCandidateReceipt
    canonicalRSAEntropySourceCitationAuthorityBoundary
    canonicalRSAEntropySourcePromotionAuthorityBundle
    canonicalRSAEntropySourceBridgeRequirementReceipt
    canonicalRSAEntropySourceStatisticalEvidenceReceipt
    SourceProcessEvidence.canonicalSourceProcessEvidenceReceipt
    canonicalRSAEntropySourceProjectionShadowAdapterReceipt
    canonicalRSAEntropySourceRSAVulnerabilityBoundary
    canonicalRSAEntropySourceStatisticalKinds
    refl
    canonicalRSAEntropySourceStatisticalLabels
    refl
    canonicalRSAEntropySourceStatisticalBoundaryClaims
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    canonicalRSAEntropySourceStatisticalBoundaryStatement
    canonicalRSAEntropySourceStatisticalBoundaryRemainingGap

canonicalRSAEntropySourceStatisticalBoundaryReceipt :
  RSAEntropySourceStatisticalBoundaryReceipt
    canonicalRSAEntropySourceStatisticalBoundarySurface
canonicalRSAEntropySourceStatisticalBoundaryReceipt =
  mkRSAEntropySourceStatisticalBoundaryReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    SourceProcessEvidence.canonicalSourceProcessEvidenceReceipt
    SourceProcessEvidence.statisticalAnomalyCandidateOnlyIsTrue
    SourceProcessEvidence.statisticalAnomalySourceCompromiseAuthorityIsFalse
    SourceProcessEvidence.sourceWideEscalationAuthorityIsFalse
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

------------------------------------------------------------------------
-- Projection lemmas.

rsaEntropySourceCandidateOnlyIsTrue :
  CandidateOnly.candidateOnly
    (boundaryCandidateRow
      canonicalRSAEntropySourceStatisticalBoundarySurface)
  ≡
  true
rsaEntropySourceCandidateOnlyIsTrue =
  receiptCandidateOnlyIsTrue
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourcePromotedIsFalse :
  CandidateOnly.promoted
    (boundaryCandidateRow
      canonicalRSAEntropySourceStatisticalBoundarySurface)
  ≡
  false
rsaEntropySourcePromotedIsFalse =
  receiptPromotedIsFalse
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceNoTruthAuthority :
  CandidateOnly.carriesTruthAuthority
    (boundaryCandidateRow
      canonicalRSAEntropySourceStatisticalBoundarySurface)
  ≡
  false
rsaEntropySourceNoTruthAuthority =
  receiptNoTruthAuthority
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceNoSupportAuthority :
  CandidateOnly.carriesSupportAuthority
    (boundaryCandidateRow
      canonicalRSAEntropySourceStatisticalBoundarySurface)
  ≡
  false
rsaEntropySourceNoSupportAuthority =
  receiptNoSupportAuthority
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceNoAdmissibilityAuthority :
  CandidateOnly.carriesAdmissibilityAuthority
    (boundaryCandidateRow
      canonicalRSAEntropySourceStatisticalBoundarySurface)
  ≡
  false
rsaEntropySourceNoAdmissibilityAuthority =
  receiptNoAdmissibilityAuthority
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceNoTradingAuthority :
  CandidateOnly.carriesTradingAuthority
    (boundaryCandidateRow
      canonicalRSAEntropySourceStatisticalBoundarySurface)
  ≡
  false
rsaEntropySourceNoTradingAuthority =
  receiptNoTradingAuthority
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceNoRuntimeAuthority :
  CandidateOnly.carriesRuntimeAuthority
    (boundaryCandidateRow
      canonicalRSAEntropySourceStatisticalBoundarySurface)
  ≡
  false
rsaEntropySourceNoRuntimeAuthority =
  receiptNoRuntimeAuthority
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceNoTheoremAuthority :
  CandidateOnly.carriesTheoremAuthority
    (boundaryCandidateRow
      canonicalRSAEntropySourceStatisticalBoundarySurface)
  ≡
  false
rsaEntropySourceNoTheoremAuthority =
  receiptNoTheoremAuthority
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim
    (boundaryGenericReceipt
      canonicalRSAEntropySourceStatisticalBoundarySurface)
  ≡
  false
rsaEntropySourceGenericReceiptNonPromoting =
  receiptGenericReceiptNonPromoting
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceCitationAuthorityAcceptedIsTrue :
  CoreAuthorityBoundary.authorityAccepted
    (CoreAuthorityBoundary.citationBoundary
      (boundaryCitationAuthorityBoundary
        canonicalRSAEntropySourceStatisticalBoundarySurface))
  ≡
  true
rsaEntropySourceCitationAuthorityAcceptedIsTrue =
  receiptCitationAuthorityAcceptedIsTrue
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceCitationArtifactAuthorityIsFalse :
  CoreAuthorityBoundary.artifactAuthority
    (CoreAuthorityBoundary.citationBoundary
      (boundaryCitationAuthorityBoundary
        canonicalRSAEntropySourceStatisticalBoundarySurface))
  ≡
  false
rsaEntropySourceCitationArtifactAuthorityIsFalse =
  receiptCitationArtifactAuthorityIsFalse
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceCitationMachineReadableArtifactPresentIsFalse :
  CoreAuthorityBoundary.machineReadableArtifactPresent
    (CoreAuthorityBoundary.citationBoundary
      (boundaryCitationAuthorityBoundary
        canonicalRSAEntropySourceStatisticalBoundarySurface))
  ≡
  false
rsaEntropySourceCitationMachineReadableArtifactPresentIsFalse =
  receiptCitationMachineReadableArtifactPresentIsFalse
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourcePromotionAuthorityBundlePromotesAnyAuthorityIsFalse :
  AuthorityNA.promotesAnyAuthority
    (boundaryPromotionAuthorityBundle
      canonicalRSAEntropySourceStatisticalBoundarySurface)
  ≡
  false
rsaEntropySourcePromotionAuthorityBundlePromotesAnyAuthorityIsFalse =
  receiptPromotionAuthorityBundlePromotesAnyAuthorityIsFalse
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceStatisticalAnomalyCandidateOnlyIsTrue :
  SourceProcessEvidence.statisticalAnomalyCandidateOnly
    SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
  ≡
  true
rsaEntropySourceStatisticalAnomalyCandidateOnlyIsTrue =
  receiptStatisticalAnomalyCandidateOnlyIsTrue
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceStatisticalAnomalySourceCompromiseAuthorityIsFalse :
  SourceProcessEvidence.statisticalAnomalySourceCompromiseAuthority
    SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
  ≡
  false
rsaEntropySourceStatisticalAnomalySourceCompromiseAuthorityIsFalse =
  receiptStatisticalAnomalySourceCompromiseAuthorityIsFalse
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceSourceWideEscalationAuthorityIsFalse :
  SourceProcessEvidence.sourceWideEscalationAuthority
    SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
  ≡
  false
rsaEntropySourceSourceWideEscalationAuthorityIsFalse =
  receiptSourceWideEscalationAuthorityIsFalse
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceKindsAreCanonical :
  boundaryKinds
    canonicalRSAEntropySourceStatisticalBoundarySurface
  ≡
  canonicalRSAEntropySourceStatisticalKinds
rsaEntropySourceKindsAreCanonical =
  receiptKindsAreCanonical
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceLabelsAreCanonical :
  boundaryLabels
    canonicalRSAEntropySourceStatisticalBoundarySurface
  ≡
  canonicalRSAEntropySourceStatisticalLabels
rsaEntropySourceLabelsAreCanonical =
  receiptLabelsAreCanonical
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceClaimsAreCanonical :
  boundaryClaims
    canonicalRSAEntropySourceStatisticalBoundarySurface
  ≡
  canonicalRSAEntropySourceStatisticalBoundaryClaims
rsaEntropySourceClaimsAreCanonical =
  receiptClaimsAreCanonical
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceCryptographicBreakClaimIsFalse :
  cryptographicBreakClaim
    canonicalRSAEntropySourceStatisticalBoundarySurface
  ≡
  false
rsaEntropySourceCryptographicBreakClaimIsFalse =
  receiptCryptographicBreakClaimIsFalse
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceFactorRecoveryClaimIsFalse :
  factorRecoveryClaim
    canonicalRSAEntropySourceStatisticalBoundarySurface
  ≡
  false
rsaEntropySourceFactorRecoveryClaimIsFalse =
  receiptFactorRecoveryClaimIsFalse
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceCausalProofClaimIsFalse :
  causalProofClaim
    canonicalRSAEntropySourceStatisticalBoundarySurface
  ≡
  false
rsaEntropySourceCausalProofClaimIsFalse =
  receiptCausalProofClaimIsFalse
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceSourceCompromiseClaimIsFalse :
  sourceCompromiseClaim
    canonicalRSAEntropySourceStatisticalBoundarySurface
  ≡
  false
rsaEntropySourceSourceCompromiseClaimIsFalse =
  receiptSourceCompromiseClaimIsFalse
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceAdvisoryAuthorityClaimIsFalse :
  advisoryAuthorityClaim
    canonicalRSAEntropySourceStatisticalBoundarySurface
  ≡
  false
rsaEntropySourceAdvisoryAuthorityClaimIsFalse =
  receiptAdvisoryAuthorityClaimIsFalse
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourcePromotionAuthorityClaimIsFalse :
  promotionAuthorityClaim
    canonicalRSAEntropySourceStatisticalBoundarySurface
  ≡
  false
rsaEntropySourcePromotionAuthorityClaimIsFalse =
  receiptPromotionAuthorityClaimIsFalse
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceBoundaryStatementIsCanonical :
  boundaryStatement
    canonicalRSAEntropySourceStatisticalBoundarySurface
  ≡
  canonicalRSAEntropySourceStatisticalBoundaryStatement
rsaEntropySourceBoundaryStatementIsCanonical =
  receiptBoundaryStatementIsCanonical
    canonicalRSAEntropySourceStatisticalBoundaryReceipt

rsaEntropySourceBoundaryRemainingGapIsCanonical :
  boundaryRemainingGap
    canonicalRSAEntropySourceStatisticalBoundarySurface
  ≡
  canonicalRSAEntropySourceStatisticalBoundaryRemainingGap
rsaEntropySourceBoundaryRemainingGapIsCanonical =
  receiptBoundaryRemainingGapIsCanonical
    canonicalRSAEntropySourceStatisticalBoundaryReceipt
