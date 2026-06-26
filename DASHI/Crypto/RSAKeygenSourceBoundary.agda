module DASHI.Crypto.RSAKeygenSourceBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdapterCanonicalityCore as Adapter
import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Core.BridgeRequirementCore as Bridge
import DASHI.Core.CandidateOnlyCore as Candidate
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.HiddenLiftProjectionCore as HiddenLift
import DASHI.Core.SourceProcessEvidenceCore as SourceProcessEvidence
import DASHI.Core.SourceProcessEvidenceLawCore as SourceProcessEvidenceLaw
import DASHI.Core.StatisticalEvidenceCore as StatisticalEvidence
import DASHI.Crypto.RSAVulnerabilityBoundary as RSAVulnerabilityBoundary
import DASHI.Promotion.AuthorityBoundaryCore as AuthorityBoundary

------------------------------------------------------------------------
-- Source-conditioned RSA key-generation boundary.
--
-- This module is intentionally candidate-only.  It records the source id,
-- hidden generator state, entropy process, candidate-prime stream,
-- acceptance predicate, observable trace, source-conditioned dataset,
-- emitted modulus, and keygen-source fiber as descriptive vocabulary, while
-- keeping all authority claims fail-closed.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Vocabulary.

data RSAKeygenSourceKind : Set where
  sourceIdKind :
    RSAKeygenSourceKind

  hiddenGeneratorStateKind :
    RSAKeygenSourceKind

  entropyProcessKind :
    RSAKeygenSourceKind

  candidatePrimeStreamKind :
    RSAKeygenSourceKind

  acceptancePredicateKind :
    RSAKeygenSourceKind

  observableTraceKind :
    RSAKeygenSourceKind

  sourceConditionedDatasetKind :
    RSAKeygenSourceKind

  emittedModulusKind :
    RSAKeygenSourceKind

  keygenSourceFiberKind :
    RSAKeygenSourceKind

  namedRSAKeygenSourceKind :
    String →
    RSAKeygenSourceKind

canonicalRSAKeygenSourceKinds :
  List RSAKeygenSourceKind
canonicalRSAKeygenSourceKinds =
  sourceIdKind
  ∷ hiddenGeneratorStateKind
  ∷ entropyProcessKind
  ∷ candidatePrimeStreamKind
  ∷ acceptancePredicateKind
  ∷ observableTraceKind
  ∷ sourceConditionedDatasetKind
  ∷ emittedModulusKind
  ∷ keygenSourceFiberKind
  ∷ []

canonicalRSAKeygenSourceKindCount : Nat
canonicalRSAKeygenSourceKindCount =
  listCount canonicalRSAKeygenSourceKinds

data RSAKeygenSourceAuthorityClaimKind : Set where
  keygenAuthorityClaim :
    RSAKeygenSourceAuthorityClaimKind

  entropyAuthorityClaim :
    RSAKeygenSourceAuthorityClaimKind

  sourceCompromiseAuthorityClaim :
    RSAKeygenSourceAuthorityClaimKind

  productionCryptoSecurityAuthorityClaim :
    RSAKeygenSourceAuthorityClaimKind

  factorRecoveryAuthorityClaim :
    RSAKeygenSourceAuthorityClaimKind

  namedRSAKeygenSourceAuthorityClaimKind :
    String →
    RSAKeygenSourceAuthorityClaimKind

canonicalRSAKeygenSourceAuthorityClaimKinds :
  List RSAKeygenSourceAuthorityClaimKind
canonicalRSAKeygenSourceAuthorityClaimKinds =
  keygenAuthorityClaim
  ∷ entropyAuthorityClaim
  ∷ sourceCompromiseAuthorityClaim
  ∷ productionCryptoSecurityAuthorityClaim
  ∷ factorRecoveryAuthorityClaim
  ∷ []

canonicalRSAKeygenSourceAuthorityClaimCount : Nat
canonicalRSAKeygenSourceAuthorityClaimCount =
  listCount canonicalRSAKeygenSourceAuthorityClaimKinds

data RSAKeygenSourceAdapterKind : Set where
  sourceConditionedKeygenAdapterKind :
    RSAKeygenSourceAdapterKind

  emittedModulusAdapterKind :
    RSAKeygenSourceAdapterKind

  keygenSourceFiberAdapterKind :
    RSAKeygenSourceAdapterKind

  namedRSAKeygenSourceAdapterKind :
    String →
    RSAKeygenSourceAdapterKind

data RSAKeygenSourceAdapterSurface : Set where
  sourceConditionedKeygenAdapter :
    RSAKeygenSourceAdapterSurface

  emittedModulusAdapter :
    RSAKeygenSourceAdapterSurface

  keygenSourceFiberAdapter :
    RSAKeygenSourceAdapterSurface

  namedRSAKeygenSourceAdapter :
    String →
    RSAKeygenSourceAdapterSurface

canonicalRSAKeygenSourceAdapter :
  RSAKeygenSourceAdapterSurface
canonicalRSAKeygenSourceAdapter =
  sourceConditionedKeygenAdapter

------------------------------------------------------------------------
-- Boundary surface.

record RSAKeygenSourceBoundarySurface : Set where
  constructor mkRSAKeygenSourceBoundarySurface
  field
    boundaryLabel :
      String

    boundaryOwner :
      String

    boundarySurface :
      String

    sourceId :
      String

    hiddenGeneratorState :
      String

    entropyProcess :
      String

    candidatePrimeStream :
      String

    acceptancePredicate :
      String

    observableTrace :
      String

    sourceConditionedDataset :
      String

    emittedModulus :
      String

    keygenSourceFiber :
      String

    boundaryKind :
      RSAKeygenSourceKind

    candidateRow :
      Candidate.CandidateOnlyRow

    candidateReceipt :
      Candidate.CandidateOnlyReceipt candidateRow

    authorityBoundaryClaims :
      List AuthorityBoundary.AuthorityBoundaryClaimKind

    authorityBundle :
      Authority.AuthorityNonPromotionBundle

    bridgeReceipt :
      Bridge.BridgeRequirementCoreReceipt

    adapterReceipt :
      Adapter.AdapterCanonicalityReceipt
        RSAKeygenSourceAdapterSurface
        canonicalRSAKeygenSourceAdapter

    hiddenLiftEvidence :
      HiddenLift.HiddenLiftProjectionEvidence

    statisticalEvidence :
      StatisticalEvidence.StatisticalEvidenceReceipt
        StatisticalEvidence.canonicalStatisticalEvidenceSurface

    sourceProcessEvidenceReceipt :
      SourceProcessEvidence.SourceProcessEvidenceReceipt
        SourceProcessEvidence.canonicalSourceProcessEvidenceSurface

    rsaVulnerabilityBoundary :
      RSAVulnerabilityBoundary.RSAVulnerabilityBoundary

    boundaryReceipt :
      GenericReceipt.GenericReceipt

    keygenAuthority :
      Bool

    entropyAuthority :
      Bool

    sourceCompromiseAuthority :
      Bool

    productionCryptoSecurityAuthority :
      Bool

    factorRecoveryAuthority :
      Bool

    boundaryStatement :
      String

    boundaryRemainingGap :
      String

open RSAKeygenSourceBoundarySurface public

record RSAKeygenSourceBoundaryReceipt
  (surface : RSAKeygenSourceBoundarySurface) :
  Set where
  constructor mkRSAKeygenSourceBoundaryReceipt
  field
    receiptCandidateOnlyIsTrue :
      Candidate.candidateOnly (candidateRow surface) ≡ true

    receiptPromotedIsFalse :
      Candidate.promoted (candidateRow surface) ≡ false

    receiptNoTruthAuthority :
      Candidate.carriesTruthAuthority (candidateRow surface) ≡ false

    receiptNoSupportAuthority :
      Candidate.carriesSupportAuthority (candidateRow surface) ≡ false

    receiptNoAdmissibilityAuthority :
      Candidate.carriesAdmissibilityAuthority (candidateRow surface) ≡ false

    receiptNoTradingAuthority :
      Candidate.carriesTradingAuthority (candidateRow surface) ≡ false

    receiptNoRuntimeAuthority :
      Candidate.carriesRuntimeAuthority (candidateRow surface) ≡ false

    receiptNoTheoremAuthority :
      Candidate.carriesTheoremAuthority (candidateRow surface) ≡ false

    receiptKeygenAuthorityIsFalse :
      keygenAuthority surface ≡ false

    receiptEntropyAuthorityIsFalse :
      entropyAuthority surface ≡ false

    receiptSourceCompromiseAuthorityIsFalse :
      sourceCompromiseAuthority surface ≡ false

    receiptProductionCryptoSecurityAuthorityIsFalse :
      productionCryptoSecurityAuthority surface ≡ false

    receiptFactorRecoveryAuthorityIsFalse :
      factorRecoveryAuthority surface ≡ false

    receiptAuthorityBoundaryClaimsCanonical :
      authorityBoundaryClaims surface
      ≡
      AuthorityBoundary.canonicalBlockedAuthorityClaims

    receiptSourceProcessEvidenceCandidateOnlyIsTrue :
      Candidate.candidateOnly
        (SourceProcessEvidence.candidateRow
          SourceProcessEvidence.canonicalSourceProcessEvidenceSurface)
      ≡
      true

    receiptSourceProcessEvidenceSideEvidenceRestrictsFiberIsTrue :
      SourceProcessEvidence.sideEvidenceRestrictsFiber
        SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
      ≡
      true

    receiptSourceProcessEvidenceSourceWideEscalationAuthorityIsFalse :
      SourceProcessEvidence.sourceWideEscalationAuthority
        SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
      ≡
      false

    receiptAuthorityBundlePromotesAnyAuthorityIsFalse :
      Authority.promotesAnyAuthority (authorityBundle surface) ≡ false

    receiptBridgeAuthorityPromotionIsFalse :
      Bridge.receiptAuthorityPromotion (bridgeReceipt surface) ≡ false

    receiptBridgeTransportMapAuthorityIsFalse :
      Bridge.receiptTransportMapAuthority (bridgeReceipt surface) ≡ false

    receiptBridgeBackgroundBridgeAuthorityIsFalse :
      Bridge.receiptBackgroundBridgeAuthority (bridgeReceipt surface) ≡ false

    receiptBoundaryReceiptNonPromoting :
      GenericReceipt.promotesClaim (boundaryReceipt surface) ≡ false

    receiptRSAVulnerabilityBoundaryCandidateOnlyIsTrue :
      RSAVulnerabilityBoundary.boundaryCandidateOnly
        (rsaVulnerabilityBoundary surface) ≡ true

    receiptRSAVulnerabilityBoundaryPromotedIsFalse :
      RSAVulnerabilityBoundary.boundaryPromoted
        (rsaVulnerabilityBoundary surface) ≡ false

open RSAKeygenSourceBoundaryReceipt public

------------------------------------------------------------------------
-- Canonical surface.

canonicalRSAKeygenSourceCandidateRow :
  Candidate.CandidateOnlyRow
canonicalRSAKeygenSourceCandidateRow =
  Candidate.mkCandidateOnlyRow
    "RSA keygen source boundary candidate"
    "DASHI.Crypto.RSAKeygenSourceBoundary"
    "canonicalRSAKeygenSourceCandidateRow"
    Candidate.operatorCandidateKind
    Candidate.operatorCandidateOnlyStatus
    "source id, hidden generator state, entropy process, candidate-prime stream, acceptance predicate, observable trace, source-conditioned dataset, emitted modulus, and keygen-source fiber are recorded as candidate-only vocabulary"
    "keygen authority, entropy authority, source-compromise authority, production crypto/security authority, and factor-recovery authority stay closed"

canonicalRSAKeygenSourceCandidateReceipt :
  Candidate.CandidateOnlyReceipt canonicalRSAKeygenSourceCandidateRow
canonicalRSAKeygenSourceCandidateReceipt =
  Candidate.canonicalCandidateOnlyReceipt
    canonicalRSAKeygenSourceCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalRSAKeygenSourceAuthorityBundle :
  Authority.AuthorityNonPromotionBundle
canonicalRSAKeygenSourceAuthorityBundle =
  Authority.canonicalAuthorityNonPromotionBundle

canonicalRSAKeygenSourceBridgeReceipt :
  Bridge.BridgeRequirementCoreReceipt
canonicalRSAKeygenSourceBridgeReceipt =
  Bridge.canonicalBridgeRequirementCoreReceipt

canonicalRSAKeygenSourceAdapterReceipt :
  Adapter.AdapterCanonicalityReceipt
    RSAKeygenSourceAdapterSurface
    canonicalRSAKeygenSourceAdapter
canonicalRSAKeygenSourceAdapterReceipt =
  Adapter.mkCanonicalAdapterReceipt
    "RSA keygen source adapter"
    "DASHI.Crypto.RSAKeygenSourceBoundary"
    "canonicalRSAKeygenSourceAdapter"
    Adapter.genericAdapterKind
    canonicalRSAKeygenSourceAdapter

canonicalRSAKeygenSourceHiddenLiftEvidence :
  HiddenLift.HiddenLiftProjectionEvidence
canonicalRSAKeygenSourceHiddenLiftEvidence =
  HiddenLift.canonicalHiddenLiftProjectionEvidence

canonicalRSAKeygenSourceStatisticalEvidence :
  StatisticalEvidence.StatisticalEvidenceReceipt
    StatisticalEvidence.canonicalStatisticalEvidenceSurface
canonicalRSAKeygenSourceStatisticalEvidence =
  StatisticalEvidence.canonicalStatisticalEvidenceReceipt

canonicalRSAKeygenSourceProcessEvidenceReceipt :
  SourceProcessEvidence.SourceProcessEvidenceReceipt
    SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
canonicalRSAKeygenSourceProcessEvidenceReceipt =
  SourceProcessEvidence.canonicalSourceProcessEvidenceReceipt

canonicalRSAKeygenSourceVulnerabilityBoundary :
  RSAVulnerabilityBoundary.RSAVulnerabilityBoundary
canonicalRSAKeygenSourceVulnerabilityBoundary =
  RSAVulnerabilityBoundary.canonicalRSAVulnerabilityBoundary

canonicalRSAKeygenSourceBoundaryGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalRSAKeygenSourceBoundaryGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "RSA keygen source boundary receipt"
    "DASHI.Crypto.RSAKeygenSourceBoundary"
    "canonicalRSAKeygenSourceBoundaryReceipt"
    "source-conditioned RSA key generation is recorded as candidate-only boundary bookkeeping"
    "the module does not promote keygen authority, entropy authority, source-compromise authority, production crypto/security authority, or factor-recovery authority"
    "agda -i . DASHI/Crypto/RSAKeygenSourceBoundary.agda"

canonicalRSAKeygenSourceBoundarySurface :
  RSAKeygenSourceBoundarySurface
canonicalRSAKeygenSourceBoundarySurface =
  mkRSAKeygenSourceBoundarySurface
    "RSA keygen source boundary"
    "DASHI.Crypto.RSAKeygenSourceBoundary"
    "candidate-only RSA keygen source boundary"
    "rsa-source-id"
    "hidden generator state is treated as private and non-authoritative"
    "entropy process is descriptive only and does not promote entropy authority"
    "candidate-prime stream is a candidate-only stream"
    "acceptance predicate is local and fail-closed"
    "observable trace is recorded as descriptive evidence"
    "source-conditioned dataset is a candidate-only dataset summary"
    "emitted modulus n = p * q is tracked as a boundary label"
    "keygen source fiber"
    sourceConditionedDatasetKind
    canonicalRSAKeygenSourceCandidateRow
    canonicalRSAKeygenSourceCandidateReceipt
    AuthorityBoundary.canonicalBlockedAuthorityClaims
    canonicalRSAKeygenSourceAuthorityBundle
    canonicalRSAKeygenSourceBridgeReceipt
    canonicalRSAKeygenSourceAdapterReceipt
    canonicalRSAKeygenSourceHiddenLiftEvidence
    canonicalRSAKeygenSourceStatisticalEvidence
    canonicalRSAKeygenSourceProcessEvidenceReceipt
    canonicalRSAKeygenSourceVulnerabilityBoundary
    canonicalRSAKeygenSourceBoundaryGenericReceipt
    false
    false
    false
    false
    false
    "source-conditioned RSA key generation remains candidate-only"
    "all crypto/security/factor-recovery authority lanes remain closed"

canonicalRSAKeygenSourceBoundaryReceipt :
  RSAKeygenSourceBoundaryReceipt canonicalRSAKeygenSourceBoundarySurface
canonicalRSAKeygenSourceBoundaryReceipt =
  mkRSAKeygenSourceBoundaryReceipt
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

canonicalRSAKeygenSourceCandidateOnlyIsTrue :
  Candidate.candidateOnly canonicalRSAKeygenSourceCandidateRow ≡ true
canonicalRSAKeygenSourceCandidateOnlyIsTrue =
  receiptCandidateOnlyIsTrue canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourcePromotedIsFalse :
  Candidate.promoted canonicalRSAKeygenSourceCandidateRow ≡ false
canonicalRSAKeygenSourcePromotedIsFalse =
  receiptPromotedIsFalse canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceNoTruthAuthority :
  Candidate.carriesTruthAuthority canonicalRSAKeygenSourceCandidateRow ≡ false
canonicalRSAKeygenSourceNoTruthAuthority =
  receiptNoTruthAuthority canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceNoSupportAuthority :
  Candidate.carriesSupportAuthority canonicalRSAKeygenSourceCandidateRow ≡ false
canonicalRSAKeygenSourceNoSupportAuthority =
  receiptNoSupportAuthority canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceNoAdmissibilityAuthority :
  Candidate.carriesAdmissibilityAuthority
    canonicalRSAKeygenSourceCandidateRow
  ≡
  false
canonicalRSAKeygenSourceNoAdmissibilityAuthority =
  receiptNoAdmissibilityAuthority canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceNoTradingAuthority :
  Candidate.carriesTradingAuthority canonicalRSAKeygenSourceCandidateRow ≡ false
canonicalRSAKeygenSourceNoTradingAuthority =
  receiptNoTradingAuthority canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceNoRuntimeAuthority :
  Candidate.carriesRuntimeAuthority canonicalRSAKeygenSourceCandidateRow ≡ false
canonicalRSAKeygenSourceNoRuntimeAuthority =
  receiptNoRuntimeAuthority canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceNoTheoremAuthority :
  Candidate.carriesTheoremAuthority canonicalRSAKeygenSourceCandidateRow ≡ false
canonicalRSAKeygenSourceNoTheoremAuthority =
  receiptNoTheoremAuthority canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceKeygenAuthorityIsFalse :
  keygenAuthority canonicalRSAKeygenSourceBoundarySurface ≡ false
canonicalRSAKeygenSourceKeygenAuthorityIsFalse =
  receiptKeygenAuthorityIsFalse canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceEntropyAuthorityIsFalse :
  entropyAuthority canonicalRSAKeygenSourceBoundarySurface ≡ false
canonicalRSAKeygenSourceEntropyAuthorityIsFalse =
  receiptEntropyAuthorityIsFalse canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceSourceCompromiseAuthorityIsFalse :
  sourceCompromiseAuthority canonicalRSAKeygenSourceBoundarySurface ≡ false
canonicalRSAKeygenSourceSourceCompromiseAuthorityIsFalse =
  receiptSourceCompromiseAuthorityIsFalse canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceProductionCryptoSecurityAuthorityIsFalse :
  productionCryptoSecurityAuthority canonicalRSAKeygenSourceBoundarySurface ≡ false
canonicalRSAKeygenSourceProductionCryptoSecurityAuthorityIsFalse =
  receiptProductionCryptoSecurityAuthorityIsFalse
    canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceFactorRecoveryAuthorityIsFalse :
  factorRecoveryAuthority canonicalRSAKeygenSourceBoundarySurface ≡ false
canonicalRSAKeygenSourceFactorRecoveryAuthorityIsFalse =
  receiptFactorRecoveryAuthorityIsFalse canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceAuthorityBoundaryClaimsCanonical :
  authorityBoundaryClaims canonicalRSAKeygenSourceBoundarySurface
  ≡
  AuthorityBoundary.canonicalBlockedAuthorityClaims
canonicalRSAKeygenSourceAuthorityBoundaryClaimsCanonical =
  receiptAuthorityBoundaryClaimsCanonical
    canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceSourceProcessEvidenceCandidateOnlyIsTrue :
  Candidate.candidateOnly
    (SourceProcessEvidence.candidateRow
      SourceProcessEvidence.canonicalSourceProcessEvidenceSurface)
  ≡
  true
canonicalRSAKeygenSourceSourceProcessEvidenceCandidateOnlyIsTrue =
  receiptSourceProcessEvidenceCandidateOnlyIsTrue
    canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceSourceProcessEvidenceSideEvidenceRestrictsFiberIsTrue :
  SourceProcessEvidence.sideEvidenceRestrictsFiber
    SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
  ≡
  true
canonicalRSAKeygenSourceSourceProcessEvidenceSideEvidenceRestrictsFiberIsTrue =
  receiptSourceProcessEvidenceSideEvidenceRestrictsFiberIsTrue
    canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceSourceProcessEvidenceSourceWideEscalationAuthorityIsFalse :
  SourceProcessEvidence.sourceWideEscalationAuthority
    SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
  ≡
  false
canonicalRSAKeygenSourceSourceProcessEvidenceSourceWideEscalationAuthorityIsFalse =
  receiptSourceProcessEvidenceSourceWideEscalationAuthorityIsFalse
    canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceAuthorityBundlePromotesAnyAuthorityIsFalse :
  Authority.promotesAnyAuthority
    canonicalRSAKeygenSourceAuthorityBundle
  ≡
  false
canonicalRSAKeygenSourceAuthorityBundlePromotesAnyAuthorityIsFalse =
  receiptAuthorityBundlePromotesAnyAuthorityIsFalse
    canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceBridgeAuthorityPromotionIsFalse :
  Bridge.receiptAuthorityPromotion canonicalRSAKeygenSourceBridgeReceipt ≡ false
canonicalRSAKeygenSourceBridgeAuthorityPromotionIsFalse =
  receiptBridgeAuthorityPromotionIsFalse canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceBridgeTransportMapAuthorityIsFalse :
  Bridge.receiptTransportMapAuthority canonicalRSAKeygenSourceBridgeReceipt ≡ false
canonicalRSAKeygenSourceBridgeTransportMapAuthorityIsFalse =
  receiptBridgeTransportMapAuthorityIsFalse canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceBridgeBackgroundBridgeAuthorityIsFalse :
  Bridge.receiptBackgroundBridgeAuthority canonicalRSAKeygenSourceBridgeReceipt ≡ false
canonicalRSAKeygenSourceBridgeBackgroundBridgeAuthorityIsFalse =
  receiptBridgeBackgroundBridgeAuthorityIsFalse canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceBoundaryReceiptNonPromoting :
  GenericReceipt.promotesClaim canonicalRSAKeygenSourceBoundaryGenericReceipt ≡ false
canonicalRSAKeygenSourceBoundaryReceiptNonPromoting =
  refl

canonicalRSAKeygenSourceVulnerabilityBoundaryCandidateOnlyIsTrue :
  RSAVulnerabilityBoundary.boundaryCandidateOnly
    canonicalRSAKeygenSourceVulnerabilityBoundary
  ≡
  true
canonicalRSAKeygenSourceVulnerabilityBoundaryCandidateOnlyIsTrue =
  receiptRSAVulnerabilityBoundaryCandidateOnlyIsTrue
    canonicalRSAKeygenSourceBoundaryReceipt

canonicalRSAKeygenSourceVulnerabilityBoundaryPromotedIsFalse :
  RSAVulnerabilityBoundary.boundaryPromoted
    canonicalRSAKeygenSourceVulnerabilityBoundary
  ≡
  false
canonicalRSAKeygenSourceVulnerabilityBoundaryPromotedIsFalse =
  receiptRSAVulnerabilityBoundaryPromotedIsFalse
    canonicalRSAKeygenSourceBoundaryReceipt
