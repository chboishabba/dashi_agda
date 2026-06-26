module DASHI.Crypto.RSAIterationLeakBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdapterCanonicalityCore as Adapter
import DASHI.Core.BridgeRequirementCore as Bridge
import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.HiddenLiftProjectionCore as HiddenLift
import DASHI.Core.SourceProcessEvidenceCore as SourceProcessEvidence
import DASHI.Core.SourceProcessEvidenceLawCore as SourceProcessEvidenceLaw
import DASHI.Core.StatisticalEvidenceCore as Statistical
import DASHI.Crypto.RSAVulnerabilityBoundary as RSAVulnerabilityBoundary
import DASHI.Promotion.AuthorityBoundaryCore as AuthorityBoundary

------------------------------------------------------------------------
-- RSA keygen iteration-leak boundary.
--
-- This module is candidate-only.  It names the side-information vocabulary
-- for iteration-count, rejection-count, timing-count, candidate-draw index,
-- rejection path, acceptance trace, generator context, constrained
-- candidate-prime set, source-fiber shrink candidate, and search-cost
-- reduction candidate surfaces.  Every authority-bearing lane is blocked.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Vocabulary.

data RSAIterationLeakVocabularyKind : Set where
  iterationCountTraceVocabularyKind :
    RSAIterationLeakVocabularyKind

  candidateDrawIndexVocabularyKind :
    RSAIterationLeakVocabularyKind

  rejectionPathVocabularyKind :
    RSAIterationLeakVocabularyKind

  acceptanceTraceVocabularyKind :
    RSAIterationLeakVocabularyKind

  knownGeneratorContextVocabularyKind :
    RSAIterationLeakVocabularyKind

  constrainedCandidatePrimeSetVocabularyKind :
    RSAIterationLeakVocabularyKind

  sourceFiberShrinkCandidateVocabularyKind :
    RSAIterationLeakVocabularyKind

  searchCostReductionCandidateVocabularyKind :
    RSAIterationLeakVocabularyKind

  rejectionCountVocabularyKind :
    RSAIterationLeakVocabularyKind

  timingCountVocabularyKind :
    RSAIterationLeakVocabularyKind

  namedRSAIterationLeakVocabularyKind :
    String →
    RSAIterationLeakVocabularyKind

canonicalRSAIterationLeakVocabulary : List RSAIterationLeakVocabularyKind
canonicalRSAIterationLeakVocabulary =
  iterationCountTraceVocabularyKind
  ∷ candidateDrawIndexVocabularyKind
  ∷ rejectionPathVocabularyKind
  ∷ acceptanceTraceVocabularyKind
  ∷ knownGeneratorContextVocabularyKind
  ∷ constrainedCandidatePrimeSetVocabularyKind
  ∷ sourceFiberShrinkCandidateVocabularyKind
  ∷ searchCostReductionCandidateVocabularyKind
  ∷ rejectionCountVocabularyKind
  ∷ timingCountVocabularyKind
  ∷ []

canonicalRSAIterationLeakVocabularyCount : Nat
canonicalRSAIterationLeakVocabularyCount =
  listCount canonicalRSAIterationLeakVocabulary

canonicalKnownGeneratorContext : String
canonicalKnownGeneratorContext =
  "known RSA key generator context"

canonicalConstrainedCandidatePrimeSet : List String
canonicalConstrainedCandidatePrimeSet =
  "candidate prime p"
  ∷ "candidate prime q"
  ∷ "candidate-prime family filtered by rejection history"
  ∷ "candidate-prime family filtered by timing history"
  ∷ []

canonicalSourceFiberShrinkCandidate : String
canonicalSourceFiberShrinkCandidate =
  "source-fiber shrink candidate"

canonicalSearchCostReductionCandidate : String
canonicalSearchCostReductionCandidate =
  "search-cost reduction candidate"

canonicalRSAIterationLeakAuthorityBoundaryClaims :
  List AuthorityBoundary.AuthorityBoundaryClaimKind
canonicalRSAIterationLeakAuthorityBoundaryClaims =
  AuthorityBoundary.runtimeAuthorityClaim
  ∷ AuthorityBoundary.physicsAuthorityClaim
  ∷ []

canonicalRSAIterationLeakAuthorityBoundaryClaimCount : Nat
canonicalRSAIterationLeakAuthorityBoundaryClaimCount =
  listCount canonicalRSAIterationLeakAuthorityBoundaryClaims

------------------------------------------------------------------------
-- Candidate-only rows.

mkRSAIterationLeakCandidateRow :
  String →
  String →
  String →
  String →
  String →
  String →
  CandidateOnly.CandidateOnlyRow
mkRSAIterationLeakCandidateRow
  label
  owner
  surface
  kindLabel
  statement
  remainingGap =
  CandidateOnly.mkCandidateOnlyRow
    label
    owner
    surface
    (CandidateOnly.namedCandidateKind kindLabel)
    CandidateOnly.diagnosticCandidateOnlyStatus
    statement
    remainingGap

iterationCountTraceCandidateRow :
  CandidateOnly.CandidateOnlyRow
iterationCountTraceCandidateRow =
  mkRSAIterationLeakCandidateRow
    "RSA iteration-count trace candidate"
    "DASHI.Crypto.RSAIterationLeakBoundary"
    "canonicalIterationCountTraceCandidateRow"
    "iteration-count trace"
    "iteration-count trace is tracked as candidate-only keygen side information"
    "factor recovery, exploit authority, side-channel authority, and security authority remain blocked"

candidateDrawIndexCandidateRow :
  CandidateOnly.CandidateOnlyRow
candidateDrawIndexCandidateRow =
  mkRSAIterationLeakCandidateRow
    "RSA candidate-draw index candidate"
    "DASHI.Crypto.RSAIterationLeakBoundary"
    "canonicalCandidateDrawIndexCandidateRow"
    "candidate draw index"
    "candidate-draw index is tracked as candidate-only keygen side information"
    "the source draw order is named, but no attack authority is promoted"

rejectionPathCandidateRow :
  CandidateOnly.CandidateOnlyRow
rejectionPathCandidateRow =
  mkRSAIterationLeakCandidateRow
    "RSA rejection-path candidate"
    "DASHI.Crypto.RSAIterationLeakBoundary"
    "canonicalRejectionPathCandidateRow"
    "rejection path"
    "rejection path is tracked as candidate-only keygen side information"
    "rejection history is named, but no factor recovery or exploit authority is supplied"

acceptanceTraceCandidateRow :
  CandidateOnly.CandidateOnlyRow
acceptanceTraceCandidateRow =
  mkRSAIterationLeakCandidateRow
    "RSA acceptance-trace candidate"
    "DASHI.Crypto.RSAIterationLeakBoundary"
    "canonicalAcceptanceTraceCandidateRow"
    "acceptance trace"
    "acceptance trace is tracked as candidate-only keygen side information"
    "acceptance history remains a receipt lane, not a security authority"

rejectionCountCandidateRow :
  CandidateOnly.CandidateOnlyRow
rejectionCountCandidateRow =
  mkRSAIterationLeakCandidateRow
    "RSA rejection-count candidate"
    "DASHI.Crypto.RSAIterationLeakBoundary"
    "canonicalRejectionCountCandidateRow"
    "rejection count"
    "rejection-count trace is tracked as candidate-only keygen side information"
    "rejection counting is not a proof of factor recovery or exploit authority"

timingCountCandidateRow :
  CandidateOnly.CandidateOnlyRow
timingCountCandidateRow =
  mkRSAIterationLeakCandidateRow
    "RSA timing-count candidate"
    "DASHI.Crypto.RSAIterationLeakBoundary"
    "canonicalTimingCountCandidateRow"
    "timing count"
    "timing-count trace is tracked as candidate-only keygen side information"
    "timing accounting stays candidate-only and does not promote side-channel authority"

sourceFiberShrinkCandidateRow :
  CandidateOnly.CandidateOnlyRow
sourceFiberShrinkCandidateRow =
  mkRSAIterationLeakCandidateRow
    "RSA source-fiber shrink candidate"
    "DASHI.Crypto.RSAIterationLeakBoundary"
    "canonicalSourceFiberShrinkCandidateRow"
    "source-fiber shrink candidate"
    "source-fiber shrink is tracked as candidate-only search bookkeeping"
    "the source fiber is constrained, but no recovery or exploit authority is supplied"

searchCostReductionCandidateRow :
  CandidateOnly.CandidateOnlyRow
searchCostReductionCandidateRow =
  mkRSAIterationLeakCandidateRow
    "RSA search-cost reduction candidate"
    "DASHI.Crypto.RSAIterationLeakBoundary"
    "canonicalSearchCostReductionCandidateRow"
    "search-cost reduction candidate"
    "search-cost reduction is tracked as candidate-only search bookkeeping"
    "reduced search cost is not promoted to factor recovery or security authority"

canonicalRSAIterationLeakCandidateRows :
  List CandidateOnly.CandidateOnlyRow
canonicalRSAIterationLeakCandidateRows =
  iterationCountTraceCandidateRow
  ∷ candidateDrawIndexCandidateRow
  ∷ rejectionPathCandidateRow
  ∷ acceptanceTraceCandidateRow
  ∷ rejectionCountCandidateRow
  ∷ timingCountCandidateRow
  ∷ sourceFiberShrinkCandidateRow
  ∷ searchCostReductionCandidateRow
  ∷ []

canonicalRSAIterationLeakCandidateRowCount : Nat
canonicalRSAIterationLeakCandidateRowCount =
  listCount canonicalRSAIterationLeakCandidateRows

iterationCountTraceCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt iterationCountTraceCandidateRow
iterationCountTraceCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    iterationCountTraceCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

candidateDrawIndexCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt candidateDrawIndexCandidateRow
candidateDrawIndexCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    candidateDrawIndexCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

rejectionPathCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt rejectionPathCandidateRow
rejectionPathCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    rejectionPathCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

acceptanceTraceCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt acceptanceTraceCandidateRow
acceptanceTraceCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    acceptanceTraceCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

rejectionCountCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt rejectionCountCandidateRow
rejectionCountCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    rejectionCountCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

timingCountCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt timingCountCandidateRow
timingCountCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    timingCountCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

sourceFiberShrinkCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt sourceFiberShrinkCandidateRow
sourceFiberShrinkCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    sourceFiberShrinkCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

searchCostReductionCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt searchCostReductionCandidateRow
searchCostReductionCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    searchCostReductionCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalRSAIterationLeakCandidateGenericReceipts :
  List GenericReceipt.GenericReceipt
canonicalRSAIterationLeakCandidateGenericReceipts =
  CandidateOnly.candidateOnlyGenericReceipt iterationCountTraceCandidateRow
  ∷ CandidateOnly.candidateOnlyGenericReceipt candidateDrawIndexCandidateRow
  ∷ CandidateOnly.candidateOnlyGenericReceipt rejectionPathCandidateRow
  ∷ CandidateOnly.candidateOnlyGenericReceipt acceptanceTraceCandidateRow
  ∷ CandidateOnly.candidateOnlyGenericReceipt rejectionCountCandidateRow
  ∷ CandidateOnly.candidateOnlyGenericReceipt timingCountCandidateRow
  ∷ CandidateOnly.candidateOnlyGenericReceipt sourceFiberShrinkCandidateRow
  ∷ CandidateOnly.candidateOnlyGenericReceipt searchCostReductionCandidateRow
  ∷ []

canonicalRSAIterationLeakCandidateGenericReceiptCount : Nat
canonicalRSAIterationLeakCandidateGenericReceiptCount =
  listCount canonicalRSAIterationLeakCandidateGenericReceipts

canonicalRSAIterationLeakCandidateGenericReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting
    canonicalRSAIterationLeakCandidateGenericReceipts
canonicalRSAIterationLeakCandidateGenericReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    canonicalRSAIterationLeakCandidateGenericReceipts

------------------------------------------------------------------------
-- Blocked authorities.

data RSAIterationLeakBlockedAuthorityKind : Set where
  factorRecoveryAuthorityKind :
    RSAIterationLeakBlockedAuthorityKind

  exploitAuthorityKind :
    RSAIterationLeakBlockedAuthorityKind

  sideChannelAuthorityKind :
    RSAIterationLeakBlockedAuthorityKind

  securityAuthorityKind :
    RSAIterationLeakBlockedAuthorityKind

  namedRSAIterationLeakBlockedAuthorityKind :
    String →
    RSAIterationLeakBlockedAuthorityKind

record RSAIterationLeakBlockedAuthority : Set where
  constructor rsaIterationLeakBlockedAuthority
  field
    blockedAuthorityLabel :
      String

    blockedAuthorityKind :
      RSAIterationLeakBlockedAuthorityKind

    blockedAuthorityNotes :
      String

    blockedAuthority :
      Bool

    blockedAuthorityIsFalse :
      blockedAuthority ≡ false

open RSAIterationLeakBlockedAuthority public

mkRSAIterationLeakBlockedAuthority :
  String →
  RSAIterationLeakBlockedAuthorityKind →
  String →
  RSAIterationLeakBlockedAuthority
mkRSAIterationLeakBlockedAuthority label kind notes =
  rsaIterationLeakBlockedAuthority
    label
    kind
    notes
    false
    refl

factorRecoveryBlockedAuthority :
  RSAIterationLeakBlockedAuthority
factorRecoveryBlockedAuthority =
  mkRSAIterationLeakBlockedAuthority
    "factor recovery authority"
    factorRecoveryAuthorityKind
    "iteration leaks are not promoted to factor recovery authority"

exploitBlockedAuthority :
  RSAIterationLeakBlockedAuthority
exploitBlockedAuthority =
  mkRSAIterationLeakBlockedAuthority
    "exploit authority"
    exploitAuthorityKind
    "iteration leaks are not promoted to exploit authority"

sideChannelBlockedAuthority :
  RSAIterationLeakBlockedAuthority
sideChannelBlockedAuthority =
  mkRSAIterationLeakBlockedAuthority
    "side-channel authority"
    sideChannelAuthorityKind
    "iteration leaks are not promoted to side-channel authority"

securityBlockedAuthority :
  RSAIterationLeakBlockedAuthority
securityBlockedAuthority =
  mkRSAIterationLeakBlockedAuthority
    "security authority"
    securityAuthorityKind
    "iteration leaks are not promoted to security authority"

canonicalRSAIterationLeakBlockedAuthorities :
  List RSAIterationLeakBlockedAuthority
canonicalRSAIterationLeakBlockedAuthorities =
  factorRecoveryBlockedAuthority
  ∷ exploitBlockedAuthority
  ∷ sideChannelBlockedAuthority
  ∷ securityBlockedAuthority
  ∷ []

canonicalRSAIterationLeakBlockedAuthorityCount : Nat
canonicalRSAIterationLeakBlockedAuthorityCount =
  listCount canonicalRSAIterationLeakBlockedAuthorities

------------------------------------------------------------------------
-- Boundary receipt surface.

record RSAIterationLeakBoundary : Set where
  constructor mkRSAIterationLeakBoundary
  field
    boundaryLabel :
      String

    boundarySurface :
      String

    boundaryOwner :
      String

    hiddenLiftProjectionReceiptReference :
      HiddenLift.HiddenLiftProjectionReceipt
        HiddenLift.canonicalHiddenLiftProjectionSurface

    sourceProcessEvidenceReceiptReference :
      SourceProcessEvidence.SourceProcessEvidenceReceipt
        SourceProcessEvidence.canonicalSourceProcessEvidenceSurface

    statisticalEvidenceCandidateReceiptReference :
      CandidateOnly.CandidateOnlyReceipt
        Statistical.canonicalStatisticalEvidenceCandidateRow

    bridgeRequirementCoreReceiptReference :
      Bridge.BridgeRequirementCoreReceipt

    adapterCanonicalityReceiptReference :
      Adapter.AdapterCanonicalityReceipt
        Adapter.AdapterSurface
        Adapter.canonicalAdapter

    vulnerabilityBoundaryReceiptReference :
      GenericReceipt.GenericReceipt

    authorityBoundaryClaims :
      List AuthorityBoundary.AuthorityBoundaryClaimKind

    authorityBoundaryClaimsAreCanonical :
      authorityBoundaryClaims ≡ canonicalRSAIterationLeakAuthorityBoundaryClaims

    iterationLeakVocabulary :
      List RSAIterationLeakVocabularyKind

    iterationLeakVocabularyAreCanonical :
      iterationLeakVocabulary ≡ canonicalRSAIterationLeakVocabulary

    knownGeneratorContext :
      String

    constrainedCandidatePrimeSet :
      List String

    constrainedCandidatePrimeSetAreCanonical :
      constrainedCandidatePrimeSet ≡ canonicalConstrainedCandidatePrimeSet

    sourceFiberShrinkCandidate :
      String

    searchCostReductionCandidate :
      String

    candidateRows :
      List CandidateOnly.CandidateOnlyRow

    candidateRowsAreCanonical :
      candidateRows ≡ canonicalRSAIterationLeakCandidateRows

    candidateGenericReceipts :
      List GenericReceipt.GenericReceipt

    candidateGenericReceiptsAreCanonical :
      candidateGenericReceipts ≡
      canonicalRSAIterationLeakCandidateGenericReceipts

    candidateGenericReceiptsNonPromoting :
      GenericReceipt.AllReceiptsNonPromoting candidateGenericReceipts

    blockedAuthorities :
      List RSAIterationLeakBlockedAuthority

    blockedAuthoritiesAreCanonical :
      blockedAuthorities ≡ canonicalRSAIterationLeakBlockedAuthorities

    sourceFiberRestriction :
      Bool

    sourceFiberRestrictionIsTrue :
      sourceFiberRestriction ≡ true

    statisticalAnomalyCandidateOnly :
      Bool

    statisticalAnomalyCandidateOnlyIsTrue :
      statisticalAnomalyCandidateOnly ≡ true

    sourceWideEscalationAuthority :
      Bool

    sourceWideEscalationAuthorityIsFalse :
      sourceWideEscalationAuthority ≡ false

    boundaryCandidateOnly :
      Bool

    boundaryCandidateOnlyIsTrue :
      boundaryCandidateOnly ≡ true

    boundaryPromoted :
      Bool

    boundaryPromotedIsFalse :
      boundaryPromoted ≡ false

    boundaryReceipt :
      GenericReceipt.GenericReceipt

    boundaryReceiptIsNonPromoting :
      GenericReceipt.promotesClaim boundaryReceipt ≡ false

open RSAIterationLeakBoundary public

canonicalRSAIterationLeakBoundaryReceipt :
  GenericReceipt.GenericReceipt
canonicalRSAIterationLeakBoundaryReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "RSA keygen iteration leak boundary"
    "DASHI.Crypto.RSAIterationLeakBoundary"
    "canonicalRSAIterationLeakBoundary"
    "candidate-only RSA keygen side-information boundary for iteration-count, rejection-count, timing-count, candidate-draw index, rejection path, acceptance trace, generator context, constrained candidate-prime set, source-fiber shrink candidate, and search-cost reduction candidate vocabulary"
    "iteration leaks stay blocked from factor recovery, exploit authority, side-channel authority, and security authority"
    "agda -i . DASHI/Crypto/RSAIterationLeakBoundary.agda"

canonicalRSAIterationLeakBoundary :
  RSAIterationLeakBoundary
canonicalRSAIterationLeakBoundary =
  mkRSAIterationLeakBoundary
    "RSA keygen iteration leak boundary"
    "candidate-only RSA keygen side-information boundary"
    "DASHI.Crypto.RSAIterationLeakBoundary"
    HiddenLift.canonicalHiddenLiftProjectionReceipt
    SourceProcessEvidence.canonicalSourceProcessEvidenceReceipt
    Statistical.canonicalStatisticalEvidenceCandidateReceipt
    Bridge.canonicalBridgeRequirementCoreReceipt
    Adapter.canonicalAdapterCanonicalityReceipt
    RSAVulnerabilityBoundary.canonicalRSAVulnerabilityBoundaryReceipt
    canonicalRSAIterationLeakAuthorityBoundaryClaims
    refl
    canonicalRSAIterationLeakVocabulary
    refl
    canonicalKnownGeneratorContext
    canonicalConstrainedCandidatePrimeSet
    refl
    canonicalSourceFiberShrinkCandidate
    canonicalSearchCostReductionCandidate
    canonicalRSAIterationLeakCandidateRows
    refl
    canonicalRSAIterationLeakCandidateGenericReceipts
    refl
    canonicalRSAIterationLeakCandidateGenericReceiptsNonPromoting
    canonicalRSAIterationLeakBlockedAuthorities
    refl
    true
    refl
    true
    refl
    false
    refl
    true
    refl
    false
    refl
    canonicalRSAIterationLeakBoundaryReceipt
    refl

canonicalRSAIterationLeakBoundaryCandidateOnly :
  boundaryCandidateOnly canonicalRSAIterationLeakBoundary ≡ true
canonicalRSAIterationLeakBoundaryCandidateOnly =
  refl

canonicalRSAIterationLeakBoundaryPromotedFalse :
  boundaryPromoted canonicalRSAIterationLeakBoundary ≡ false
canonicalRSAIterationLeakBoundaryPromotedFalse =
  refl

canonicalRSAIterationLeakBoundaryNonPromoting :
  GenericReceipt.promotesClaim canonicalRSAIterationLeakBoundaryReceipt ≡ false
canonicalRSAIterationLeakBoundaryNonPromoting =
  refl

canonicalRSAIterationLeakBoundarySourceFiberRestrictionIsTrue :
  sourceFiberRestriction canonicalRSAIterationLeakBoundary ≡ true
canonicalRSAIterationLeakBoundarySourceFiberRestrictionIsTrue =
  refl

canonicalRSAIterationLeakBoundaryStatisticalAnomalyCandidateOnlyIsTrue :
  statisticalAnomalyCandidateOnly canonicalRSAIterationLeakBoundary ≡ true
canonicalRSAIterationLeakBoundaryStatisticalAnomalyCandidateOnlyIsTrue =
  refl

canonicalRSAIterationLeakBoundarySourceWideEscalationAuthorityIsFalse :
  sourceWideEscalationAuthority canonicalRSAIterationLeakBoundary ≡ false
canonicalRSAIterationLeakBoundarySourceWideEscalationAuthorityIsFalse =
  refl

canonicalRSAIterationLeakBoundaryLabels :
  List String
canonicalRSAIterationLeakBoundaryLabels =
  "DASHI.Core.HiddenLiftProjectionCore"
  ∷ "DASHI.Core.SourceProcessEvidenceCore"
  ∷ "DASHI.Core.StatisticalEvidenceCore"
  ∷ "DASHI.Core.BridgeRequirementCore"
  ∷ "DASHI.Core.AdapterCanonicalityCore"
  ∷ "DASHI.Crypto.RSAVulnerabilityBoundary"
  ∷ "RSA iteration-count trace candidate"
  ∷ "RSA candidate-draw index candidate"
  ∷ "RSA rejection-path candidate"
  ∷ "RSA acceptance-trace candidate"
  ∷ "RSA rejection-count candidate"
  ∷ "RSA timing-count candidate"
  ∷ "RSA source-fiber shrink candidate"
  ∷ "RSA search-cost reduction candidate"
  ∷ "factor recovery authority"
  ∷ "exploit authority"
  ∷ "side-channel authority"
  ∷ "security authority"
  ∷ []
