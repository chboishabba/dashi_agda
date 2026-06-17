module DASHI.Core.SourceProcessEvidenceCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdapterCanonicalityCore as Adapter
import DASHI.Core.AuthorityNonPromotionCore as AuthorityNA
import DASHI.Core.BridgeRequirementCore as Bridge
import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.StatisticalEvidenceCore as StatisticalEvidence
import DASHI.Promotion.AuthorityBoundaryCore as AuthorityBoundary

------------------------------------------------------------------------
-- Source-process evidence core.
--
-- This core names the reusable batch/source-process pattern:
--
--   hidden/source process theta emits many public artifacts;
--   traces, metadata, side evidence, and statistics can restrict the
--   source fiber or create a candidate weakness;
--   only an explicit recovered witness can support an artifact-local
--   finding, and source-wide or production authority remains blocked.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Vocabulary.

data SourceProcessEvidenceKind : Set where
  sourceStateKind :
    SourceProcessEvidenceKind

  emissionProcessKind :
    SourceProcessEvidenceKind

  publicArtifactKind :
    SourceProcessEvidenceKind

  publicArtifactBatchKind :
    SourceProcessEvidenceKind

  observableTraceKind :
    SourceProcessEvidenceKind

  sideEvidenceKind :
    SourceProcessEvidenceKind

  sourceFiberKind :
    SourceProcessEvidenceKind

  restrictedSourceFiberKind :
    SourceProcessEvidenceKind

  batchStatisticKind :
    SourceProcessEvidenceKind

  candidateWeaknessKind :
    SourceProcessEvidenceKind

  recoveredWitnessKind :
    SourceProcessEvidenceKind

  artifactSpecificFindingKind :
    SourceProcessEvidenceKind

  sourceClassWeaknessKind :
    SourceProcessEvidenceKind

  namedSourceProcessEvidenceKind :
    String →
    SourceProcessEvidenceKind

canonicalSourceProcessEvidenceKinds :
  List SourceProcessEvidenceKind
canonicalSourceProcessEvidenceKinds =
  sourceStateKind
  ∷ emissionProcessKind
  ∷ publicArtifactKind
  ∷ publicArtifactBatchKind
  ∷ observableTraceKind
  ∷ sideEvidenceKind
  ∷ sourceFiberKind
  ∷ restrictedSourceFiberKind
  ∷ batchStatisticKind
  ∷ candidateWeaknessKind
  ∷ recoveredWitnessKind
  ∷ artifactSpecificFindingKind
  ∷ sourceClassWeaknessKind
  ∷ []

canonicalSourceProcessEvidenceKindCount : Nat
canonicalSourceProcessEvidenceKindCount =
  listCount canonicalSourceProcessEvidenceKinds

data SourceProcessEvidenceAdapterSurface : Set where
  sourceProcessEvidenceAdapter :
    SourceProcessEvidenceAdapterSurface

  sourceFiberRestrictionAdapter :
    SourceProcessEvidenceAdapterSurface

  recoveredWitnessEscalationAdapter :
    SourceProcessEvidenceAdapterSurface

  namedSourceProcessEvidenceAdapter :
    String →
    SourceProcessEvidenceAdapterSurface

canonicalSourceProcessEvidenceAdapter :
  SourceProcessEvidenceAdapterSurface
canonicalSourceProcessEvidenceAdapter =
  sourceProcessEvidenceAdapter

canonicalSourceProcessEvidenceBoundaryClaims :
  List AuthorityBoundary.AuthorityBoundaryClaimKind
canonicalSourceProcessEvidenceBoundaryClaims =
  AuthorityBoundary.runtimeAuthorityClaim
  ∷ AuthorityBoundary.legalAuthorityClaim
  ∷ AuthorityBoundary.clinicalAuthorityClaim
  ∷ AuthorityBoundary.tradingAuthorityClaim
  ∷ []

canonicalSourceProcessEvidenceBoundaryClaimCount : Nat
canonicalSourceProcessEvidenceBoundaryClaimCount =
  listCount canonicalSourceProcessEvidenceBoundaryClaims

------------------------------------------------------------------------
-- Canonical support receipts.

canonicalSourceProcessEvidenceCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalSourceProcessEvidenceCandidateRow =
  CandidateOnly.mkCandidateOnlyRow
    "source-process evidence candidate"
    "DASHI.Core.SourceProcessEvidenceCore"
    "canonicalSourceProcessEvidenceCandidateRow"
    CandidateOnly.diagnosticCandidateKind
    CandidateOnly.diagnosticCandidateOnlyStatus
    "source-process evidence is candidate-only bookkeeping for batches emitted by a shared hidden/source process"
    "side evidence, traces, metadata, and statistics restrict candidate fibers but do not promote source, causal, production, security, clinical, legal, trading, or governance authority"

canonicalSourceProcessEvidenceCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt
    canonicalSourceProcessEvidenceCandidateRow
canonicalSourceProcessEvidenceCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalSourceProcessEvidenceCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalSourceProcessEvidenceAuthorityBundle :
  AuthorityNA.AuthorityNonPromotionBundle
canonicalSourceProcessEvidenceAuthorityBundle =
  AuthorityNA.canonicalAuthorityNonPromotionBundle

canonicalSourceProcessEvidenceBridgeReceipt :
  Bridge.BridgeRequirementCoreReceipt
canonicalSourceProcessEvidenceBridgeReceipt =
  Bridge.canonicalBridgeRequirementCoreReceipt

canonicalSourceProcessEvidenceAdapterReceipt :
  Adapter.AdapterCanonicalityReceipt
    SourceProcessEvidenceAdapterSurface
    canonicalSourceProcessEvidenceAdapter
canonicalSourceProcessEvidenceAdapterReceipt =
  Adapter.mkCanonicalAdapterReceipt
    "source-process evidence adapter"
    "DASHI.Core.SourceProcessEvidenceCore"
    "canonicalSourceProcessEvidenceAdapter"
    (Adapter.namedAdapterKind "source-process evidence")
    canonicalSourceProcessEvidenceAdapter

canonicalSourceProcessStatisticalEvidenceReceipt :
  StatisticalEvidence.StatisticalEvidenceReceipt
    StatisticalEvidence.canonicalStatisticalEvidenceSurface
canonicalSourceProcessStatisticalEvidenceReceipt =
  StatisticalEvidence.canonicalStatisticalEvidenceReceipt

canonicalSourceProcessEvidenceGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalSourceProcessEvidenceGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "source-process evidence core"
    "DASHI.Core.SourceProcessEvidenceCore"
    "canonicalSourceProcessEvidenceSurface"
    "many public artifacts emitted from a shared source process are tracked as candidate-only evidence with source-fiber restriction and witness-escalation boundaries"
    "statistical anomaly and side evidence do not promote source compromise, causal proof, production authority, security authority, clinical authority, legal authority, trading authority, or governance promotion"
    "agda -i . DASHI/Core/SourceProcessEvidenceCore.agda"

------------------------------------------------------------------------
-- Surface and receipt.

record SourceProcessEvidenceSurface : Set where
  constructor sourceProcessEvidenceSurface
  field
    evidenceLabel :
      String

    evidenceOwner :
      String

    evidenceSurface :
      String

    sourceState :
      String

    emissionProcess :
      String

    publicArtifact :
      String

    publicArtifactBatch :
      String

    observableTrace :
      String

    sideEvidence :
      String

    sourceFiber :
      String

    restrictedSourceFiber :
      String

    batchStatistic :
      String

    candidateWeakness :
      String

    recoveredWitness :
      String

    artifactSpecificFinding :
      String

    sourceClassWeakness :
      String

    evidenceKinds :
      List SourceProcessEvidenceKind

    evidenceKindsCount :
      Nat

    candidateRow :
      CandidateOnly.CandidateOnlyRow

    candidateReceipt :
      CandidateOnly.CandidateOnlyReceipt candidateRow

    authorityBundle :
      AuthorityNA.AuthorityNonPromotionBundle

    authorityBoundaryClaims :
      List AuthorityBoundary.AuthorityBoundaryClaimKind

    statisticalEvidenceReceipt :
      StatisticalEvidence.StatisticalEvidenceReceipt
        StatisticalEvidence.canonicalStatisticalEvidenceSurface

    bridgeReceipt :
      Bridge.BridgeRequirementCoreReceipt

    adapterReceipt :
      Adapter.AdapterCanonicalityReceipt
        SourceProcessEvidenceAdapterSurface
        canonicalSourceProcessEvidenceAdapter

    genericReceipt :
      GenericReceipt.GenericReceipt

    sideEvidenceRestrictsFiber :
      Bool

    statisticalAnomalyCandidateOnly :
      Bool

    statisticalAnomalySourceCompromiseAuthority :
      Bool

    recoveredWitnessEscalatesArtifactOnly :
      Bool

    sourceWideEscalationAuthority :
      Bool

    causalAuthority :
      Bool

    productionAuthority :
      Bool

    securityAuthority :
      Bool

    clinicalAuthority :
      Bool

    legalAuthority :
      Bool

    tradingAuthority :
      Bool

    governancePromotionAuthority :
      Bool

    evidenceStatement :
      String

    evidenceRemainingGap :
      String

open SourceProcessEvidenceSurface public

record SourceProcessEvidenceReceipt
  (surface : SourceProcessEvidenceSurface) :
  Set where
  constructor sourceProcessEvidenceReceipt
  field
    receiptCandidateOnlyIsTrue :
      CandidateOnly.candidateOnly (candidateRow surface) ≡ true

    receiptPromotedIsFalse :
      CandidateOnly.promoted (candidateRow surface) ≡ false

    receiptAuthorityBundlePromotesAnyAuthorityIsFalse :
      AuthorityNA.promotesAnyAuthority (authorityBundle surface) ≡ false

    receiptBridgeAuthorityPromotionIsFalse :
      Bridge.receiptAuthorityPromotion (bridgeReceipt surface) ≡ false

    receiptBridgeTransportMapAuthorityIsFalse :
      Bridge.receiptTransportMapAuthority (bridgeReceipt surface) ≡ false

    receiptBridgeBackgroundBridgeAuthorityIsFalse :
      Bridge.receiptBackgroundBridgeAuthority (bridgeReceipt surface) ≡ false

    receiptAdapterPromotesAuthorityIsFalse :
      Adapter.adapterPromotesAuthority (adapterReceipt surface) ≡ false

    receiptGenericReceiptNonPromoting :
      GenericReceipt.promotesClaim (genericReceipt surface) ≡ false

    receiptEvidenceKindsCanonical :
      evidenceKinds surface ≡ canonicalSourceProcessEvidenceKinds

    receiptEvidenceKindsCountCanonical :
      evidenceKindsCount surface
      ≡
      canonicalSourceProcessEvidenceKindCount

    receiptAuthorityBoundaryClaimsCanonical :
      authorityBoundaryClaims surface
      ≡
      canonicalSourceProcessEvidenceBoundaryClaims

    receiptSideEvidenceRestrictsFiberIsTrue :
      sideEvidenceRestrictsFiber surface ≡ true

    receiptStatisticalAnomalyCandidateOnlyIsTrue :
      statisticalAnomalyCandidateOnly surface ≡ true

    receiptStatisticalAnomalySourceCompromiseAuthorityIsFalse :
      statisticalAnomalySourceCompromiseAuthority surface ≡ false

    receiptRecoveredWitnessEscalatesArtifactOnlyIsTrue :
      recoveredWitnessEscalatesArtifactOnly surface ≡ true

    receiptSourceWideEscalationAuthorityIsFalse :
      sourceWideEscalationAuthority surface ≡ false

    receiptCausalAuthorityIsFalse :
      causalAuthority surface ≡ false

    receiptProductionAuthorityIsFalse :
      productionAuthority surface ≡ false

    receiptSecurityAuthorityIsFalse :
      securityAuthority surface ≡ false

    receiptClinicalAuthorityIsFalse :
      clinicalAuthority surface ≡ false

    receiptLegalAuthorityIsFalse :
      legalAuthority surface ≡ false

    receiptTradingAuthorityIsFalse :
      tradingAuthority surface ≡ false

    receiptGovernancePromotionAuthorityIsFalse :
      governancePromotionAuthority surface ≡ false

open SourceProcessEvidenceReceipt public

canonicalSourceProcessEvidenceSurface :
  SourceProcessEvidenceSurface
canonicalSourceProcessEvidenceSurface =
  sourceProcessEvidenceSurface
    "source-process evidence"
    "DASHI.Core.SourceProcessEvidenceCore"
    "canonicalSourceProcessEvidenceSurface"
    "source state theta"
    "emission process"
    "public artifact"
    "public artifact batch"
    "observable trace"
    "side evidence"
    "source fiber"
    "restricted source fiber"
    "batch statistic"
    "candidate source weakness"
    "recovered witness"
    "artifact-specific finding"
    "source-class weakness"
    canonicalSourceProcessEvidenceKinds
    canonicalSourceProcessEvidenceKindCount
    canonicalSourceProcessEvidenceCandidateRow
    canonicalSourceProcessEvidenceCandidateReceipt
    canonicalSourceProcessEvidenceAuthorityBundle
    canonicalSourceProcessEvidenceBoundaryClaims
    canonicalSourceProcessStatisticalEvidenceReceipt
    canonicalSourceProcessEvidenceBridgeReceipt
    canonicalSourceProcessEvidenceAdapterReceipt
    canonicalSourceProcessEvidenceGenericReceipt
    true
    true
    false
    true
    false
    false
    false
    false
    false
    false
    false
    false
    "source-process evidence records how traces, side evidence, metadata, and batch statistics constrain emitted public artifacts"
    "restriction and anomaly are candidate-only; artifact findings require explicit witnesses, and source-wide authority requires a separate receipt"

canonicalSourceProcessEvidenceReceipt :
  SourceProcessEvidenceReceipt canonicalSourceProcessEvidenceSurface
canonicalSourceProcessEvidenceReceipt =
  sourceProcessEvidenceReceipt
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
-- Projection lemmas for downstream consumers.

sourceProcessEvidenceCandidateOnlyIsTrue :
  CandidateOnly.candidateOnly canonicalSourceProcessEvidenceCandidateRow
  ≡
  true
sourceProcessEvidenceCandidateOnlyIsTrue =
  receiptCandidateOnlyIsTrue canonicalSourceProcessEvidenceReceipt

sourceProcessEvidencePromotedIsFalse :
  CandidateOnly.promoted canonicalSourceProcessEvidenceCandidateRow
  ≡
  false
sourceProcessEvidencePromotedIsFalse =
  receiptPromotedIsFalse canonicalSourceProcessEvidenceReceipt

sourceProcessEvidenceKindsAreCanonical :
  evidenceKinds canonicalSourceProcessEvidenceSurface
  ≡
  canonicalSourceProcessEvidenceKinds
sourceProcessEvidenceKindsAreCanonical =
  receiptEvidenceKindsCanonical canonicalSourceProcessEvidenceReceipt

sideEvidenceRestrictsFiberIsTrue :
  sideEvidenceRestrictsFiber canonicalSourceProcessEvidenceSurface ≡ true
sideEvidenceRestrictsFiberIsTrue =
  receiptSideEvidenceRestrictsFiberIsTrue
    canonicalSourceProcessEvidenceReceipt

statisticalAnomalyCandidateOnlyIsTrue :
  statisticalAnomalyCandidateOnly canonicalSourceProcessEvidenceSurface
  ≡
  true
statisticalAnomalyCandidateOnlyIsTrue =
  receiptStatisticalAnomalyCandidateOnlyIsTrue
    canonicalSourceProcessEvidenceReceipt

statisticalAnomalySourceCompromiseAuthorityIsFalse :
  statisticalAnomalySourceCompromiseAuthority
    canonicalSourceProcessEvidenceSurface
  ≡
  false
statisticalAnomalySourceCompromiseAuthorityIsFalse =
  receiptStatisticalAnomalySourceCompromiseAuthorityIsFalse
    canonicalSourceProcessEvidenceReceipt

recoveredWitnessEscalatesArtifactOnlyIsTrue :
  recoveredWitnessEscalatesArtifactOnly canonicalSourceProcessEvidenceSurface
  ≡
  true
recoveredWitnessEscalatesArtifactOnlyIsTrue =
  receiptRecoveredWitnessEscalatesArtifactOnlyIsTrue
    canonicalSourceProcessEvidenceReceipt

sourceWideEscalationAuthorityIsFalse :
  sourceWideEscalationAuthority canonicalSourceProcessEvidenceSurface
  ≡
  false
sourceWideEscalationAuthorityIsFalse =
  receiptSourceWideEscalationAuthorityIsFalse
    canonicalSourceProcessEvidenceReceipt

sourceProcessEvidenceGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim canonicalSourceProcessEvidenceGenericReceipt
  ≡
  false
sourceProcessEvidenceGenericReceiptNonPromoting =
  receiptGenericReceiptNonPromoting canonicalSourceProcessEvidenceReceipt
