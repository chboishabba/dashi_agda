module DASHI.Crypto.RSABatchSharedPrimeBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Crypto.RSABTResidueBraidHypervoxelBoundary as BT
import DASHI.Crypto.RSAVulnerabilityBoundary as RSA
import DASHI.Core.AdapterCanonicalityCore as Adapter
import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Core.BridgeRequirementCore as Bridge
import DASHI.Core.CandidateOnlyCore as Candidate
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.HiddenLiftProjectionCore as HiddenLift
import DASHI.Core.SourceProcessEvidenceCore as SourceProcessEvidence
import DASHI.Core.SourceProcessEvidenceLawCore as SourceProcessEvidenceLaw
import DASHI.Core.StatisticalEvidenceCore as Stats
import DASHI.Promotion.AuthorityBoundaryCore as AuthorityBoundary

------------------------------------------------------------------------
-- RSA batch / shared-prime boundary receipt core.
--
-- This module stays candidate-only.  It records a source-conditioned modulus
-- batch, a pairwise modulus-pair witness lane, gcd/shared-prime collapse
-- candidate surfaces, a recovered-factor boundary marker, and a generic
-- artifact-specific vulnerability receipt.  It keeps authority blocked:
-- no general RSA break, no factoring oracle, no source-wide compromise, no
-- semantic-security break, and no production advisory authority unless an
-- explicit recovered witness is separately supplied elsewhere.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Boundary vocabulary.

data RSABatchSharedPrimeBoundaryKind : Set where
  sourceConditionedModulusBatchKind :
    RSABatchSharedPrimeBoundaryKind

  pairwiseModulusPairKind :
    RSABatchSharedPrimeBoundaryKind

  gcdWitnessCandidateKind :
    RSABatchSharedPrimeBoundaryKind

  sharedPrimeCollapseCandidateKind :
    RSABatchSharedPrimeBoundaryKind

  recoveredFactorWitnessBoundaryKind :
    RSABatchSharedPrimeBoundaryKind

  artifactSpecificVulnerabilityReceiptKind :
    RSABatchSharedPrimeBoundaryKind

  namedRSABatchSharedPrimeBoundaryKind :
    String →
    RSABatchSharedPrimeBoundaryKind

canonicalRSABatchSharedPrimeBoundaryKinds :
  List RSABatchSharedPrimeBoundaryKind
canonicalRSABatchSharedPrimeBoundaryKinds =
  sourceConditionedModulusBatchKind
  ∷ pairwiseModulusPairKind
  ∷ gcdWitnessCandidateKind
  ∷ sharedPrimeCollapseCandidateKind
  ∷ recoveredFactorWitnessBoundaryKind
  ∷ artifactSpecificVulnerabilityReceiptKind
  ∷ []

canonicalRSABatchSharedPrimeBoundaryKindCount :
  Nat
canonicalRSABatchSharedPrimeBoundaryKindCount =
  listCount canonicalRSABatchSharedPrimeBoundaryKinds

data RSABatchAuthorityClaim : Set where
  generalRSABreakClaim :
    RSABatchAuthorityClaim

  factoringOracleClaim :
    RSABatchAuthorityClaim

  sourceWideCompromiseClaim :
    RSABatchAuthorityClaim

  semanticSecurityBreakClaim :
    RSABatchAuthorityClaim

  productionAdvisoryAuthorityClaim :
    RSABatchAuthorityClaim

  namedRSABatchAuthorityClaim :
    String →
    RSABatchAuthorityClaim

canonicalRSABatchAuthorityClaims :
  List RSABatchAuthorityClaim
canonicalRSABatchAuthorityClaims =
  generalRSABreakClaim
  ∷ factoringOracleClaim
  ∷ sourceWideCompromiseClaim
  ∷ semanticSecurityBreakClaim
  ∷ productionAdvisoryAuthorityClaim
  ∷ []

canonicalRSABatchAuthorityClaimCount :
  Nat
canonicalRSABatchAuthorityClaimCount =
  listCount canonicalRSABatchAuthorityClaims

canonicalGenericAuthorityBoundaryClaims :
  List AuthorityBoundary.AuthorityBoundaryClaimKind
canonicalGenericAuthorityBoundaryClaims =
  AuthorityBoundary.canonicalBlockedAuthorityClaims

canonicalGenericAuthorityBoundaryClaimCount :
  Nat
canonicalGenericAuthorityBoundaryClaimCount =
  AuthorityBoundary.canonicalBlockedAuthorityClaimCount

------------------------------------------------------------------------
-- Pairwise modulus-pair candidate row and receipt.

record RSABatchSharedPrimeModulusPair : Set where
  constructor mkRSABatchSharedPrimeModulusPair
  field
    pairLabel :
      String

    leftModulusLabel :
      String

    rightModulusLabel :
      String

    pairKind :
      RSABatchSharedPrimeBoundaryKind

    pairCandidateOnly :
      Bool

    pairPromoted :
      Bool

    pairGcdWitnessCandidate :
      Bool

    pairSharedPrimeCollapseCandidate :
      Bool

    pairRecoveredFactorWitnessBoundary :
      Bool

    pairGeneralRSABreakBlocked :
      Bool

    pairFactoringOracleBlocked :
      Bool

    pairSourceWideCompromiseBlocked :
      Bool

    pairSemanticSecurityBreakBlocked :
      Bool

    pairProductionAdvisoryAuthorityBlocked :
      Bool

    pairStatement :
      String

    pairRemainingGap :
      String

open RSABatchSharedPrimeModulusPair public

record RSABatchSharedPrimeModulusPairReceipt
  (pair : RSABatchSharedPrimeModulusPair) :
  Set where
  constructor mkRSABatchSharedPrimeModulusPairReceipt
  field
    pairCandidateOnlyIsTrue :
      pairCandidateOnly pair ≡ true

    pairPromotedIsFalse :
      pairPromoted pair ≡ false

    pairGcdWitnessCandidateIsTrue :
      pairGcdWitnessCandidate pair ≡ true

    pairSharedPrimeCollapseCandidateIsTrue :
      pairSharedPrimeCollapseCandidate pair ≡ true

    pairRecoveredFactorWitnessBoundaryIsFalse :
      pairRecoveredFactorWitnessBoundary pair ≡ false

    pairGeneralRSABreakBlockedIsFalse :
      pairGeneralRSABreakBlocked pair ≡ false

    pairFactoringOracleBlockedIsFalse :
      pairFactoringOracleBlocked pair ≡ false

    pairSourceWideCompromiseBlockedIsFalse :
      pairSourceWideCompromiseBlocked pair ≡ false

    pairSemanticSecurityBreakBlockedIsFalse :
      pairSemanticSecurityBreakBlocked pair ≡ false

    pairProductionAdvisoryAuthorityBlockedIsFalse :
      pairProductionAdvisoryAuthorityBlocked pair ≡ false

open RSABatchSharedPrimeModulusPairReceipt public

canonicalRSABatchSharedPrimeModulusPair :
  RSABatchSharedPrimeModulusPair
canonicalRSABatchSharedPrimeModulusPair =
  mkRSABatchSharedPrimeModulusPair
    "pairwise shared-prime modulus pair"
    "batch modulus left"
    "batch modulus right"
    pairwiseModulusPairKind
    true
    false
    true
    true
    false
    false
    false
    false
    false
    false
    "candidate-only pairwise modulus pair for gcd and shared-prime collapse inspection"
    "no recovered factor witness is promoted from this pair surface"

canonicalRSABatchSharedPrimeModulusPairReceipt :
  RSABatchSharedPrimeModulusPairReceipt
    canonicalRSABatchSharedPrimeModulusPair
canonicalRSABatchSharedPrimeModulusPairReceipt =
  mkRSABatchSharedPrimeModulusPairReceipt
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

canonicalRSABatchSharedPrimeModulusPairCandidateOnlyIsTrue :
  pairCandidateOnly canonicalRSABatchSharedPrimeModulusPair ≡ true
canonicalRSABatchSharedPrimeModulusPairCandidateOnlyIsTrue =
  pairCandidateOnlyIsTrue canonicalRSABatchSharedPrimeModulusPairReceipt

canonicalRSABatchSharedPrimeModulusPairPromotedIsFalse :
  pairPromoted canonicalRSABatchSharedPrimeModulusPair ≡ false
canonicalRSABatchSharedPrimeModulusPairPromotedIsFalse =
  pairPromotedIsFalse canonicalRSABatchSharedPrimeModulusPairReceipt

canonicalRSABatchSharedPrimeModulusPairGcdWitnessCandidateIsTrue :
  pairGcdWitnessCandidate canonicalRSABatchSharedPrimeModulusPair ≡ true
canonicalRSABatchSharedPrimeModulusPairGcdWitnessCandidateIsTrue =
  pairGcdWitnessCandidateIsTrue canonicalRSABatchSharedPrimeModulusPairReceipt

canonicalRSABatchSharedPrimeModulusPairSharedPrimeCollapseCandidateIsTrue :
  pairSharedPrimeCollapseCandidate canonicalRSABatchSharedPrimeModulusPair ≡ true
canonicalRSABatchSharedPrimeModulusPairSharedPrimeCollapseCandidateIsTrue =
  pairSharedPrimeCollapseCandidateIsTrue
    canonicalRSABatchSharedPrimeModulusPairReceipt

canonicalRSABatchSharedPrimeModulusPairRecoveredFactorWitnessBoundaryIsFalse :
  pairRecoveredFactorWitnessBoundary canonicalRSABatchSharedPrimeModulusPair ≡ false
canonicalRSABatchSharedPrimeModulusPairRecoveredFactorWitnessBoundaryIsFalse =
  pairRecoveredFactorWitnessBoundaryIsFalse
    canonicalRSABatchSharedPrimeModulusPairReceipt

canonicalRSABatchSharedPrimeModulusPairs :
  List RSABatchSharedPrimeModulusPair
canonicalRSABatchSharedPrimeModulusPairs =
  canonicalRSABatchSharedPrimeModulusPair
  ∷ []

canonicalRSABatchSharedPrimeModulusPairCount :
  Nat
canonicalRSABatchSharedPrimeModulusPairCount =
  listCount canonicalRSABatchSharedPrimeModulusPairs

------------------------------------------------------------------------
-- Batch surface and receipt.

record RSABatchSharedPrimeBoundarySurface : Set where
  constructor mkRSABatchSharedPrimeBoundarySurface
  field
    surfaceLabel :
      String

    surfaceOwner :
      String

    surfaceName :
      String

    sourceConditionedModulusBatch :
      String

    surfaceKinds :
      List RSABatchSharedPrimeBoundaryKind

    surfaceKindsAreCanonical :
      surfaceKinds ≡ canonicalRSABatchSharedPrimeBoundaryKinds

    surfaceAuthorityClaims :
      List RSABatchAuthorityClaim

    surfaceAuthorityClaimsAreCanonical :
      surfaceAuthorityClaims ≡ canonicalRSABatchAuthorityClaims

    surfaceGenericAuthorityBoundaryClaims :
      List AuthorityBoundary.AuthorityBoundaryClaimKind

    surfaceGenericAuthorityBoundaryClaimsAreCanonical :
      surfaceGenericAuthorityBoundaryClaims
      ≡
      canonicalGenericAuthorityBoundaryClaims

    surfacePairwiseModulusPairs :
      List RSABatchSharedPrimeModulusPair

    surfacePairwiseModulusPairsAreCanonical :
      surfacePairwiseModulusPairs ≡ canonicalRSABatchSharedPrimeModulusPairs

    surfacePairwiseModulusPairCount :
      Nat

    surfacePairwiseModulusPairCountIsCanonical :
      surfacePairwiseModulusPairCount
      ≡
      canonicalRSABatchSharedPrimeModulusPairCount

    sourceConditionedModulusBatchCandidateRow :
      Candidate.CandidateOnlyRow

    sourceConditionedModulusBatchCandidateReceipt :
      Candidate.CandidateOnlyReceipt
        sourceConditionedModulusBatchCandidateRow

    batchAuthorityBundle :
      Authority.AuthorityNonPromotionBundle

    batchBridgeCoreReceipt :
      Bridge.BridgeRequirementCoreReceipt

    batchAdapterReceipt :
      Adapter.AdapterCanonicalityReceipt
        Adapter.AdapterSurface
        Adapter.canonicalAdapter

    batchHiddenLiftProjectionReceipt :
      HiddenLift.HiddenLiftProjectionReceipt
        HiddenLift.canonicalHiddenLiftProjectionSurface

    batchStatisticalEvidenceReceipt :
      Stats.StatisticalEvidenceReceipt
        Stats.canonicalStatisticalEvidenceSurface

    sourceProcessEvidenceReceipt :
      SourceProcessEvidence.SourceProcessEvidenceReceipt
        SourceProcessEvidence.canonicalSourceProcessEvidenceSurface

    batchRSAVulnerabilityBoundary :
      RSA.RSAVulnerabilityBoundary

    batchRSABTResidueBraidHypervoxelBoundarySurface :
      BT.RSABTResidueBraidHypervoxelBoundarySurface

    artifactSpecificVulnerabilityReceipt :
      GenericReceipt.GenericReceipt

    batchCandidateOnly :
      Bool

    batchPromoted :
      Bool

    batchGeneralRSABreakBlocked :
      Bool

    batchFactoringOracleBlocked :
      Bool

    batchSourceWideCompromiseBlocked :
      Bool

    batchSemanticSecurityBreakBlocked :
      Bool

    batchProductionAdvisoryAuthorityBlocked :
      Bool

    batchStatement :
      String

    batchRemainingGap :
      String

open RSABatchSharedPrimeBoundarySurface public

record RSABatchSharedPrimeBoundaryReceipt
  (surface : RSABatchSharedPrimeBoundarySurface) :
  Set where
  constructor mkRSABatchSharedPrimeBoundaryReceipt
  field
    surfaceBatchCandidateOnlyIsTrue :
      batchCandidateOnly surface ≡ true

    surfaceBatchPromotedIsFalse :
      batchPromoted surface ≡ false

    surfaceGeneralRSABreakBlockedIsFalse :
      batchGeneralRSABreakBlocked surface ≡ false

    surfaceFactoringOracleBlockedIsFalse :
      batchFactoringOracleBlocked surface ≡ false

    surfaceSourceWideCompromiseBlockedIsFalse :
      batchSourceWideCompromiseBlocked surface ≡ false

    surfaceSemanticSecurityBreakBlockedIsFalse :
      batchSemanticSecurityBreakBlocked surface ≡ false

    surfaceProductionAdvisoryAuthorityBlockedIsFalse :
      batchProductionAdvisoryAuthorityBlocked surface ≡ false

    surfaceKindsCanonical :
      surfaceKinds surface ≡ canonicalRSABatchSharedPrimeBoundaryKinds

    surfaceAuthorityClaimsCanonical :
      surfaceAuthorityClaims surface ≡ canonicalRSABatchAuthorityClaims

    surfaceGenericAuthorityBoundaryClaimsCanonical :
      surfaceGenericAuthorityBoundaryClaims surface
      ≡
      canonicalGenericAuthorityBoundaryClaims

    surfacePairwiseModulusPairsCanonical :
      surfacePairwiseModulusPairs surface ≡ canonicalRSABatchSharedPrimeModulusPairs

    surfacePairwiseModulusPairCountCanonical :
      surfacePairwiseModulusPairCount surface
      ≡
      canonicalRSABatchSharedPrimeModulusPairCount

    surfaceSourceFiberRestrictsIsTrue :
      SourceProcessEvidence.sideEvidenceRestrictsFiber
        SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
      ≡
      true

    surfaceRecoveredWitnessEscalatesArtifactOnlyIsTrue :
      SourceProcessEvidence.recoveredWitnessEscalatesArtifactOnly
        SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
      ≡
      true

    surfaceSourceWideEscalationAuthorityIsFalse :
      SourceProcessEvidence.sourceWideEscalationAuthority
        SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
      ≡
      false

    surfaceArtifactSpecificVulnerabilityReceiptNonPromoting :
      GenericReceipt.promotesClaim
        (artifactSpecificVulnerabilityReceipt surface)
      ≡
      false

open RSABatchSharedPrimeBoundaryReceipt public

canonicalRSABatchSharedPrimeBoundaryArtifactReceipt :
  GenericReceipt.GenericReceipt
canonicalRSABatchSharedPrimeBoundaryArtifactReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "RSA batch shared-prime boundary"
    "DASHI.Crypto.RSABatchSharedPrimeBoundary"
    "canonicalRSABatchSharedPrimeBoundarySurface"
    "batch moduli, pairwise gcd witnesses, shared-prime collapse candidates, and a recovered-factor boundary are tracked as a candidate-only receipt surface"
    "no general RSA break, no factoring oracle, no source-wide compromise, no semantic-security break, and no production advisory authority are promoted"
    "agda -i . DASHI/Crypto/RSABatchSharedPrimeBoundary.agda"

canonicalRSABatchSharedPrimeBoundarySurface :
  RSABatchSharedPrimeBoundarySurface
canonicalRSABatchSharedPrimeBoundarySurface =
  mkRSABatchSharedPrimeBoundarySurface
    "RSA batch shared-prime boundary"
    "DASHI.Crypto.RSABatchSharedPrimeBoundary"
    "canonicalRSABatchSharedPrimeBoundarySurface"
    "source-conditioned modulus batch"
    canonicalRSABatchSharedPrimeBoundaryKinds
    refl
    canonicalRSABatchAuthorityClaims
    refl
    canonicalGenericAuthorityBoundaryClaims
    refl
    canonicalRSABatchSharedPrimeModulusPairs
    refl
    canonicalRSABatchSharedPrimeModulusPairCount
    refl
    Candidate.canonicalDiagnosticCandidateOnlyRow
    Candidate.canonicalDiagnosticCandidateOnlyReceipt
    Authority.canonicalAuthorityNonPromotionBundle
    Bridge.canonicalBridgeRequirementCoreReceipt
    Adapter.canonicalAdapterCanonicalityReceipt
    HiddenLift.canonicalHiddenLiftProjectionReceipt
    Stats.canonicalStatisticalEvidenceReceipt
    SourceProcessEvidence.canonicalSourceProcessEvidenceReceipt
    RSA.canonicalRSAVulnerabilityBoundary
    BT.canonicalRSABTResidueBraidHypervoxelBoundarySurface
    canonicalRSABatchSharedPrimeBoundaryArtifactReceipt
    true
    false
    false
    false
    false
    false
    false
    "candidate-only batch RSA shared-prime boundary over source-conditioned moduli and pairwise gcd/shared-prime collapse inspection"
    "all authority lanes stay blocked until a separate explicit recovered witness is supplied"

canonicalRSABatchSharedPrimeBoundaryReceipt :
  RSABatchSharedPrimeBoundaryReceipt
    canonicalRSABatchSharedPrimeBoundarySurface
canonicalRSABatchSharedPrimeBoundaryReceipt =
  mkRSABatchSharedPrimeBoundaryReceipt
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

batchCandidateOnlyIsTrue :
  batchCandidateOnly canonicalRSABatchSharedPrimeBoundarySurface ≡ true
batchCandidateOnlyIsTrue =
  surfaceBatchCandidateOnlyIsTrue canonicalRSABatchSharedPrimeBoundaryReceipt

batchPromotedIsFalse :
  batchPromoted canonicalRSABatchSharedPrimeBoundarySurface ≡ false
batchPromotedIsFalse =
  surfaceBatchPromotedIsFalse canonicalRSABatchSharedPrimeBoundaryReceipt

batchGeneralRSABreakBlockedIsFalse :
  batchGeneralRSABreakBlocked canonicalRSABatchSharedPrimeBoundarySurface ≡ false
batchGeneralRSABreakBlockedIsFalse =
  surfaceGeneralRSABreakBlockedIsFalse canonicalRSABatchSharedPrimeBoundaryReceipt

batchFactoringOracleBlockedIsFalse :
  batchFactoringOracleBlocked canonicalRSABatchSharedPrimeBoundarySurface ≡ false
batchFactoringOracleBlockedIsFalse =
  surfaceFactoringOracleBlockedIsFalse canonicalRSABatchSharedPrimeBoundaryReceipt

batchSourceWideCompromiseBlockedIsFalse :
  batchSourceWideCompromiseBlocked canonicalRSABatchSharedPrimeBoundarySurface ≡ false
batchSourceWideCompromiseBlockedIsFalse =
  surfaceSourceWideCompromiseBlockedIsFalse
    canonicalRSABatchSharedPrimeBoundaryReceipt

batchSemanticSecurityBreakBlockedIsFalse :
  batchSemanticSecurityBreakBlocked canonicalRSABatchSharedPrimeBoundarySurface ≡ false
batchSemanticSecurityBreakBlockedIsFalse =
  surfaceSemanticSecurityBreakBlockedIsFalse
    canonicalRSABatchSharedPrimeBoundaryReceipt

batchProductionAdvisoryAuthorityBlockedIsFalse :
  batchProductionAdvisoryAuthorityBlocked canonicalRSABatchSharedPrimeBoundarySurface ≡ false
batchProductionAdvisoryAuthorityBlockedIsFalse =
  surfaceProductionAdvisoryAuthorityBlockedIsFalse
    canonicalRSABatchSharedPrimeBoundaryReceipt

canonicalRSABatchSurfaceKindsAreCanonical :
  surfaceKinds canonicalRSABatchSharedPrimeBoundarySurface
  ≡
  canonicalRSABatchSharedPrimeBoundaryKinds
canonicalRSABatchSurfaceKindsAreCanonical =
  surfaceKindsCanonical canonicalRSABatchSharedPrimeBoundaryReceipt

canonicalRSABatchSurfaceAuthorityClaimsAreCanonical :
  surfaceAuthorityClaims canonicalRSABatchSharedPrimeBoundarySurface
  ≡
  canonicalRSABatchAuthorityClaims
canonicalRSABatchSurfaceAuthorityClaimsAreCanonical =
  surfaceAuthorityClaimsCanonical canonicalRSABatchSharedPrimeBoundaryReceipt

canonicalRSABatchSurfaceGenericAuthorityBoundaryClaimsAreCanonical :
  surfaceGenericAuthorityBoundaryClaims canonicalRSABatchSharedPrimeBoundarySurface
  ≡
  canonicalGenericAuthorityBoundaryClaims
canonicalRSABatchSurfaceGenericAuthorityBoundaryClaimsAreCanonical =
  surfaceGenericAuthorityBoundaryClaimsCanonical
    canonicalRSABatchSharedPrimeBoundaryReceipt

canonicalRSABatchSurfacePairwiseModulusPairsAreCanonical :
  surfacePairwiseModulusPairs canonicalRSABatchSharedPrimeBoundarySurface
  ≡
  canonicalRSABatchSharedPrimeModulusPairs
canonicalRSABatchSurfacePairwiseModulusPairsAreCanonical =
  surfacePairwiseModulusPairsCanonical
    canonicalRSABatchSharedPrimeBoundaryReceipt

canonicalRSABatchSurfacePairwiseModulusPairCountIsCanonical :
  surfacePairwiseModulusPairCount canonicalRSABatchSharedPrimeBoundarySurface
  ≡
  canonicalRSABatchSharedPrimeModulusPairCount
canonicalRSABatchSurfacePairwiseModulusPairCountIsCanonical =
  surfacePairwiseModulusPairCountCanonical
    canonicalRSABatchSharedPrimeBoundaryReceipt

sourceFiberRestrictsIsTrue :
  SourceProcessEvidence.sideEvidenceRestrictsFiber
    SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
  ≡
  true
sourceFiberRestrictsIsTrue =
  surfaceSourceFiberRestrictsIsTrue
    canonicalRSABatchSharedPrimeBoundaryReceipt

recoveredWitnessEscalatesArtifactOnlyIsTrue :
  SourceProcessEvidence.recoveredWitnessEscalatesArtifactOnly
    SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
  ≡
  true
recoveredWitnessEscalatesArtifactOnlyIsTrue =
  surfaceRecoveredWitnessEscalatesArtifactOnlyIsTrue
    canonicalRSABatchSharedPrimeBoundaryReceipt

sourceWideEscalationAuthorityIsFalse :
  SourceProcessEvidence.sourceWideEscalationAuthority
    SourceProcessEvidence.canonicalSourceProcessEvidenceSurface
  ≡
  false
sourceWideEscalationAuthorityIsFalse =
  surfaceSourceWideEscalationAuthorityIsFalse
    canonicalRSABatchSharedPrimeBoundaryReceipt

artifactSpecificVulnerabilityReceiptIsNonPromoting :
  GenericReceipt.promotesClaim
    (artifactSpecificVulnerabilityReceipt
      canonicalRSABatchSharedPrimeBoundarySurface)
  ≡
  false
artifactSpecificVulnerabilityReceiptIsNonPromoting =
  surfaceArtifactSpecificVulnerabilityReceiptNonPromoting
    canonicalRSABatchSharedPrimeBoundaryReceipt
