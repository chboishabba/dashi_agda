module DASHI.Physics.Closure.NSTriadKNMixedTailACLOperatorNormAuditReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSFieldsACLExternalSchurResidueBridgeReceipt as Fields
import DASHI.Physics.Closure.NSTriadKNMixedTailACLSchurResidueProofPlanReceipt as ProofPlan

------------------------------------------------------------------------
-- Candidate-only ACL-to-L_FT^+ operator-norm audit receipt.
--
-- This receipt does not prove the operator-norm estimate.  It records the
-- exact analytic checklist that must be discharged before the Fields ACL
-- carrier can be used for the mixed-tail Schur residue step.

canonicalSampledFiniteShellSchurTestWitnessText : String
canonicalSampledFiniteShellSchurTestWitnessText =
  "sampled finite-shell witness: checked"

canonicalProfileIndependentSchurTestKernelSumBoundText : String
canonicalProfileIndependentSchurTestKernelSumBoundText =
  "profile-independent weighted Schur product bound: open"

record NSTriadKNMixedTailSampledFiniteShellSchurTestWitness : Set where
  field
    statusText :
      String
    statusTextIsCanonical :
      statusText ≡ canonicalSampledFiniteShellSchurTestWitnessText
    scopeText :
      String
    scopeTextIsCanonical :
      scopeText ≡ "N=6,8,10,12; forced-tail rows + sampled adversarial equal-mass worst-tail sweep"
    rowSupRangeText :
      String
    rowSupRangeTextIsCanonical :
      rowSupRangeText ≡ "[0.01147, 0.01166]"
    columnSupRangeText :
      String
    columnSupRangeTextIsCanonical :
      columnSupRangeText ≡ "[9.16e-4, 1.78e-3] adversarial; [9.17e-5, 3.41e-4] forced-tail"
    nTimesBoundText :
      String
    nTimesBoundTextIsCanonical :
      nTimesBoundText ≡ "[0.0118, 0.0128] near-flat"
    profileIndependentText :
      String
    profileIndependentTextIsCanonical :
      profileIndependentText ≡ "false"

canonicalSampledFiniteShellSchurTestWitness :
  NSTriadKNMixedTailSampledFiniteShellSchurTestWitness
canonicalSampledFiniteShellSchurTestWitness = record
  { statusText = canonicalSampledFiniteShellSchurTestWitnessText
  ; statusTextIsCanonical = refl
  ; scopeText =
      "N=6,8,10,12; forced-tail rows + sampled adversarial equal-mass worst-tail sweep"
  ; scopeTextIsCanonical = refl
  ; rowSupRangeText = "[0.01147, 0.01166]"
  ; rowSupRangeTextIsCanonical = refl
  ; columnSupRangeText =
      "[9.16e-4, 1.78e-3] adversarial; [9.17e-5, 3.41e-4] forced-tail"
  ; columnSupRangeTextIsCanonical = refl
  ; nTimesBoundText = "[0.0118, 0.0128] near-flat"
  ; nTimesBoundTextIsCanonical = refl
  ; profileIndependentText = "false"
  ; profileIndependentTextIsCanonical = refl
  }

record NSTriadKNMixedTailProfileIndependentSchurTestKernelSumBound : Set where
  field
    statusText :
      String
    statusTextIsCanonical :
      statusText ≡ canonicalProfileIndependentSchurTestKernelSumBoundText
    targetText :
      String
    targetTextIsCanonical :
      targetText ≡ "weighted Schur target: choose w so that R_N(w) * C_N(w) <= C^2 / N^2, hence ||L_FT^+||_op <= C / N for all NS-compatible profiles"
    missingText :
      String
    missingTextIsCanonical :
      missingText ≡ "direct positive-sector magnitude/counting theorem and a profile-uniform weighted Schur product bound"

canonicalProfileIndependentSchurTestKernelSumBound :
  NSTriadKNMixedTailProfileIndependentSchurTestKernelSumBound
canonicalProfileIndependentSchurTestKernelSumBound = record
  { statusText = canonicalProfileIndependentSchurTestKernelSumBoundText
  ; statusTextIsCanonical = refl
  ; targetText =
      "weighted Schur target: choose w so that R_N(w) * C_N(w) <= C^2 / N^2, hence ||L_FT^+||_op <= C / N for all NS-compatible profiles"
  ; targetTextIsCanonical = refl
  ; missingText =
      "direct positive-sector magnitude/counting theorem and a profile-uniform weighted Schur product bound"
  ; missingTextIsCanonical = refl
  }

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSTriadKNMixedTailACLOperatorNormAuditStatus : Set where
  aclOperatorNormAuditRecorded :
    NSTriadKNMixedTailACLOperatorNormAuditStatus

data NSTriadKNMixedTailACLOperatorNormAuditRow : Set where
  kernelMatchRow :
    NSTriadKNMixedTailACLOperatorNormAuditRow
  shellConventionMatchRow :
    NSTriadKNMixedTailACLOperatorNormAuditRow
  cancellationLiftRow :
    NSTriadKNMixedTailACLOperatorNormAuditRow
  schurTestRouteRow :
    NSTriadKNMixedTailACLOperatorNormAuditRow
  normalizationTransferRow :
    NSTriadKNMixedTailACLOperatorNormAuditRow
  profileScopeRow :
    NSTriadKNMixedTailACLOperatorNormAuditRow

canonicalNSTriadKNMixedTailACLOperatorNormAuditRows :
  List NSTriadKNMixedTailACLOperatorNormAuditRow
canonicalNSTriadKNMixedTailACLOperatorNormAuditRows =
  kernelMatchRow
  ∷ shellConventionMatchRow
  ∷ cancellationLiftRow
  ∷ schurTestRouteRow
  ∷ normalizationTransferRow
  ∷ profileScopeRow
  ∷ []

nSTriadKNMixedTailACLOperatorNormAuditRowCount : Nat
nSTriadKNMixedTailACLOperatorNormAuditRowCount =
  listLength canonicalNSTriadKNMixedTailACLOperatorNormAuditRows

nSTriadKNMixedTailACLOperatorNormAuditRowCountIs6 :
  nSTriadKNMixedTailACLOperatorNormAuditRowCount ≡ 6
nSTriadKNMixedTailACLOperatorNormAuditRowCountIs6 = refl

data NSTriadKNMixedTailACLOperatorNormAuditCandidateLemma : Set where
  aclCarrierCandidate :
    NSTriadKNMixedTailACLOperatorNormAuditCandidateLemma
  operatorNormGateCandidate :
    NSTriadKNMixedTailACLOperatorNormAuditCandidateLemma
  schurResidueTransferCandidate :
    NSTriadKNMixedTailACLOperatorNormAuditCandidateLemma

canonicalNSTriadKNMixedTailACLOperatorNormAuditCandidateLemmas :
  List NSTriadKNMixedTailACLOperatorNormAuditCandidateLemma
canonicalNSTriadKNMixedTailACLOperatorNormAuditCandidateLemmas =
  aclCarrierCandidate
  ∷ operatorNormGateCandidate
  ∷ schurResidueTransferCandidate
  ∷ []

nSTriadKNMixedTailACLOperatorNormAuditCandidateLemmaCount : Nat
nSTriadKNMixedTailACLOperatorNormAuditCandidateLemmaCount =
  listLength canonicalNSTriadKNMixedTailACLOperatorNormAuditCandidateLemmas

nSTriadKNMixedTailACLOperatorNormAuditCandidateLemmaCountIs3 :
  nSTriadKNMixedTailACLOperatorNormAuditCandidateLemmaCount ≡ 3
nSTriadKNMixedTailACLOperatorNormAuditCandidateLemmaCountIs3 = refl

data NSTriadKNMixedTailACLOperatorNormAuditOpenGap : Set where
  exactKernelNormalizationOpen :
    NSTriadKNMixedTailACLOperatorNormAuditOpenGap
  shellCountLiftOpen :
    NSTriadKNMixedTailACLOperatorNormAuditOpenGap
  uniformAsymptoticSchurDecayOpen :
    NSTriadKNMixedTailACLOperatorNormAuditOpenGap
  qGapNormalizationOpen :
    NSTriadKNMixedTailACLOperatorNormAuditOpenGap
  profileScopeOpen :
    NSTriadKNMixedTailACLOperatorNormAuditOpenGap
  noTheoremFullNSOrClayPromotion :
    NSTriadKNMixedTailACLOperatorNormAuditOpenGap

canonicalNSTriadKNMixedTailACLOperatorNormAuditOpenGaps :
  List NSTriadKNMixedTailACLOperatorNormAuditOpenGap
canonicalNSTriadKNMixedTailACLOperatorNormAuditOpenGaps =
  exactKernelNormalizationOpen
  ∷ shellCountLiftOpen
  ∷ uniformAsymptoticSchurDecayOpen
  ∷ qGapNormalizationOpen
  ∷ profileScopeOpen
  ∷ noTheoremFullNSOrClayPromotion
  ∷ []

nSTriadKNMixedTailACLOperatorNormAuditOpenGapCount : Nat
nSTriadKNMixedTailACLOperatorNormAuditOpenGapCount =
  listLength canonicalNSTriadKNMixedTailACLOperatorNormAuditOpenGaps

nSTriadKNMixedTailACLOperatorNormAuditOpenGapCountIs6 :
  nSTriadKNMixedTailACLOperatorNormAuditOpenGapCount ≡ 6
nSTriadKNMixedTailACLOperatorNormAuditOpenGapCountIs6 = refl

data NSTriadKNMixedTailACLOperatorNormAuditPromotion : Set where

promotionImpossibleHere :
  NSTriadKNMixedTailACLOperatorNormAuditPromotion → ⊥
promotionImpossibleHere ()

canonicalReceiptText : String
canonicalReceiptText =
  "Candidate-only ACL-to-L_FT^+ operator-norm audit receipt for the mixed-tail lane."

canonicalReadoutText : String
canonicalReadoutText =
  "The sampled finite-shell witness records the checked N=6,8,10,12 mixed-tail rows and N^-1 block scale, but the direct ACL kernel match now fails for the current positive-sector L_FT^+ because the exact entry carries profile amplitudes and max(cos(closure),0); the corrected signed half-sum test also leaves S_+ = S_abs/2, so the live open gate is a profile-uniform weighted Schur product bound on the direct positive-sector route."

canonicalSourceFieldsReceiptText : String
canonicalSourceFieldsReceiptText =
  Fields.canonicalReceiptText

canonicalSourceProofPlanText : String
canonicalSourceProofPlanText =
  ProofPlan.canonicalProofPlanText

canonicalFiniteShellProofArtifactJSON : String
canonicalFiniteShellProofArtifactJSON =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_acl_schur_test_proof_20260624/summary.json"

canonicalFiniteShellProofArtifactMarkdown : String
canonicalFiniteShellProofArtifactMarkdown =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_acl_schur_test_proof_20260624/summary.md"

canonicalAuditText : String
canonicalAuditText =
  "Audit target: exact L_FT^+ normalization, ACL kernel comparison, unit-width shell match, first-harmonic cancellation survival, signed half-sum fork resolution, sampled finite-shell witness, failed direct kernel match receipt, profile-independent Schur-test kernel-sum bound, finite-shell proof artifact, uniform L2 operator-norm route, N^-2 residue transfer, and profile scope."

canonicalBoundaryText : String
canonicalBoundaryText =
  "Boundary: this audit records the proof checklist, the sampled finite-shell witness, the failed direct ACL kernel match, the failed signed rescue, and the still-open profile-independent Schur-test bound only; theorem/full-NS/BKM/Clay promotion remains false."

canonicalOText : String
canonicalOText =
  "O: record the ACL-to-L_FT^+ operator-norm audit as a candidate-only bridge receipt."

canonicalRText : String
canonicalRText =
  "R: line up the Fields ACL carrier against the exact mixed-tail operator normalization."

canonicalCText : String
canonicalCText =
  "C: export the checklist rows, candidate lemmas, sampled witness, open profile-independent bound, finite-shell proof artifacts, open gaps, and false promotion flags."

canonicalSText : String
canonicalSText =
  "S: proof checklist only; no theorem authority, no full-NS promotion, no BKM exclusion proof, and no Clay promotion."

canonicalLText : String
canonicalLText =
  "L: sampled finite-shell witness -> failed direct ACL kernel match -> failed signed rescue -> operator-norm gate still open on the direct positive-sector route -> Schur residue transfer still open."

canonicalPText : String
canonicalPText =
  "P: keep the sampled N^-1 witness, but prove the direct positive-sector magnitude/counting theorem and then a weighted Schur product bound R_N(w) * C_N(w) <= C^2 / N^2 before attempting theorem promotion."

canonicalGText : String
canonicalGText =
  "G: keep the audit fail-closed; the finite-shell proof does not by itself justify a uniform operator-norm theorem, and the direct ACL kernel match is dead for the current positive-sector block."

canonicalFText : String
canonicalFText =
  "F: the open gap is the profile-independent operator-norm theorem on the direct positive-sector carrier, not the existence of the sampled witness."

record NSTriadKNMixedTailACLOperatorNormAuditORCSLPGF : Set where
  constructor mkNSTriadKNMixedTailACLOperatorNormAuditORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ canonicalOText
    R : String
    RIsCanonical : R ≡ canonicalRText
    C : String
    CIsCanonical : C ≡ canonicalCText
    S : String
    SIsCanonical : S ≡ canonicalSText
    L : String
    LIsCanonical : L ≡ canonicalLText
    P : String
    PIsCanonical : P ≡ canonicalPText
    G : String
    GIsCanonical : G ≡ canonicalGText
    F : String
    FIsCanonical : F ≡ canonicalFText

canonicalNSTriadKNMixedTailACLOperatorNormAuditORCSLPGF :
  NSTriadKNMixedTailACLOperatorNormAuditORCSLPGF
canonicalNSTriadKNMixedTailACLOperatorNormAuditORCSLPGF =
  mkNSTriadKNMixedTailACLOperatorNormAuditORCSLPGF
    canonicalOText
    refl
    canonicalRText
    refl
    canonicalCText
    refl
    canonicalSText
    refl
    canonicalLText
    refl
    canonicalPText
    refl
    canonicalGText
    refl
    canonicalFText
    refl

record NSTriadKNMixedTailACLOperatorNormAuditReceipt : Setω where
  constructor mkNSTriadKNMixedTailACLOperatorNormAuditReceipt
  field
    receiptName :
      String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNMixedTailACLOperatorNormAuditReceipt"

    status :
      NSTriadKNMixedTailACLOperatorNormAuditStatus
    statusIsCanonical :
      status ≡ aclOperatorNormAuditRecorded

    receiptText :
      String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    readoutText :
      String
    readoutTextIsCanonical :
      readoutText ≡ canonicalReadoutText

    sourceFieldsReceiptText :
      String
    sourceFieldsReceiptTextIsCanonical :
      sourceFieldsReceiptText ≡ canonicalSourceFieldsReceiptText

    sourceProofPlanText :
      String
    sourceProofPlanTextIsCanonical :
      sourceProofPlanText ≡ canonicalSourceProofPlanText

    finiteShellProofArtifactJSON :
      String
    finiteShellProofArtifactJSONIsCanonical :
      finiteShellProofArtifactJSON ≡ canonicalFiniteShellProofArtifactJSON

    finiteShellProofArtifactMarkdown :
      String
    finiteShellProofArtifactMarkdownIsCanonical :
      finiteShellProofArtifactMarkdown ≡ canonicalFiniteShellProofArtifactMarkdown

    sampledFiniteShellSchurTestWitness :
      NSTriadKNMixedTailSampledFiniteShellSchurTestWitness
    sampledFiniteShellSchurTestWitnessIsCanonical :
      sampledFiniteShellSchurTestWitness ≡ canonicalSampledFiniteShellSchurTestWitness

    profileIndependentSchurTestKernelSumBound :
      NSTriadKNMixedTailProfileIndependentSchurTestKernelSumBound
    profileIndependentSchurTestKernelSumBoundIsCanonical :
      profileIndependentSchurTestKernelSumBound ≡ canonicalProfileIndependentSchurTestKernelSumBound

    auditText :
      String
    auditTextIsCanonical :
      auditText ≡ canonicalAuditText

    boundaryText :
      String
    boundaryTextIsCanonical :
      boundaryText ≡ canonicalBoundaryText

    rows :
      List NSTriadKNMixedTailACLOperatorNormAuditRow
    rowsAreCanonical :
      rows ≡ canonicalNSTriadKNMixedTailACLOperatorNormAuditRows

    candidateLemmas :
      List NSTriadKNMixedTailACLOperatorNormAuditCandidateLemma
    candidateLemmasAreCanonical :
      candidateLemmas ≡ canonicalNSTriadKNMixedTailACLOperatorNormAuditCandidateLemmas

    openGaps :
      List NSTriadKNMixedTailACLOperatorNormAuditOpenGap
    openGapsAreCanonical :
      openGaps ≡ canonicalNSTriadKNMixedTailACLOperatorNormAuditOpenGaps

    orcslpgf :
      NSTriadKNMixedTailACLOperatorNormAuditORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadKNMixedTailACLOperatorNormAuditORCSLPGF

    rowCount :
      Nat
    rowCountIsCanonical :
      rowCount ≡ 6

    candidateLemmaCount :
      Nat
    candidateLemmaCountIsCanonical :
      candidateLemmaCount ≡ 3

    openGapCount :
      Nat
    openGapCountIsCanonical :
      openGapCount ≡ 6

    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    fullNSPromoted :
      Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    bkmExclusionProved :
      Bool
    bkmExclusionProvedIsFalse :
      bkmExclusionProved ≡ false

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

canonicalNSTriadKNMixedTailACLOperatorNormAuditReceipt :
  NSTriadKNMixedTailACLOperatorNormAuditReceipt
canonicalNSTriadKNMixedTailACLOperatorNormAuditReceipt =
  mkNSTriadKNMixedTailACLOperatorNormAuditReceipt
    "NSTriadKNMixedTailACLOperatorNormAuditReceipt"
    refl
    aclOperatorNormAuditRecorded
    refl
    canonicalReceiptText
    refl
    canonicalReadoutText
    refl
    canonicalSourceFieldsReceiptText
    refl
    canonicalSourceProofPlanText
    refl
    canonicalFiniteShellProofArtifactJSON
    refl
    canonicalFiniteShellProofArtifactMarkdown
    refl
    canonicalSampledFiniteShellSchurTestWitness
    refl
    canonicalProfileIndependentSchurTestKernelSumBound
    refl
    canonicalAuditText
    refl
    canonicalBoundaryText
    refl
    canonicalNSTriadKNMixedTailACLOperatorNormAuditRows
    refl
    canonicalNSTriadKNMixedTailACLOperatorNormAuditCandidateLemmas
    refl
    canonicalNSTriadKNMixedTailACLOperatorNormAuditOpenGaps
    refl
    canonicalNSTriadKNMixedTailACLOperatorNormAuditORCSLPGF
    refl
    6
    refl
    3
    refl
    6
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
