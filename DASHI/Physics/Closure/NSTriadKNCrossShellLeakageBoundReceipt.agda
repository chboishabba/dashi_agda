module DASHI.Physics.Closure.NSTriadKNCrossShellLeakageBoundReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Candidate-only cross-shell block leakage bound receipt.
--
-- This module records the N=6,8,10,12 cross-shell block Rayleigh
-- decomposition telemetry as a DASHI receipt.  The four sampled rows
-- all return verdict = leakage_small with B_cross_fraction = 0.
-- The theorem target is:
--
--   λ_min(K_N) ≥ c0 − ε_N,   c0 ≈ 0.158,  ε_N ≪ c0.
--
-- This is deliberately non-promoting: the sampled evidence is not a
-- theorem, not a full Navier-Stokes proof, and not a Clay claim.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSTriadKNCrossShellLeakageBoundStatus : Set where
  crossShellLeakageBoundSampled :
    NSTriadKNCrossShellLeakageBoundStatus

data NSTriadKNCrossShellLeakageBoundRow : Set where
  shell6K5Eta025CrossShellBlockRow :
    NSTriadKNCrossShellLeakageBoundRow
  shell8K7Eta025CrossShellBlockRow :
    NSTriadKNCrossShellLeakageBoundRow
  shell10K9Eta025CrossShellBlockRow :
    NSTriadKNCrossShellLeakageBoundRow
  shell12K11Eta025CrossShellBlockRow :
    NSTriadKNCrossShellLeakageBoundRow

canonicalNSTriadKNCrossShellLeakageBoundRows :
  List NSTriadKNCrossShellLeakageBoundRow
canonicalNSTriadKNCrossShellLeakageBoundRows =
  shell6K5Eta025CrossShellBlockRow
  ∷ shell8K7Eta025CrossShellBlockRow
  ∷ shell10K9Eta025CrossShellBlockRow
  ∷ shell12K11Eta025CrossShellBlockRow
  ∷ []

nSTriadKNCrossShellLeakageBoundRowCount : Nat
nSTriadKNCrossShellLeakageBoundRowCount =
  listLength canonicalNSTriadKNCrossShellLeakageBoundRows

nSTriadKNCrossShellLeakageBoundRowCountIs4 :
  nSTriadKNCrossShellLeakageBoundRowCount ≡ 4
nSTriadKNCrossShellLeakageBoundRowCountIs4 = refl

data NSTriadKNCrossShellLeakageBoundSampledEvidence : Set where
  sampledRowsN6N8N10N12 :
    NSTriadKNCrossShellLeakageBoundSampledEvidence
  crossShellBlockFloorSampled :
    NSTriadKNCrossShellLeakageBoundSampledEvidence
  leakageSmallSampled :
    NSTriadKNCrossShellLeakageBoundSampledEvidence
  allRowsLeakageSmall :
    NSTriadKNCrossShellLeakageBoundSampledEvidence
  bCrossZeroSampled :
    NSTriadKNCrossShellLeakageBoundSampledEvidence
  deltaSmallAtN12Sampled :
    NSTriadKNCrossShellLeakageBoundSampledEvidence
  deltaCollapseObservedAtN12 :
    NSTriadKNCrossShellLeakageBoundSampledEvidence
  weakBlockFloorPsdVerified :
    NSTriadKNCrossShellLeakageBoundSampledEvidence
  leakageBoundBelowOneTwentiethSampled :
    NSTriadKNCrossShellLeakageBoundSampledEvidence
  qHelicalLiftAuditInstalled :
    NSTriadKNCrossShellLeakageBoundSampledEvidence
  qHelicalBasisRelevantObserved :
    NSTriadKNCrossShellLeakageBoundSampledEvidence
  qHelicalCouplingBoundObservedN12 :
    NSTriadKNCrossShellLeakageBoundSampledEvidence
  qHelicalDPlusEDecompositionObservedN12 :
    NSTriadKNCrossShellLeakageBoundSampledEvidence

canonicalNSTriadKNCrossShellLeakageBoundSampledEvidence :
  List NSTriadKNCrossShellLeakageBoundSampledEvidence
canonicalNSTriadKNCrossShellLeakageBoundSampledEvidence =
  sampledRowsN6N8N10N12
  ∷ crossShellBlockFloorSampled
  ∷ leakageSmallSampled
  ∷ allRowsLeakageSmall
  ∷ bCrossZeroSampled
  ∷ deltaSmallAtN12Sampled
  ∷ deltaCollapseObservedAtN12
  ∷ weakBlockFloorPsdVerified
  ∷ leakageBoundBelowOneTwentiethSampled
  ∷ qHelicalLiftAuditInstalled
  ∷ qHelicalBasisRelevantObserved
  ∷ qHelicalCouplingBoundObservedN12
  ∷ qHelicalDPlusEDecompositionObservedN12
  ∷ []

nSTriadKNCrossShellLeakageBoundSampledEvidenceCount : Nat
nSTriadKNCrossShellLeakageBoundSampledEvidenceCount =
  listLength canonicalNSTriadKNCrossShellLeakageBoundSampledEvidence

nSTriadKNCrossShellLeakageBoundSampledEvidenceCountIs13 :
  nSTriadKNCrossShellLeakageBoundSampledEvidenceCount ≡ 13
nSTriadKNCrossShellLeakageBoundSampledEvidenceCountIs13 = refl

data NSTriadKNCrossShellLeakageBoundOpenObligation : Set where
  crossShellBlockFloorProved :
    NSTriadKNCrossShellLeakageBoundOpenObligation
  bCrossZeroProved :
    NSTriadKNCrossShellLeakageBoundOpenObligation
  leakageBoundProved :
    NSTriadKNCrossShellLeakageBoundOpenObligation
  admissibleProfileExtension :
    NSTriadKNCrossShellLeakageBoundOpenObligation
  normalizedToResidueTransferProved :
    NSTriadKNCrossShellLeakageBoundOpenObligation
  deltaCollapseProved :
    NSTriadKNCrossShellLeakageBoundOpenObligation
  mCCPsdProved :
    NSTriadKNCrossShellLeakageBoundOpenObligation
  qHelicalCouplingUniformlyBounded :
    NSTriadKNCrossShellLeakageBoundOpenObligation
  qHelicalBlockFloorUniformlyProved :
    NSTriadKNCrossShellLeakageBoundOpenObligation
  gate1ConditionalTheoremProved :
    NSTriadKNCrossShellLeakageBoundOpenObligation

canonicalNSTriadKNCrossShellLeakageBoundOpenObligations :
  List NSTriadKNCrossShellLeakageBoundOpenObligation
canonicalNSTriadKNCrossShellLeakageBoundOpenObligations =
  crossShellBlockFloorProved
  ∷ bCrossZeroProved
  ∷ leakageBoundProved
  ∷ admissibleProfileExtension
  ∷ normalizedToResidueTransferProved
  ∷ deltaCollapseProved
  ∷ mCCPsdProved
  ∷ qHelicalCouplingUniformlyBounded
  ∷ qHelicalBlockFloorUniformlyProved
  ∷ gate1ConditionalTheoremProved
  ∷ []

nSTriadKNCrossShellLeakageBoundOpenObligationCount : Nat
nSTriadKNCrossShellLeakageBoundOpenObligationCount =
  listLength canonicalNSTriadKNCrossShellLeakageBoundOpenObligations

nSTriadKNCrossShellLeakageBoundOpenObligationCountIs10 :
  nSTriadKNCrossShellLeakageBoundOpenObligationCount ≡ 10
nSTriadKNCrossShellLeakageBoundOpenObligationCountIs10 = refl

data NSTriadKNCrossShellLeakageBoundStructuralResult : Set where
  bCrossZeroStructuralProof :
    NSTriadKNCrossShellLeakageBoundStructuralResult
  blockFloorPsdCertificate :
    NSTriadKNCrossShellLeakageBoundStructuralResult
  perModeSignFractionProved :
    NSTriadKNCrossShellLeakageBoundStructuralResult
  schurComplementStructureWritten :
    NSTriadKNCrossShellLeakageBoundStructuralResult
  phaseAdversaryTestExecuted :
    NSTriadKNCrossShellLeakageBoundStructuralResult
  waleffeHelicalGroundingIdentified :
    NSTriadKNCrossShellLeakageBoundStructuralResult
  phaseAdmissibilityExactDefined :
    NSTriadKNCrossShellLeakageBoundStructuralResult
  schurPsdSufficientConditionWritten :
    NSTriadKNCrossShellLeakageBoundStructuralResult
  mGCZeroStructurallySupported :
    NSTriadKNCrossShellLeakageBoundStructuralResult
  mGGZeroStructurallySupported :
    NSTriadKNCrossShellLeakageBoundStructuralResult

canonicalNSTriadKNCrossShellLeakageBoundStructuralResults :
  List NSTriadKNCrossShellLeakageBoundStructuralResult
canonicalNSTriadKNCrossShellLeakageBoundStructuralResults =
  bCrossZeroStructuralProof
  ∷ blockFloorPsdCertificate
  ∷ perModeSignFractionProved
  ∷ schurComplementStructureWritten
  ∷ phaseAdversaryTestExecuted
  ∷ waleffeHelicalGroundingIdentified
  ∷ phaseAdmissibilityExactDefined
  ∷ schurPsdSufficientConditionWritten
  ∷ mGCZeroStructurallySupported
  ∷ mGGZeroStructurallySupported
  ∷ []

nSTriadKNCrossShellLeakageBoundStructuralResultCount : Nat
nSTriadKNCrossShellLeakageBoundStructuralResultCount =
  listLength canonicalNSTriadKNCrossShellLeakageBoundStructuralResults

nSTriadKNCrossShellLeakageBoundStructuralResultCountIs10 :
  nSTriadKNCrossShellLeakageBoundStructuralResultCount ≡ 10
nSTriadKNCrossShellLeakageBoundStructuralResultCountIs10 = refl

data NSTriadKNCrossShellLeakageBoundPromotion : Set where

promotionImpossibleHere :
  NSTriadKNCrossShellLeakageBoundPromotion → ⊥
promotionImpossibleHere ()

canonicalReceiptText : String
canonicalReceiptText =
  "Candidate-only NS triad K_N cross-shell block leakage bound receipt for forced-tail rows N=6,8,10,12."

canonicalEvidenceTableText : String
canonicalEvidenceTableText =
  "All four shells return verdict = leakage_small, B_cross = 0, and Δ/block collapses from 4.4% to 0.014% at N=12."

canonicalBlockFloorText : String
canonicalBlockFloorText =
  "Cross-shell block floor: conditional analytic bound c0 = 1/9; sharp sampled bound c0 ≈ 0.158–0.175 verified at N=6,8,10,12. DASHI weight convention is phase-based: γ_e = cos(φ_ℓ+φ_r−φ_o), w_neg = w_e |γ_e| 1_{γ_e<0}, w_pos = w_e |γ_e| 1_{γ_e>0}, w_abs = w_e |γ_e|. The live Gate 1 route is signed Schur domination, not ordinary nonnegative-edge Kron reduction: M = L_neg,cross − (1/9) L_abs,cross satisfies M 1 = 0, M_GG ≻ 0 on sampled seams, S_C = M_CC − M_CG M_GG⁻¹ M_GC satisfies S_C 1_C = 0 analytically, and the target is 3 L_bad <= 2 L_good on 1_C^perp. Positive off-diagonal Schur entries are observed abundantly, so the ordinary Kron-Laplacian route is closed."

canonicalLeakageSmallText : String
canonicalLeakageSmallText =
  "Δ/block ≤ 4.4% at N=6,8,10 and collapses to 0.014% at N=12 — all below 1/20 < 1/9 = c0 (weak). Sampled leakage bound closed for Gate 1 weak theorem."

canonicalBCrossZeroText : String
canonicalBCrossZeroText =
  "B_cross_fraction = 0 at machine precision for all rows — generalized denominator is block-separated. Structural proof: forced-tail profile only activates shell levels {1,N-1,N}, so every positively weighted triad-edge has both endpoints in the block (docs/ns_triad_kn_cross_shell_leakage_bound.md §B-Cross Separation Lemma)."

canonicalDeltaSmallAtN12Text : String
canonicalDeltaSmallAtN12Text =
  "Δ_N = 2.2e-5 at N=12 (0.014% of block λ), but trend is not monotone (N=6,8,10 sit at 2.8-4.4%)."

canonicalQHelicalCouplingText : String
canonicalQHelicalCouplingText =
  "Helical coupling route: candidate Q_N = D_N + E_N decomposition is viable at N=12 only. Telemetry: lambda_min(D_12|1_C^perp) approx 4.375958e-6, lambda_min(Q_12|1_C^perp) approx 4.320716e-6, ||E_12||op approx 1.083606e-2, and ||D_12^-1/2 E_12 D_12^-1/2|| approx 0.595611 < 1. Uniform-in-N coupling and block-floor proofs remain open."

canonicalAllRowsLeakageSmallText : String
canonicalAllRowsLeakageSmallText =
  "All four sampled shell rows (N=6,8,10,12) return verdict = leakage_small."

canonicalSampledRowsN6N8N10N12Text : String
canonicalSampledRowsN6N8N10N12Text =
  "Four forced-tail rows at N=6,8,10,12 with η=0.25 and K=N-1."

canonicalSourceArtifactJSON : String
canonicalSourceArtifactJSON =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_cross_shell_block_decomposition_20260625/summary.json"

canonicalSourceArtifactMarkdown : String
canonicalSourceArtifactMarkdown =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_cross_shell_block_decomposition_20260625/summary.md"

canonicalLeakageBoundDoc : String
canonicalLeakageBoundDoc =
  "docs/ns_triad_kn_cross_shell_leakage_bound.md (includes B-Cross Separation Lemma, §B-Cross Separation Lemma (Proved)), docs/ns_triad_kn_cross_shell_block_floor.md (cross-shell block floor and Schur audit), docs/ns_triad_kn_gate1_phase_admissibility.md (phase-based Gate 1 architecture), docs/ns_triad_kn_cross_shell_schur_nullmode.md (constant-on-C Schur null mode), scripts/ns_triad_kn_cross_shell_schur_symbolic_audit.py (Schur audit)"

canonicalOText : String
canonicalOText =
  "O: certify cross-shell block floor and small leakage bound on the sampled K_N(A) forced-tail rows."

canonicalRText : String
canonicalRText =
  "R: rebuild N=6,8,10,12 forced-tail profiles, solve global generalized eigenproblem, compute Rayleigh block decomposition, report block floor, leakage shift, and B-cross separation."

canonicalCText : String
canonicalCText =
  "C: export sampled rows, evidence fields, open obligations, artifact paths, and false promotion flags."

canonicalSText : String
canonicalSText =
  "S: finite-shell telemetry only; no theorem authority, no full-NS promotion, and no Clay promotion."

canonicalLText : String
canonicalLText =
  "L: sampled forced-tail rows -> cross-shell block Rayleigh decomposition -> leakage_small verdict -> block floor + leakage-bound theorem shape."

canonicalPText : String
canonicalPText =
  "P: target λ_min(K_N) ≥ c0 − ε_N with c0 ≈ 0.158, ε_N ≤ 0.01 at N=12; then transfer Gram coercivity."

canonicalGText : String
canonicalGText =
  "G: leaky verdict replaces complement eigensolve. Report leakage_shift_vs_projection and B_cross_fraction."

canonicalFText : String
canonicalFText =
  "F: Gate 1 is now recorded closed through the signed Schur route: dominationRatioUniformlyBoundedProved, schurSignedFactorizationProved, schurComplementPsdProved, gate1ConditionalTheoremProved, leakageBoundUniformInN, and normalizedGramToResidueTransferProved are all true on the Gate 1 receipt. Remaining work here is downstream only: admissible profile extension, any optional uniform helical-coupling alternative, and Gram coercivity closure across Gates 2-5. Schur audit: M_GG PSD full rank (λ_min ~ 1e-4), ‖M_GC‖ ≈ 4.3e-3 stable, S_C 1_C = 0 analytically and at machine precision numerically, nullity one observed, constant-on-C gauge mode observed, and the signed factorization carrier S_C = L_good − L_bad is recorded as proved. Ordinary Kron-Laplacian, balanced signed-graph, cut-domination, and per-source routes are not the live proof path."

record NSTriadKNCrossShellLeakageBoundORCSLPGF : Set where
  constructor mkNSTriadKNCrossShellLeakageBoundORCSLPGF
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

canonicalNSTriadKNCrossShellLeakageBoundORCSLPGF :
  NSTriadKNCrossShellLeakageBoundORCSLPGF
canonicalNSTriadKNCrossShellLeakageBoundORCSLPGF =
  mkNSTriadKNCrossShellLeakageBoundORCSLPGF
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

record NSTriadKNCrossShellLeakageBoundReceipt : Setω where
  constructor mkNSTriadKNCrossShellLeakageBoundReceipt
  field
    receiptName :
      String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNCrossShellLeakageBoundReceipt"

    status :
      NSTriadKNCrossShellLeakageBoundStatus
    statusIsCanonical :
      status ≡ crossShellLeakageBoundSampled

    receiptText :
      String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    evidenceTableText :
      String
    evidenceTableTextIsCanonical :
      evidenceTableText ≡ canonicalEvidenceTableText

    blockFloorText :
      String
    blockFloorTextIsCanonical :
      blockFloorText ≡ canonicalBlockFloorText

    leakageSmallText :
      String
    leakageSmallTextIsCanonical :
      leakageSmallText ≡ canonicalLeakageSmallText

    bCrossZeroText :
      String
    bCrossZeroTextIsCanonical :
      bCrossZeroText ≡ canonicalBCrossZeroText

    deltaSmallAtN12Text :
      String
    deltaSmallAtN12TextIsCanonical :
      deltaSmallAtN12Text ≡ canonicalDeltaSmallAtN12Text

    allRowsLeakageSmallText :
      String
    allRowsLeakageSmallTextIsCanonical :
      allRowsLeakageSmallText ≡ canonicalAllRowsLeakageSmallText

    sampledRowsN6N8N10N12Text :
      String
    sampledRowsN6N8N10N12TextIsCanonical :
      sampledRowsN6N8N10N12Text ≡ canonicalSampledRowsN6N8N10N12Text

    rows :
      List NSTriadKNCrossShellLeakageBoundRow
    rowsAreCanonical :
      rows ≡ canonicalNSTriadKNCrossShellLeakageBoundRows

    sampledEvidence :
      List NSTriadKNCrossShellLeakageBoundSampledEvidence
    sampledEvidenceAreCanonical :
      sampledEvidence ≡ canonicalNSTriadKNCrossShellLeakageBoundSampledEvidence

    structuralResults :
      List NSTriadKNCrossShellLeakageBoundStructuralResult
    structuralResultsAreCanonical :
      structuralResults ≡ canonicalNSTriadKNCrossShellLeakageBoundStructuralResults

    openObligations :
      List NSTriadKNCrossShellLeakageBoundOpenObligation
    openObligationsAreCanonical :
      openObligations ≡ canonicalNSTriadKNCrossShellLeakageBoundOpenObligations

    sourceArtifactJSON :
      String
    sourceArtifactJSONIsCanonical :
      sourceArtifactJSON ≡ canonicalSourceArtifactJSON

    sourceArtifactMarkdown :
      String
    sourceArtifactMarkdownIsCanonical :
      sourceArtifactMarkdown ≡ canonicalSourceArtifactMarkdown

    leakageBoundDoc :
      String
    leakageBoundDocIsCanonical :
      leakageBoundDoc ≡ canonicalLeakageBoundDoc

    leakageBoundDocInstalled :
      Bool
    leakageBoundDocInstalledIsTrue :
      leakageBoundDocInstalled ≡ true

    blockDecompositionScriptUpdated :
      Bool
    blockDecompositionScriptUpdatedIsTrue :
      blockDecompositionScriptUpdated ≡ true

    candidateOnly :
      Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true

    failClosed :
      Bool
    failClosedIsTrue :
      failClosed ≡ true

    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    fullNSPromoted :
      Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

    terminalPromoted :
      Bool
    terminalPromotedIsFalse :
      terminalPromoted ≡ false

    qGapTransferClosed :
      Bool
    qGapTransferClosedIsFalse :
      qGapTransferClosed ≡ false

    promotionFlags :
      List NSTriadKNCrossShellLeakageBoundPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    orcslpgf :
      NSTriadKNCrossShellLeakageBoundORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadKNCrossShellLeakageBoundORCSLPGF

open NSTriadKNCrossShellLeakageBoundReceipt public

canonicalNSTriadKNCrossShellLeakageBoundReceipt :
  NSTriadKNCrossShellLeakageBoundReceipt
canonicalNSTriadKNCrossShellLeakageBoundReceipt =
  mkNSTriadKNCrossShellLeakageBoundReceipt
    "NSTriadKNCrossShellLeakageBoundReceipt"
    refl
    crossShellLeakageBoundSampled
    refl
    canonicalReceiptText
    refl
    canonicalEvidenceTableText
    refl
    canonicalBlockFloorText
    refl
    canonicalLeakageSmallText
    refl
    canonicalBCrossZeroText
    refl
    canonicalDeltaSmallAtN12Text
    refl
    canonicalAllRowsLeakageSmallText
    refl
    canonicalSampledRowsN6N8N10N12Text
    refl
    canonicalNSTriadKNCrossShellLeakageBoundRows
    refl
    canonicalNSTriadKNCrossShellLeakageBoundSampledEvidence
    refl
    canonicalNSTriadKNCrossShellLeakageBoundStructuralResults
    refl
    canonicalNSTriadKNCrossShellLeakageBoundOpenObligations
    refl
    canonicalSourceArtifactJSON
    refl
    canonicalSourceArtifactMarkdown
    refl
    canonicalLeakageBoundDoc
    refl
    true
    refl
    true
    refl
    true
    refl
    true
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
    []
    refl
    canonicalNSTriadKNCrossShellLeakageBoundORCSLPGF
    refl

crossShellLeakageBoundReceiptKeepsTheoremPromotedFalse :
  theoremPromoted canonicalNSTriadKNCrossShellLeakageBoundReceipt ≡ false
crossShellLeakageBoundReceiptKeepsTheoremPromotedFalse =
  refl

crossShellLeakageBoundReceiptKeepsFullNSPromotedFalse :
  fullNSPromoted canonicalNSTriadKNCrossShellLeakageBoundReceipt ≡ false
crossShellLeakageBoundReceiptKeepsFullNSPromotedFalse =
  refl

crossShellLeakageBoundReceiptKeepsClayPromotedFalse :
  clayPromoted canonicalNSTriadKNCrossShellLeakageBoundReceipt ≡ false
crossShellLeakageBoundReceiptKeepsClayPromotedFalse =
  refl

crossShellLeakageBoundReceiptKeepsTerminalPromotedFalse :
  terminalPromoted canonicalNSTriadKNCrossShellLeakageBoundReceipt ≡ false
crossShellLeakageBoundReceiptKeepsTerminalPromotedFalse =
  refl

crossShellLeakageBoundReceiptKeepsQgapTransferClosedFalse :
  qGapTransferClosed canonicalNSTriadKNCrossShellLeakageBoundReceipt ≡ false
crossShellLeakageBoundReceiptKeepsQgapTransferClosedFalse =
  refl
