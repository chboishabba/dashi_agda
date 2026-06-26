module DASHI.Physics.Closure.NSTriadKNMixedTailSchurScalingReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Candidate-only mixed-tail Schur scaling receipt.
--
-- This module records the corrected N=6,8,10,12 top-tail sparse-Schur
-- telemetry as a DASHI receipt.  It is deliberately non-promoting:
-- the fitted laws and candidate lemma names are evidence targets, not
-- theorem authority, not a full Navier-Stokes proof, and not a Clay claim.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSTriadKNMixedTailSchurScalingStatus : Set where
  mixedTailSchurScalingCandidateRecorded :
    NSTriadKNMixedTailSchurScalingStatus

data NSTriadKNMixedTailSchurScalingRow : Set where
  shell6K5Eta025TopTailSparseSchurRow :
    NSTriadKNMixedTailSchurScalingRow
  shell8K7Eta025TopTailSparseSchurRow :
    NSTriadKNMixedTailSchurScalingRow
  shell10K9Eta025TopTailSparseSchurRow :
    NSTriadKNMixedTailSchurScalingRow
  shell12K11Eta025TopTailSparseSchurRow :
    NSTriadKNMixedTailSchurScalingRow

canonicalNSTriadKNMixedTailSchurScalingRows :
  List NSTriadKNMixedTailSchurScalingRow
canonicalNSTriadKNMixedTailSchurScalingRows =
  shell6K5Eta025TopTailSparseSchurRow
  ∷ shell8K7Eta025TopTailSparseSchurRow
  ∷ shell10K9Eta025TopTailSparseSchurRow
  ∷ shell12K11Eta025TopTailSparseSchurRow
  ∷ []

nSTriadKNMixedTailSchurScalingRowCount : Nat
nSTriadKNMixedTailSchurScalingRowCount =
  listLength canonicalNSTriadKNMixedTailSchurScalingRows

nSTriadKNMixedTailSchurScalingRowCountIs4 :
  nSTriadKNMixedTailSchurScalingRowCount ≡ 4
nSTriadKNMixedTailSchurScalingRowCountIs4 = refl

data NSTriadKNMixedTailSchurScalingFit : Set where
  qGapVsNFitRecorded :
    NSTriadKNMixedTailSchurScalingFit
  dVsNFitRecorded :
    NSTriadKNMixedTailSchurScalingFit
  qGapVsDFitRecorded :
    NSTriadKNMixedTailSchurScalingFit
  dTimesQGapProductStabilityRecorded :
    NSTriadKNMixedTailSchurScalingFit
  nSquaredQGapProductStabilityRecorded :
    NSTriadKNMixedTailSchurScalingFit

canonicalNSTriadKNMixedTailSchurScalingFits :
  List NSTriadKNMixedTailSchurScalingFit
canonicalNSTriadKNMixedTailSchurScalingFits =
  qGapVsNFitRecorded
  ∷ dVsNFitRecorded
  ∷ qGapVsDFitRecorded
  ∷ dTimesQGapProductStabilityRecorded
  ∷ nSquaredQGapProductStabilityRecorded
  ∷ []

nSTriadKNMixedTailSchurScalingFitCount : Nat
nSTriadKNMixedTailSchurScalingFitCount =
  listLength canonicalNSTriadKNMixedTailSchurScalingFits

nSTriadKNMixedTailSchurScalingFitCountIs5 :
  nSTriadKNMixedTailSchurScalingFitCount ≡ 5
nSTriadKNMixedTailSchurScalingFitCountIs5 = refl

data NSTriadKNMixedTailSchurScalingCandidateLemma : Set where
  tailSubspaceCoercivityCandidate :
    NSTriadKNMixedTailSchurScalingCandidateLemma
  mixedTailSchurGapDissipationScaleCandidate :
    NSTriadKNMixedTailSchurScalingCandidateLemma
  finiteAnchorMixedTailRepairCandidate :
    NSTriadKNMixedTailSchurScalingCandidateLemma
  coherenceProjectionSmallnessCandidate :
    NSTriadKNMixedTailSchurScalingCandidateLemma
  residenceTimeExclusionCandidate :
    NSTriadKNMixedTailSchurScalingCandidateLemma

canonicalNSTriadKNMixedTailSchurScalingCandidateLemmas :
  List NSTriadKNMixedTailSchurScalingCandidateLemma
canonicalNSTriadKNMixedTailSchurScalingCandidateLemmas =
  tailSubspaceCoercivityCandidate
  ∷ mixedTailSchurGapDissipationScaleCandidate
  ∷ finiteAnchorMixedTailRepairCandidate
  ∷ coherenceProjectionSmallnessCandidate
  ∷ residenceTimeExclusionCandidate
  ∷ []

data NSTriadKNMixedTailSchurScalingOpenGap : Set where
  analyticQGapLowerBoundOpen :
    NSTriadKNMixedTailSchurScalingOpenGap
  uniformTailSubspaceCoercivityOpen :
    NSTriadKNMixedTailSchurScalingOpenGap
  structuralBKMProjectionSmallnessOpen :
    NSTriadKNMixedTailSchurScalingOpenGap
  finiteDimensionalToPDETrajectoryBridgeOpen :
    NSTriadKNMixedTailSchurScalingOpenGap
  bkmResidenceAssemblyOpen :
    NSTriadKNMixedTailSchurScalingOpenGap
  noTheoremFullNSOrClayPromotion :
    NSTriadKNMixedTailSchurScalingOpenGap

canonicalNSTriadKNMixedTailSchurScalingOpenGaps :
  List NSTriadKNMixedTailSchurScalingOpenGap
canonicalNSTriadKNMixedTailSchurScalingOpenGaps =
  analyticQGapLowerBoundOpen
  ∷ uniformTailSubspaceCoercivityOpen
  ∷ structuralBKMProjectionSmallnessOpen
  ∷ finiteDimensionalToPDETrajectoryBridgeOpen
  ∷ bkmResidenceAssemblyOpen
  ∷ noTheoremFullNSOrClayPromotion
  ∷ []

nSTriadKNMixedTailSchurScalingOpenGapCount : Nat
nSTriadKNMixedTailSchurScalingOpenGapCount =
  listLength canonicalNSTriadKNMixedTailSchurScalingOpenGaps

nSTriadKNMixedTailSchurScalingOpenGapCountIs6 :
  nSTriadKNMixedTailSchurScalingOpenGapCount ≡ 6
nSTriadKNMixedTailSchurScalingOpenGapCountIs6 = refl

data NSTriadKNMixedTailSchurScalingPromotion : Set where

promotionImpossibleHere :
  NSTriadKNMixedTailSchurScalingPromotion → ⊥
promotionImpossibleHere ()

canonicalReceiptText : String
canonicalReceiptText =
  "Candidate-only NS triad K_N mixed-tail sparse-Schur scaling receipt for top-tail forced rows N=6,8,10,12."

canonicalEvidenceTableText : String
canonicalEvidenceTableText =
  "Observed rows: R_tail remains above c0, q_gap remains positive, q_gap fits N^-2.198, D fits N^1.985, and D*q_gap is approximately stable."

canonicalCorrectedBKMProjectionText : String
canonicalCorrectedBKMProjectionText =
  "BKM-tail projection squared remains tiny across N=6,8,10,12 and drops sharply by N=12; it is not recorded as monotone because N=8 exceeds N=6."

canonicalCorrectedCrossTermText : String
canonicalCorrectedCrossTermText =
  "cross-L_neg fraction is remarkably stable in the forced-tail family, but this receipt does not promote that stability to a structural theorem."

canonicalCandidateLemmaText : String
canonicalCandidateLemmaText =
  "MixedTailSchurGapDissipationScale candidate: q_gap(N) * D(N) >= c_mix > 0, with sampled floor about 3.9e-3 only on the four recorded rows."

canonicalFitArtifactJSON : String
canonicalFitArtifactJSON =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_sparse_schur_scaling_fit_20260624/summary.json"

canonicalFitArtifactMarkdown : String
canonicalFitArtifactMarkdown =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_sparse_schur_scaling_fit_20260624/summary.md"

canonicalSourceSummaryN6N10 : String
canonicalSourceSummaryN6N10 =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_sparse_schur_scaling_20260624/summary.json"

canonicalSourceSummaryN12 : String
canonicalSourceSummaryN12 =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_sparse_schur_scaling_shell12_20260624/summary.json"

canonicalOText : String
canonicalOText =
  "O: record the mixed-tail sparse-Schur scaling telemetry as a candidate-only DASHI receipt."

canonicalRText : String
canonicalRText =
  "R: keep the corrected N=6,8,10,12 read: tail-only coercivity survives, q_gap is positive, q_gap scales near D^-1, and promotion remains blocked."

canonicalCText : String
canonicalCText =
  "C: export sampled rows, fitted laws, candidate lemma names, corrected cautions, artifact paths, open gaps, and false promotion flags."

canonicalSText : String
canonicalSText =
  "S: finite-shell telemetry only; no theorem authority, no full-NS promotion, and no Clay promotion."

canonicalLText : String
canonicalLText =
  "L: R_full<c0 mixed-tail row -> R_tail>c0 and q_gap>0 telemetry -> q_gap*D candidate scale -> open analytic/PDE bridge."

canonicalPText : String
canonicalPText =
  "P: target q_gap(N) >= N^-2-epsilon with D(N) near N^2, then connect mixed-tail repair to coherence projection and residence."

canonicalGText : String
canonicalGText =
  "G: chart language must say tiny BKM-tail projection, not monotone projection decay; stable cross-L_neg is forced-tail telemetry, not a theorem."

canonicalFText : String
canonicalFText =
  "F: missing proofs are analytic q_gap lower bound, uniform tail coercivity, structural BKM projection smallness, PDE trajectory bridge, and BKM residence assembly."

record NSTriadKNMixedTailSchurScalingORCSLPGF : Set where
  constructor mkNSTriadKNMixedTailSchurScalingORCSLPGF
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

canonicalNSTriadKNMixedTailSchurScalingORCSLPGF :
  NSTriadKNMixedTailSchurScalingORCSLPGF
canonicalNSTriadKNMixedTailSchurScalingORCSLPGF =
  mkNSTriadKNMixedTailSchurScalingORCSLPGF
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

record NSTriadKNMixedTailSchurScalingReceipt : Setω where
  constructor mkNSTriadKNMixedTailSchurScalingReceipt
  field
    receiptName :
      String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNMixedTailSchurScalingReceipt"

    status :
      NSTriadKNMixedTailSchurScalingStatus
    statusIsCanonical :
      status ≡ mixedTailSchurScalingCandidateRecorded

    receiptText :
      String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    evidenceTableText :
      String
    evidenceTableTextIsCanonical :
      evidenceTableText ≡ canonicalEvidenceTableText

    correctedBKMProjectionText :
      String
    correctedBKMProjectionTextIsCanonical :
      correctedBKMProjectionText ≡ canonicalCorrectedBKMProjectionText

    correctedCrossTermText :
      String
    correctedCrossTermTextIsCanonical :
      correctedCrossTermText ≡ canonicalCorrectedCrossTermText

    candidateLemmaText :
      String
    candidateLemmaTextIsCanonical :
      candidateLemmaText ≡ canonicalCandidateLemmaText

    rows :
      List NSTriadKNMixedTailSchurScalingRow
    rowsAreCanonical :
      rows ≡ canonicalNSTriadKNMixedTailSchurScalingRows

    fits :
      List NSTriadKNMixedTailSchurScalingFit
    fitsAreCanonical :
      fits ≡ canonicalNSTriadKNMixedTailSchurScalingFits

    candidateLemmas :
      List NSTriadKNMixedTailSchurScalingCandidateLemma
    candidateLemmasAreCanonical :
      candidateLemmas ≡ canonicalNSTriadKNMixedTailSchurScalingCandidateLemmas

    openGaps :
      List NSTriadKNMixedTailSchurScalingOpenGap
    openGapsAreCanonical :
      openGaps ≡ canonicalNSTriadKNMixedTailSchurScalingOpenGaps

    fitArtifactJSON :
      String
    fitArtifactJSONIsCanonical :
      fitArtifactJSON ≡ canonicalFitArtifactJSON

    fitArtifactMarkdown :
      String
    fitArtifactMarkdownIsCanonical :
      fitArtifactMarkdown ≡ canonicalFitArtifactMarkdown

    sourceSummaryN6N10 :
      String
    sourceSummaryN6N10IsCanonical :
      sourceSummaryN6N10 ≡ canonicalSourceSummaryN6N10

    sourceSummaryN12 :
      String
    sourceSummaryN12IsCanonical :
      sourceSummaryN12 ≡ canonicalSourceSummaryN12

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

    promotionFlags :
      List NSTriadKNMixedTailSchurScalingPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    orcslpgf :
      NSTriadKNMixedTailSchurScalingORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadKNMixedTailSchurScalingORCSLPGF

open NSTriadKNMixedTailSchurScalingReceipt public

canonicalNSTriadKNMixedTailSchurScalingReceipt :
  NSTriadKNMixedTailSchurScalingReceipt
canonicalNSTriadKNMixedTailSchurScalingReceipt =
  mkNSTriadKNMixedTailSchurScalingReceipt
    "NSTriadKNMixedTailSchurScalingReceipt"
    refl
    mixedTailSchurScalingCandidateRecorded
    refl
    canonicalReceiptText
    refl
    canonicalEvidenceTableText
    refl
    canonicalCorrectedBKMProjectionText
    refl
    canonicalCorrectedCrossTermText
    refl
    canonicalCandidateLemmaText
    refl
    canonicalNSTriadKNMixedTailSchurScalingRows
    refl
    canonicalNSTriadKNMixedTailSchurScalingFits
    refl
    canonicalNSTriadKNMixedTailSchurScalingCandidateLemmas
    refl
    canonicalNSTriadKNMixedTailSchurScalingOpenGaps
    refl
    canonicalFitArtifactJSON
    refl
    canonicalFitArtifactMarkdown
    refl
    canonicalSourceSummaryN6N10
    refl
    canonicalSourceSummaryN12
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
    []
    refl
    canonicalNSTriadKNMixedTailSchurScalingORCSLPGF
    refl

mixedTailSchurScalingReceiptKeepsTheoremPromotedFalse :
  theoremPromoted canonicalNSTriadKNMixedTailSchurScalingReceipt ≡ false
mixedTailSchurScalingReceiptKeepsTheoremPromotedFalse =
  refl

mixedTailSchurScalingReceiptKeepsFullNSPromotedFalse :
  fullNSPromoted canonicalNSTriadKNMixedTailSchurScalingReceipt ≡ false
mixedTailSchurScalingReceiptKeepsFullNSPromotedFalse =
  refl

mixedTailSchurScalingReceiptKeepsClayPromotedFalse :
  clayPromoted canonicalNSTriadKNMixedTailSchurScalingReceipt ≡ false
mixedTailSchurScalingReceiptKeepsClayPromotedFalse =
  refl

mixedTailSchurScalingReceiptKeepsTerminalPromotedFalse :
  terminalPromoted canonicalNSTriadKNMixedTailSchurScalingReceipt ≡ false
mixedTailSchurScalingReceiptKeepsTerminalPromotedFalse =
  refl
