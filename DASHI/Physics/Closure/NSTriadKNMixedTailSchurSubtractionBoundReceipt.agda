module DASHI.Physics.Closure.NSTriadKNMixedTailSchurSubtractionBoundReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSTriadKNMixedTailSchurGapAnatomyReceipt as Anatomy

------------------------------------------------------------------------
-- Candidate-only finite-shell Schur subtraction bound receipt.
--
-- This module records the next bridge question after the anatomy report:
-- whether the small normalized Schur gap is controlled by a structural
-- subtraction bound or merely observed as a stable residue.  It is not a
-- theorem, not a full-NS promotion, not a BKM exclusion proof, and not a
-- Clay claim.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSTriadKNMixedTailSchurSubtractionBoundStatus : Set where
  mixedTailSchurSubtractionBoundRecorded :
    NSTriadKNMixedTailSchurSubtractionBoundStatus

data NSTriadKNMixedTailSchurSubtractionBoundRow : Set where
  shell6K5Eta025SchurSubtractionBoundRow :
    NSTriadKNMixedTailSchurSubtractionBoundRow
  shell8K7Eta025SchurSubtractionBoundRow :
    NSTriadKNMixedTailSchurSubtractionBoundRow
  shell10K9Eta025SchurSubtractionBoundRow :
    NSTriadKNMixedTailSchurSubtractionBoundRow
  shell12K11Eta025SchurSubtractionBoundRow :
    NSTriadKNMixedTailSchurSubtractionBoundRow

canonicalNSTriadKNMixedTailSchurSubtractionBoundRows :
  List NSTriadKNMixedTailSchurSubtractionBoundRow
canonicalNSTriadKNMixedTailSchurSubtractionBoundRows =
  shell6K5Eta025SchurSubtractionBoundRow
  ∷ shell8K7Eta025SchurSubtractionBoundRow
  ∷ shell10K9Eta025SchurSubtractionBoundRow
  ∷ shell12K11Eta025SchurSubtractionBoundRow
  ∷ []

nSTriadKNMixedTailSchurSubtractionBoundRowCount : Nat
nSTriadKNMixedTailSchurSubtractionBoundRowCount =
  listLength canonicalNSTriadKNMixedTailSchurSubtractionBoundRows

nSTriadKNMixedTailSchurSubtractionBoundRowCountIs4 :
  nSTriadKNMixedTailSchurSubtractionBoundRowCount ≡ 4
nSTriadKNMixedTailSchurSubtractionBoundRowCountIs4 = refl

data NSTriadKNMixedTailSchurSubtractionBoundMetric : Set where
  qDiagRecorded :
    NSTriadKNMixedTailSchurSubtractionBoundMetric
  qSchurRecorded :
    NSTriadKNMixedTailSchurSubtractionBoundMetric
  qSchurSubtractionRecorded :
    NSTriadKNMixedTailSchurSubtractionBoundMetric
  qGapRecorded :
    NSTriadKNMixedTailSchurSubtractionBoundMetric
  qGapOverQDiagRecorded :
    NSTriadKNMixedTailSchurSubtractionBoundMetric
  qSchurSubtractionOverQDiagRecorded :
    NSTriadKNMixedTailSchurSubtractionBoundMetric
  dissipationGapProductRecorded :
    NSTriadKNMixedTailSchurSubtractionBoundMetric
  nSquaredQGapProductRecorded :
    NSTriadKNMixedTailSchurSubtractionBoundMetric
  tailRayleighAndBkmTelemetryRecorded :
    NSTriadKNMixedTailSchurSubtractionBoundMetric

canonicalNSTriadKNMixedTailSchurSubtractionBoundMetrics :
  List NSTriadKNMixedTailSchurSubtractionBoundMetric
canonicalNSTriadKNMixedTailSchurSubtractionBoundMetrics =
  qDiagRecorded
  ∷ qSchurRecorded
  ∷ qSchurSubtractionRecorded
  ∷ qGapRecorded
  ∷ qGapOverQDiagRecorded
  ∷ qSchurSubtractionOverQDiagRecorded
  ∷ dissipationGapProductRecorded
  ∷ nSquaredQGapProductRecorded
  ∷ tailRayleighAndBkmTelemetryRecorded
  ∷ []

nSTriadKNMixedTailSchurSubtractionBoundMetricCount : Nat
nSTriadKNMixedTailSchurSubtractionBoundMetricCount =
  listLength canonicalNSTriadKNMixedTailSchurSubtractionBoundMetrics

nSTriadKNMixedTailSchurSubtractionBoundMetricCountIs9 :
  nSTriadKNMixedTailSchurSubtractionBoundMetricCount ≡ 9
nSTriadKNMixedTailSchurSubtractionBoundMetricCountIs9 = refl

data NSTriadKNMixedTailSchurSubtractionBoundCandidateLemma : Set where
  tailDiagonalStableCandidate :
    NSTriadKNMixedTailSchurSubtractionBoundCandidateLemma
  schurSubtractionSmallCandidate :
    NSTriadKNMixedTailSchurSubtractionBoundCandidateLemma
  schurGapSecondOrderResidueCandidate :
    NSTriadKNMixedTailSchurSubtractionBoundCandidateLemma
  dissipationScaledSchurGapCandidate :
    NSTriadKNMixedTailSchurSubtractionBoundCandidateLemma

canonicalNSTriadKNMixedTailSchurSubtractionBoundCandidateLemmas :
  List NSTriadKNMixedTailSchurSubtractionBoundCandidateLemma
canonicalNSTriadKNMixedTailSchurSubtractionBoundCandidateLemmas =
  tailDiagonalStableCandidate
  ∷ schurSubtractionSmallCandidate
  ∷ schurGapSecondOrderResidueCandidate
  ∷ dissipationScaledSchurGapCandidate
  ∷ []

nSTriadKNMixedTailSchurSubtractionBoundCandidateLemmaCount : Nat
nSTriadKNMixedTailSchurSubtractionBoundCandidateLemmaCount =
  listLength canonicalNSTriadKNMixedTailSchurSubtractionBoundCandidateLemmas

nSTriadKNMixedTailSchurSubtractionBoundCandidateLemmaCountIs4 :
  nSTriadKNMixedTailSchurSubtractionBoundCandidateLemmaCount ≡ 4
nSTriadKNMixedTailSchurSubtractionBoundCandidateLemmaCountIs4 = refl

data NSTriadKNMixedTailSchurSubtractionBoundOpenGap : Set where
  tailDiagonalUniformityOpen :
    NSTriadKNMixedTailSchurSubtractionBoundOpenGap
  schurSubtractionBoundOpen :
    NSTriadKNMixedTailSchurSubtractionBoundOpenGap
  geometricResidueInterpretationOpen :
    NSTriadKNMixedTailSchurSubtractionBoundOpenGap
  dissipationScaleBridgeOpen :
    NSTriadKNMixedTailSchurSubtractionBoundOpenGap
  noTheoremFullNSOrClayPromotion :
    NSTriadKNMixedTailSchurSubtractionBoundOpenGap

canonicalNSTriadKNMixedTailSchurSubtractionBoundOpenGaps :
  List NSTriadKNMixedTailSchurSubtractionBoundOpenGap
canonicalNSTriadKNMixedTailSchurSubtractionBoundOpenGaps =
  tailDiagonalUniformityOpen
  ∷ schurSubtractionBoundOpen
  ∷ geometricResidueInterpretationOpen
  ∷ dissipationScaleBridgeOpen
  ∷ noTheoremFullNSOrClayPromotion
  ∷ []

nSTriadKNMixedTailSchurSubtractionBoundOpenGapCount : Nat
nSTriadKNMixedTailSchurSubtractionBoundOpenGapCount =
  listLength canonicalNSTriadKNMixedTailSchurSubtractionBoundOpenGaps

nSTriadKNMixedTailSchurSubtractionBoundOpenGapCountIs5 :
  nSTriadKNMixedTailSchurSubtractionBoundOpenGapCount ≡ 5
nSTriadKNMixedTailSchurSubtractionBoundOpenGapCountIs5 = refl

data NSTriadKNMixedTailSchurSubtractionBoundPromotion : Set where

promotionImpossibleHere :
  NSTriadKNMixedTailSchurSubtractionBoundPromotion → ⊥
promotionImpossibleHere ()

canonicalReceiptText : String
canonicalReceiptText =
  "Candidate-only finite-shell Schur subtraction bound receipt for the N=6,8,10,12 forced-tail rows with K=N-1 and eta=0.25."

canonicalReadoutText : String
canonicalReadoutText =
  "The anatomy report says the tail block stays O(10^-2), q_schur_subtraction/q_diag stays around 0.3%, q_gap is positive and roughly N^-2.2, and D*q_gap is approximately stable; this receipt records that the next analytic target is to prove the subtraction bound structurally."

canonicalSourceAnatomyArtifactJSON : String
canonicalSourceAnatomyArtifactJSON = Anatomy.canonicalAnatomyArtifactJSON

canonicalSourceAnatomyArtifactMarkdown : String
canonicalSourceAnatomyArtifactMarkdown = Anatomy.canonicalAnatomyArtifactMarkdown

canonicalSourceProofObligationMapText : String
canonicalSourceProofObligationMapText =
  "DASHI/Physics/Closure/NSTriadKNMixedTailProofObligationMapReceipt.agda"

canonicalBoundArtifactJSON : String
canonicalBoundArtifactJSON =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_schur_subtraction_bound_20260624/summary.json"

canonicalBoundArtifactMarkdown : String
canonicalBoundArtifactMarkdown =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_schur_subtraction_bound_20260624/summary.md"

canonicalOText : String
canonicalOText =
  "O: record the Schur-subtraction bound bridge as a candidate-only finite-shell receipt."

canonicalRText : String
canonicalRText =
  "R: determine whether the observed small q_gap is a stable second-order residue or demands a structural subtraction estimate."

canonicalCText : String
canonicalCText =
  "C: export the same mixed-tail shells, q_diag, q_schur, q_schur_subtraction, q_gap, both q_gap ratios, D*q_gap, N^2*q_gap, R_tail, cross-L_neg fraction, and BKM-tail projection squared."

canonicalSText : String
canonicalSText =
  "S: finite-shell telemetry only; no theorem authority, no full-NS promotion, no BKM exclusion proof, and no Clay promotion."

canonicalLText : String
canonicalLText =
  "L: anatomy report -> Schur subtraction bound target -> analytic and PDE bridges still open."

canonicalPText : String
canonicalPText =
  "P: prove a subtraction bound or structural lower bound on the residual q_gap, then combine it with the N^2 dissipation scale."

canonicalGText : String
canonicalGText =
  "G: keep the candidate-only posture; the sampled rows support the target but do not discharge it."

canonicalFText : String
canonicalFText =
  "F: the open gap is the analytic bridge from stable tail geometry and small Schur subtraction to a theorem-shaped q_gap lower bound."

record NSTriadKNMixedTailSchurSubtractionBoundORCSLPGF : Set where
  constructor mkNSTriadKNMixedTailSchurSubtractionBoundORCSLPGF
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

canonicalNSTriadKNMixedTailSchurSubtractionBoundORCSLPGF :
  NSTriadKNMixedTailSchurSubtractionBoundORCSLPGF
canonicalNSTriadKNMixedTailSchurSubtractionBoundORCSLPGF =
  mkNSTriadKNMixedTailSchurSubtractionBoundORCSLPGF
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

record NSTriadKNMixedTailSchurSubtractionBoundReceipt : Setω where
  constructor mkNSTriadKNMixedTailSchurSubtractionBoundReceipt
  field
    receiptName :
      String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNMixedTailSchurSubtractionBoundReceipt"

    status :
      NSTriadKNMixedTailSchurSubtractionBoundStatus
    statusIsCanonical :
      status ≡ mixedTailSchurSubtractionBoundRecorded

    receiptText :
      String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    readoutText :
      String
    readoutTextIsCanonical :
      readoutText ≡ canonicalReadoutText

    sourceAnatomyArtifactJSON :
      String
    sourceAnatomyArtifactJSONIsCanonical :
      sourceAnatomyArtifactJSON ≡ canonicalSourceAnatomyArtifactJSON

    sourceAnatomyArtifactMarkdown :
      String
    sourceAnatomyArtifactMarkdownIsCanonical :
      sourceAnatomyArtifactMarkdown ≡ canonicalSourceAnatomyArtifactMarkdown

    sourceProofObligationMapText :
      String
    sourceProofObligationMapTextIsCanonical :
      sourceProofObligationMapText ≡ canonicalSourceProofObligationMapText

    boundArtifactJSON :
      String
    boundArtifactJSONIsCanonical :
      boundArtifactJSON ≡ canonicalBoundArtifactJSON

    boundArtifactMarkdown :
      String
    boundArtifactMarkdownIsCanonical :
      boundArtifactMarkdown ≡ canonicalBoundArtifactMarkdown

    rows :
      List NSTriadKNMixedTailSchurSubtractionBoundRow
    rowsAreCanonical :
      rows ≡ canonicalNSTriadKNMixedTailSchurSubtractionBoundRows

    metrics :
      List NSTriadKNMixedTailSchurSubtractionBoundMetric
    metricsAreCanonical :
      metrics ≡ canonicalNSTriadKNMixedTailSchurSubtractionBoundMetrics

    candidateLemmas :
      List NSTriadKNMixedTailSchurSubtractionBoundCandidateLemma
    candidateLemmasAreCanonical :
      candidateLemmas ≡ canonicalNSTriadKNMixedTailSchurSubtractionBoundCandidateLemmas

    openGaps :
      List NSTriadKNMixedTailSchurSubtractionBoundOpenGap
    openGapsAreCanonical :
      openGaps ≡ canonicalNSTriadKNMixedTailSchurSubtractionBoundOpenGaps

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

    bkmExclusionProved :
      Bool
    bkmExclusionProvedIsFalse :
      bkmExclusionProved ≡ false

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

    terminalPromoted :
      Bool
    terminalPromotedIsFalse :
      terminalPromoted ≡ false

    promotionFlags :
      List NSTriadKNMixedTailSchurSubtractionBoundPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    orcslpgf :
      NSTriadKNMixedTailSchurSubtractionBoundORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadKNMixedTailSchurSubtractionBoundORCSLPGF

open NSTriadKNMixedTailSchurSubtractionBoundReceipt public

canonicalNSTriadKNMixedTailSchurSubtractionBoundReceipt :
  NSTriadKNMixedTailSchurSubtractionBoundReceipt
canonicalNSTriadKNMixedTailSchurSubtractionBoundReceipt =
  mkNSTriadKNMixedTailSchurSubtractionBoundReceipt
    "NSTriadKNMixedTailSchurSubtractionBoundReceipt"
    refl
    mixedTailSchurSubtractionBoundRecorded
    refl
    canonicalReceiptText
    refl
    canonicalReadoutText
    refl
    canonicalSourceAnatomyArtifactJSON
    refl
    canonicalSourceAnatomyArtifactMarkdown
    refl
    canonicalSourceProofObligationMapText
    refl
    canonicalBoundArtifactJSON
    refl
    canonicalBoundArtifactMarkdown
    refl
    canonicalNSTriadKNMixedTailSchurSubtractionBoundRows
    refl
    canonicalNSTriadKNMixedTailSchurSubtractionBoundMetrics
    refl
    canonicalNSTriadKNMixedTailSchurSubtractionBoundCandidateLemmas
    refl
    canonicalNSTriadKNMixedTailSchurSubtractionBoundOpenGaps
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
    canonicalNSTriadKNMixedTailSchurSubtractionBoundORCSLPGF
    refl

schurSubtractionBoundKeepsTheoremPromotedFalse :
  theoremPromoted canonicalNSTriadKNMixedTailSchurSubtractionBoundReceipt ≡ false
schurSubtractionBoundKeepsTheoremPromotedFalse = refl

schurSubtractionBoundKeepsFullNSPromotedFalse :
  fullNSPromoted canonicalNSTriadKNMixedTailSchurSubtractionBoundReceipt ≡ false
schurSubtractionBoundKeepsFullNSPromotedFalse = refl

schurSubtractionBoundKeepsBKMExclusionFalse :
  bkmExclusionProved canonicalNSTriadKNMixedTailSchurSubtractionBoundReceipt ≡ false
schurSubtractionBoundKeepsBKMExclusionFalse = refl

schurSubtractionBoundKeepsClayPromotedFalse :
  clayPromoted canonicalNSTriadKNMixedTailSchurSubtractionBoundReceipt ≡ false
schurSubtractionBoundKeepsClayPromotedFalse = refl

schurSubtractionBoundKeepsTerminalPromotedFalse :
  terminalPromoted canonicalNSTriadKNMixedTailSchurSubtractionBoundReceipt ≡ false
schurSubtractionBoundKeepsTerminalPromotedFalse = refl
