module DASHI.Physics.Closure.NSTriadKNMixedTailSchurGapAnatomyReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSTriadKNMixedTailSchurScalingReceipt as Scaling
import DASHI.Physics.Closure.NSTriadKNMixedTailProofObligationMapReceipt as Obligations

------------------------------------------------------------------------
-- Candidate-only finite-shell Schur-gap anatomy receipt.
--
-- This module records the live readout requested for the N=6,8,10,12
-- forced-tail rows with K=N-1 and eta=0.25.  It is deliberately non-
-- promoting: the diagnostic readout is evidence, not theorem authority,
-- not full-NS promotion, not BKM exclusion, and not a Clay claim.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSTriadKNMixedTailSchurGapAnatomyStatus : Set where
  mixedTailSchurGapAnatomyRecorded :
    NSTriadKNMixedTailSchurGapAnatomyStatus

data NSTriadKNMixedTailSchurGapAnatomyRow : Set where
  shell6K5Eta025AnatomyRow :
    NSTriadKNMixedTailSchurGapAnatomyRow
  shell8K7Eta025AnatomyRow :
    NSTriadKNMixedTailSchurGapAnatomyRow
  shell10K9Eta025AnatomyRow :
    NSTriadKNMixedTailSchurGapAnatomyRow
  shell12K11Eta025AnatomyRow :
    NSTriadKNMixedTailSchurGapAnatomyRow

canonicalNSTriadKNMixedTailSchurGapAnatomyRows :
  List NSTriadKNMixedTailSchurGapAnatomyRow
canonicalNSTriadKNMixedTailSchurGapAnatomyRows =
  shell6K5Eta025AnatomyRow
  ∷ shell8K7Eta025AnatomyRow
  ∷ shell10K9Eta025AnatomyRow
  ∷ shell12K11Eta025AnatomyRow
  ∷ []

nSTriadKNMixedTailSchurGapAnatomyRowCount : Nat
nSTriadKNMixedTailSchurGapAnatomyRowCount =
  listLength canonicalNSTriadKNMixedTailSchurGapAnatomyRows

nSTriadKNMixedTailSchurGapAnatomyRowCountIs4 :
  nSTriadKNMixedTailSchurGapAnatomyRowCount ≡ 4
nSTriadKNMixedTailSchurGapAnatomyRowCountIs4 = refl

data NSTriadKNMixedTailSchurGapAnatomyMetric : Set where
  qDiagRecorded :
    NSTriadKNMixedTailSchurGapAnatomyMetric
  qSchurRecorded :
    NSTriadKNMixedTailSchurGapAnatomyMetric
  qSchurSubtractionRecorded :
    NSTriadKNMixedTailSchurGapAnatomyMetric
  qGapRecorded :
    NSTriadKNMixedTailSchurGapAnatomyMetric
  qGapOverQDiagRecorded :
    NSTriadKNMixedTailSchurGapAnatomyMetric
  qSchurSubtractionOverQDiagRecorded :
    NSTriadKNMixedTailSchurGapAnatomyMetric
  dissipationGapProductRecorded :
    NSTriadKNMixedTailSchurGapAnatomyMetric
  nSquaredQGapProductRecorded :
    NSTriadKNMixedTailSchurGapAnatomyMetric
  tailRayleighAndBkmTelemetryRecorded :
    NSTriadKNMixedTailSchurGapAnatomyMetric

canonicalNSTriadKNMixedTailSchurGapAnatomyMetrics :
  List NSTriadKNMixedTailSchurGapAnatomyMetric
canonicalNSTriadKNMixedTailSchurGapAnatomyMetrics =
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

nSTriadKNMixedTailSchurGapAnatomyMetricCount : Nat
nSTriadKNMixedTailSchurGapAnatomyMetricCount =
  listLength canonicalNSTriadKNMixedTailSchurGapAnatomyMetrics

nSTriadKNMixedTailSchurGapAnatomyMetricCountIs9 :
  nSTriadKNMixedTailSchurGapAnatomyMetricCount ≡ 9
nSTriadKNMixedTailSchurGapAnatomyMetricCountIs9 = refl

data NSTriadKNMixedTailSchurGapAnatomyOpenGap : Set where
  secondOrderSchurResidueInterpretationOpen :
    NSTriadKNMixedTailSchurGapAnatomyOpenGap
  directTailCoercivityCollapseOpen :
    NSTriadKNMixedTailSchurGapAnatomyOpenGap
  asymptoticRepairStabilityOpen :
    NSTriadKNMixedTailSchurGapAnatomyOpenGap
  bkmProjectionBridgeOpen :
    NSTriadKNMixedTailSchurGapAnatomyOpenGap
  noTheoremFullNSOrClayPromotion :
    NSTriadKNMixedTailSchurGapAnatomyOpenGap

canonicalNSTriadKNMixedTailSchurGapAnatomyOpenGaps :
  List NSTriadKNMixedTailSchurGapAnatomyOpenGap
canonicalNSTriadKNMixedTailSchurGapAnatomyOpenGaps =
  secondOrderSchurResidueInterpretationOpen
  ∷ directTailCoercivityCollapseOpen
  ∷ asymptoticRepairStabilityOpen
  ∷ bkmProjectionBridgeOpen
  ∷ noTheoremFullNSOrClayPromotion
  ∷ []

nSTriadKNMixedTailSchurGapAnatomyOpenGapCount : Nat
nSTriadKNMixedTailSchurGapAnatomyOpenGapCount =
  listLength canonicalNSTriadKNMixedTailSchurGapAnatomyOpenGaps

nSTriadKNMixedTailSchurGapAnatomyOpenGapCountIs5 :
  nSTriadKNMixedTailSchurGapAnatomyOpenGapCount ≡ 5
nSTriadKNMixedTailSchurGapAnatomyOpenGapCountIs5 = refl

data NSTriadKNMixedTailSchurGapAnatomyPromotion : Set where

promotionImpossibleHere :
  NSTriadKNMixedTailSchurGapAnatomyPromotion → ⊥
promotionImpossibleHere ()

canonicalReceiptText : String
canonicalReceiptText =
  "Candidate-only finite-shell Schur-gap anatomy receipt for the N=6,8,10,12 forced-tail rows with K=N-1 and eta=0.25."

canonicalReadoutText : String
canonicalReadoutText =
  "The readout favors a second-order Schur residue: q_diag and q_schur stay on the sampled 10^-2 scale, q_gap is much smaller and tracks the parent N^-2.2 fit, q_schur_subtraction/q_diag stays around 0.2%-0.3%, and the subtraction is small rather than catastrophic."

canonicalSourceFitSummaryText : String
canonicalSourceFitSummaryText =
  Scaling.canonicalFitArtifactJSON

canonicalSourceProofObligationMapText : String
canonicalSourceProofObligationMapText =
  "DASHI/Physics/Closure/NSTriadKNMixedTailProofObligationMapReceipt.agda"

canonicalAnatomyArtifactJSON : String
canonicalAnatomyArtifactJSON =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_schur_gap_anatomy_20260624/summary.json"

canonicalAnatomyArtifactMarkdown : String
canonicalAnatomyArtifactMarkdown =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_schur_gap_anatomy_20260624/summary.md"

canonicalOText : String
canonicalOText =
  "O: record the Schur-gap anatomy readout as a candidate-only finite-shell receipt."

canonicalRText : String
canonicalRText =
  "R: decide whether q_gap ~ N^-2 looks geometric or like a small Schur subtraction residue."

canonicalCText : String
canonicalCText =
  "C: export q_diag, q_schur, q_schur_subtraction, q_gap, the two ratios against q_diag, D*q_gap, N²*q_gap, R_tail, cross-L_neg fraction, and BKM-tail projection squared."

canonicalSText : String
canonicalSText =
  "S: this is a finite-shell report only; no theorem authority, no full-NS promotion, no BKM exclusion proof, and no Clay promotion are claimed."

canonicalLText : String
canonicalLText =
  "L: fit summary -> anatomy report -> small Schur residue interpretation -> remaining analytic bridges."

canonicalPText : String
canonicalPText =
  "P: use the anatomy to decide whether the next proof target is tail coercivity or Schur subtraction control."

canonicalGText : String
canonicalGText =
  "G: keep the promotion flags false and do not overread the sampled cancellation as a theorem."

canonicalFText : String
canonicalFText =
  "F: the open gap is still the analytic bridge from finite-shell Schur telemetry to a structural q_gap lower bound and PDE-level residence control."

record NSTriadKNMixedTailSchurGapAnatomyORCSLPGF : Set where
  constructor mkNSTriadKNMixedTailSchurGapAnatomyORCSLPGF
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

canonicalNSTriadKNMixedTailSchurGapAnatomyORCSLPGF :
  NSTriadKNMixedTailSchurGapAnatomyORCSLPGF
canonicalNSTriadKNMixedTailSchurGapAnatomyORCSLPGF =
  mkNSTriadKNMixedTailSchurGapAnatomyORCSLPGF
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

record NSTriadKNMixedTailSchurGapAnatomyReceipt : Setω where
  constructor mkNSTriadKNMixedTailSchurGapAnatomyReceipt
  field
    receiptName :
      String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNMixedTailSchurGapAnatomyReceipt"

    status :
      NSTriadKNMixedTailSchurGapAnatomyStatus
    statusIsCanonical :
      status ≡ mixedTailSchurGapAnatomyRecorded

    receiptText :
      String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    readoutText :
      String
    readoutTextIsCanonical :
      readoutText ≡ canonicalReadoutText

    sourceFitSummaryText :
      String
    sourceFitSummaryTextIsCanonical :
      sourceFitSummaryText ≡ canonicalSourceFitSummaryText

    sourceProofObligationMapText :
      String
    sourceProofObligationMapTextIsCanonical :
      sourceProofObligationMapText ≡ canonicalSourceProofObligationMapText

    anatomyArtifactJSON :
      String
    anatomyArtifactJSONIsCanonical :
      anatomyArtifactJSON ≡ canonicalAnatomyArtifactJSON

    anatomyArtifactMarkdown :
      String
    anatomyArtifactMarkdownIsCanonical :
      anatomyArtifactMarkdown ≡ canonicalAnatomyArtifactMarkdown

    rows :
      List NSTriadKNMixedTailSchurGapAnatomyRow
    rowsAreCanonical :
      rows ≡ canonicalNSTriadKNMixedTailSchurGapAnatomyRows

    metrics :
      List NSTriadKNMixedTailSchurGapAnatomyMetric
    metricsAreCanonical :
      metrics ≡ canonicalNSTriadKNMixedTailSchurGapAnatomyMetrics

    openGaps :
      List NSTriadKNMixedTailSchurGapAnatomyOpenGap
    openGapsAreCanonical :
      openGaps ≡ canonicalNSTriadKNMixedTailSchurGapAnatomyOpenGaps

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
      List NSTriadKNMixedTailSchurGapAnatomyPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    orcslpgf :
      NSTriadKNMixedTailSchurGapAnatomyORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadKNMixedTailSchurGapAnatomyORCSLPGF

open NSTriadKNMixedTailSchurGapAnatomyReceipt public

canonicalNSTriadKNMixedTailSchurGapAnatomyReceipt :
  NSTriadKNMixedTailSchurGapAnatomyReceipt
canonicalNSTriadKNMixedTailSchurGapAnatomyReceipt =
  mkNSTriadKNMixedTailSchurGapAnatomyReceipt
    "NSTriadKNMixedTailSchurGapAnatomyReceipt"
    refl
    mixedTailSchurGapAnatomyRecorded
    refl
    canonicalReceiptText
    refl
    canonicalReadoutText
    refl
    canonicalSourceFitSummaryText
    refl
    canonicalSourceProofObligationMapText
    refl
    canonicalAnatomyArtifactJSON
    refl
    canonicalAnatomyArtifactMarkdown
    refl
    canonicalNSTriadKNMixedTailSchurGapAnatomyRows
    refl
    canonicalNSTriadKNMixedTailSchurGapAnatomyMetrics
    refl
    canonicalNSTriadKNMixedTailSchurGapAnatomyOpenGaps
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
    canonicalNSTriadKNMixedTailSchurGapAnatomyORCSLPGF
    refl

schurGapAnatomyKeepsTheoremPromotedFalse :
  theoremPromoted canonicalNSTriadKNMixedTailSchurGapAnatomyReceipt ≡ false
schurGapAnatomyKeepsTheoremPromotedFalse = refl

schurGapAnatomyKeepsFullNSPromotedFalse :
  fullNSPromoted canonicalNSTriadKNMixedTailSchurGapAnatomyReceipt ≡ false
schurGapAnatomyKeepsFullNSPromotedFalse = refl

schurGapAnatomyKeepsBKMExclusionFalse :
  bkmExclusionProved canonicalNSTriadKNMixedTailSchurGapAnatomyReceipt ≡ false
schurGapAnatomyKeepsBKMExclusionFalse = refl

schurGapAnatomyKeepsClayPromotedFalse :
  clayPromoted canonicalNSTriadKNMixedTailSchurGapAnatomyReceipt ≡ false
schurGapAnatomyKeepsClayPromotedFalse = refl

schurGapAnatomyKeepsTerminalPromotedFalse :
  terminalPromoted canonicalNSTriadKNMixedTailSchurGapAnatomyReceipt ≡ false
schurGapAnatomyKeepsTerminalPromotedFalse = refl
