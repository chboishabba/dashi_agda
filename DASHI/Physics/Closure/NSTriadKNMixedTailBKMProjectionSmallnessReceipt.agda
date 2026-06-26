module DASHI.Physics.Closure.NSTriadKNMixedTailBKMProjectionSmallnessReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSTriadKNMixedTailProofObligationMapReceipt as Obligations
import DASHI.Physics.Closure.NSTriadKNMixedTailSchurScalingReceipt as Scaling

------------------------------------------------------------------------
-- Candidate-only finite-shell BKM-projection smallness receipt.
--
-- This receipt records the next bridge question after the diagonal-residue
-- and Schur-scaling reports: whether the bad mixed-tail eigenpiece is
-- structurally small against the BKM stretching proxy, or merely looks small
-- on the sampled shells.  It is not a theorem, not a full-NS promotion, not a
-- BKM exclusion proof, and not a Clay claim.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSTriadKNMixedTailBKMProjectionSmallnessStatus : Set where
  mixedTailBKMProjectionSmallnessRecorded :
    NSTriadKNMixedTailBKMProjectionSmallnessStatus

data NSTriadKNMixedTailBKMProjectionSmallnessRow : Set where
  shell6K5Eta025BKMProjectionSmallnessRow :
    NSTriadKNMixedTailBKMProjectionSmallnessRow
  shell8K7Eta025BKMProjectionSmallnessRow :
    NSTriadKNMixedTailBKMProjectionSmallnessRow
  shell10K9Eta025BKMProjectionSmallnessRow :
    NSTriadKNMixedTailBKMProjectionSmallnessRow
  shell12K11Eta025BKMProjectionSmallnessRow :
    NSTriadKNMixedTailBKMProjectionSmallnessRow

canonicalNSTriadKNMixedTailBKMProjectionSmallnessRows :
  List NSTriadKNMixedTailBKMProjectionSmallnessRow
canonicalNSTriadKNMixedTailBKMProjectionSmallnessRows =
  shell6K5Eta025BKMProjectionSmallnessRow
  ∷ shell8K7Eta025BKMProjectionSmallnessRow
  ∷ shell10K9Eta025BKMProjectionSmallnessRow
  ∷ shell12K11Eta025BKMProjectionSmallnessRow
  ∷ []

nSTriadKNMixedTailBKMProjectionSmallnessRowCount : Nat
nSTriadKNMixedTailBKMProjectionSmallnessRowCount =
  listLength canonicalNSTriadKNMixedTailBKMProjectionSmallnessRows

nSTriadKNMixedTailBKMProjectionSmallnessRowCountIs4 :
  nSTriadKNMixedTailBKMProjectionSmallnessRowCount ≡ 4
nSTriadKNMixedTailBKMProjectionSmallnessRowCountIs4 = refl

data NSTriadKNMixedTailBKMProjectionSmallnessMetric : Set where
  bkmProjectionSquaredRecorded :
    NSTriadKNMixedTailBKMProjectionSmallnessMetric
  bkmProjectionTimesDRecorded :
    NSTriadKNMixedTailBKMProjectionSmallnessMetric
  bkmProjectionOverQGapRecorded :
    NSTriadKNMixedTailBKMProjectionSmallnessMetric
  qGapRecorded :
    NSTriadKNMixedTailBKMProjectionSmallnessMetric
  qGapN2Recorded :
    NSTriadKNMixedTailBKMProjectionSmallnessMetric
  tailRayleighRecorded :
    NSTriadKNMixedTailBKMProjectionSmallnessMetric
  crossLNegRecorded :
    NSTriadKNMixedTailBKMProjectionSmallnessMetric
  eigenTailMassRecorded :
    NSTriadKNMixedTailBKMProjectionSmallnessMetric

canonicalNSTriadKNMixedTailBKMProjectionSmallnessMetrics :
  List NSTriadKNMixedTailBKMProjectionSmallnessMetric
canonicalNSTriadKNMixedTailBKMProjectionSmallnessMetrics =
  bkmProjectionSquaredRecorded
  ∷ bkmProjectionTimesDRecorded
  ∷ bkmProjectionOverQGapRecorded
  ∷ qGapRecorded
  ∷ qGapN2Recorded
  ∷ tailRayleighRecorded
  ∷ crossLNegRecorded
  ∷ eigenTailMassRecorded
  ∷ []

nSTriadKNMixedTailBKMProjectionSmallnessMetricCount : Nat
nSTriadKNMixedTailBKMProjectionSmallnessMetricCount =
  listLength canonicalNSTriadKNMixedTailBKMProjectionSmallnessMetrics

nSTriadKNMixedTailBKMProjectionSmallnessMetricCountIs8 :
  nSTriadKNMixedTailBKMProjectionSmallnessMetricCount ≡ 8
nSTriadKNMixedTailBKMProjectionSmallnessMetricCountIs8 = refl

data NSTriadKNMixedTailBKMProjectionSmallnessCandidateLemma : Set where
  structuralBKMProjectionSmallnessCandidate :
    NSTriadKNMixedTailBKMProjectionSmallnessCandidateLemma
  orthogonalityResidueSeparationCandidate :
    NSTriadKNMixedTailBKMProjectionSmallnessCandidateLemma
  residenceBridgeCandidate :
    NSTriadKNMixedTailBKMProjectionSmallnessCandidateLemma

canonicalNSTriadKNMixedTailBKMProjectionSmallnessCandidateLemmas :
  List NSTriadKNMixedTailBKMProjectionSmallnessCandidateLemma
canonicalNSTriadKNMixedTailBKMProjectionSmallnessCandidateLemmas =
  structuralBKMProjectionSmallnessCandidate
  ∷ orthogonalityResidueSeparationCandidate
  ∷ residenceBridgeCandidate
  ∷ []

nSTriadKNMixedTailBKMProjectionSmallnessCandidateLemmaCount : Nat
nSTriadKNMixedTailBKMProjectionSmallnessCandidateLemmaCount =
  listLength canonicalNSTriadKNMixedTailBKMProjectionSmallnessCandidateLemmas

nSTriadKNMixedTailBKMProjectionSmallnessCandidateLemmaCountIs3 :
  nSTriadKNMixedTailBKMProjectionSmallnessCandidateLemmaCount ≡ 3
nSTriadKNMixedTailBKMProjectionSmallnessCandidateLemmaCountIs3 = refl

data NSTriadKNMixedTailBKMProjectionSmallnessOpenGap : Set where
  structuralProjectionEstimateOpen :
    NSTriadKNMixedTailBKMProjectionSmallnessOpenGap
  analyticProjectionDecayOpen :
    NSTriadKNMixedTailBKMProjectionSmallnessOpenGap
  finiteDimensionalToPDETrajectoryBridgeOpen :
    NSTriadKNMixedTailBKMProjectionSmallnessOpenGap
  residenceTimeBKMContradictionOpen :
    NSTriadKNMixedTailBKMProjectionSmallnessOpenGap
  noTheoremFullNSOrClayPromotion :
    NSTriadKNMixedTailBKMProjectionSmallnessOpenGap

canonicalNSTriadKNMixedTailBKMProjectionSmallnessOpenGaps :
  List NSTriadKNMixedTailBKMProjectionSmallnessOpenGap
canonicalNSTriadKNMixedTailBKMProjectionSmallnessOpenGaps =
  structuralProjectionEstimateOpen
  ∷ analyticProjectionDecayOpen
  ∷ finiteDimensionalToPDETrajectoryBridgeOpen
  ∷ residenceTimeBKMContradictionOpen
  ∷ noTheoremFullNSOrClayPromotion
  ∷ []

nSTriadKNMixedTailBKMProjectionSmallnessOpenGapCount : Nat
nSTriadKNMixedTailBKMProjectionSmallnessOpenGapCount =
  listLength canonicalNSTriadKNMixedTailBKMProjectionSmallnessOpenGaps

nSTriadKNMixedTailBKMProjectionSmallnessOpenGapCountIs5 :
  nSTriadKNMixedTailBKMProjectionSmallnessOpenGapCount ≡ 5
nSTriadKNMixedTailBKMProjectionSmallnessOpenGapCountIs5 = refl

data NSTriadKNMixedTailBKMProjectionSmallnessPromotion : Set where

promotionImpossibleHere :
  NSTriadKNMixedTailBKMProjectionSmallnessPromotion → ⊥
promotionImpossibleHere ()

canonicalReceiptText : String
canonicalReceiptText =
  "Candidate-only finite-shell BKM-projection smallness receipt for the N=6,8,10,12 forced-tail rows with K=N-1 and eta=0.25."

canonicalReadoutText : String
canonicalReadoutText =
  "The sparse-Schur scaling report says the BKM-tail projection squared fraction is tiny across N=6,8,10,12, drops sharply by N=12, and is not monotone from N=6 to N=8; this receipt records that the next analytic target is a structural projection estimate rather than another telemetry scan."

canonicalSourceScalingArtifactJSON : String
canonicalSourceScalingArtifactJSON = Scaling.canonicalFitArtifactJSON

canonicalSourceScalingArtifactMarkdown : String
canonicalSourceScalingArtifactMarkdown = Scaling.canonicalFitArtifactMarkdown

canonicalSourceProofObligationMapText : String
canonicalSourceProofObligationMapText =
  "DASHI/Physics/Closure/NSTriadKNMixedTailProofObligationMapReceipt.agda"

canonicalBKMArtifactJSON : String
canonicalBKMArtifactJSON =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_bkm_projection_smallness_20260624/summary.json"

canonicalBKMArtifactMarkdown : String
canonicalBKMArtifactMarkdown =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_bkm_projection_smallness_20260624/summary.md"

canonicalOText : String
canonicalOText =
  "O: record the BKM-projection smallness bridge as a candidate-only finite-shell receipt."

canonicalRText : String
canonicalRText =
  "R: distinguish numerical projection smallness from a structural orthogonality estimate against the BKM stretching proxy."

canonicalCText : String
canonicalCText =
  "C: export the sampled rows, projection smallness fit, source scaling receipt, open gaps, and false promotion flags."

canonicalSText : String
canonicalSText =
  "S: finite-shell telemetry only; no theorem authority, no full-NS promotion, no BKM exclusion proof, and no Clay promotion."

canonicalLText : String
canonicalLText =
  "L: diagonal-residue bridge -> BKM projection smallness -> residence bridge still open."

canonicalPText : String
canonicalPText =
  "P: prove the bad mixed-tail branch is structurally small against the BKM proxy, then use that to support the residence bridge."

canonicalGText : String
canonicalGText =
  "G: keep the candidate-only posture; the sampled rows support the target but do not discharge it."

canonicalFText : String
canonicalFText =
  "F: the open gap is the structural projection estimate and the finite-dimensional-to-PDE bridge, not a missing telemetry scan."

record NSTriadKNMixedTailBKMProjectionSmallnessORCSLPGF : Set where
  constructor mkNSTriadKNMixedTailBKMProjectionSmallnessORCSLPGF
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

canonicalNSTriadKNMixedTailBKMProjectionSmallnessORCSLPGF :
  NSTriadKNMixedTailBKMProjectionSmallnessORCSLPGF
canonicalNSTriadKNMixedTailBKMProjectionSmallnessORCSLPGF =
  mkNSTriadKNMixedTailBKMProjectionSmallnessORCSLPGF
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

record NSTriadKNMixedTailBKMProjectionSmallnessReceipt : Setω where
  constructor mkNSTriadKNMixedTailBKMProjectionSmallnessReceipt
  field
    receiptName :
      String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNMixedTailBKMProjectionSmallnessReceipt"

    status :
      NSTriadKNMixedTailBKMProjectionSmallnessStatus
    statusIsCanonical :
      status ≡ mixedTailBKMProjectionSmallnessRecorded

    receiptText :
      String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    readoutText :
      String
    readoutTextIsCanonical :
      readoutText ≡ canonicalReadoutText

    sourceScalingArtifactJSON :
      String
    sourceScalingArtifactJSONIsCanonical :
      sourceScalingArtifactJSON ≡ canonicalSourceScalingArtifactJSON

    sourceScalingArtifactMarkdown :
      String
    sourceScalingArtifactMarkdownIsCanonical :
      sourceScalingArtifactMarkdown ≡ canonicalSourceScalingArtifactMarkdown

    sourceProofObligationMapText :
      String
    sourceProofObligationMapTextIsCanonical :
      sourceProofObligationMapText ≡ canonicalSourceProofObligationMapText

    bkmArtifactJSON :
      String
    bkmArtifactJSONIsCanonical :
      bkmArtifactJSON ≡ canonicalBKMArtifactJSON

    bkmArtifactMarkdown :
      String
    bkmArtifactMarkdownIsCanonical :
      bkmArtifactMarkdown ≡ canonicalBKMArtifactMarkdown

    rows :
      List NSTriadKNMixedTailBKMProjectionSmallnessRow
    rowsAreCanonical :
      rows ≡ canonicalNSTriadKNMixedTailBKMProjectionSmallnessRows

    candidateLemmas :
      List NSTriadKNMixedTailBKMProjectionSmallnessCandidateLemma
    candidateLemmasAreCanonical :
      candidateLemmas ≡ canonicalNSTriadKNMixedTailBKMProjectionSmallnessCandidateLemmas

    openGaps :
      List NSTriadKNMixedTailBKMProjectionSmallnessOpenGap
    openGapsAreCanonical :
      openGaps ≡ canonicalNSTriadKNMixedTailBKMProjectionSmallnessOpenGaps

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
      List NSTriadKNMixedTailBKMProjectionSmallnessPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    orcslpgf :
      NSTriadKNMixedTailBKMProjectionSmallnessORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadKNMixedTailBKMProjectionSmallnessORCSLPGF

open NSTriadKNMixedTailBKMProjectionSmallnessReceipt public

canonicalNSTriadKNMixedTailBKMProjectionSmallnessReceipt :
  NSTriadKNMixedTailBKMProjectionSmallnessReceipt
canonicalNSTriadKNMixedTailBKMProjectionSmallnessReceipt =
  mkNSTriadKNMixedTailBKMProjectionSmallnessReceipt
    "NSTriadKNMixedTailBKMProjectionSmallnessReceipt"
    refl
    mixedTailBKMProjectionSmallnessRecorded
    refl
    canonicalReceiptText
    refl
    canonicalReadoutText
    refl
    canonicalSourceScalingArtifactJSON
    refl
    canonicalSourceScalingArtifactMarkdown
    refl
    canonicalSourceProofObligationMapText
    refl
    canonicalBKMArtifactJSON
    refl
    canonicalBKMArtifactMarkdown
    refl
    canonicalNSTriadKNMixedTailBKMProjectionSmallnessRows
    refl
    canonicalNSTriadKNMixedTailBKMProjectionSmallnessCandidateLemmas
    refl
    canonicalNSTriadKNMixedTailBKMProjectionSmallnessOpenGaps
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
    canonicalNSTriadKNMixedTailBKMProjectionSmallnessORCSLPGF
    refl

bkmProjectionSmallnessKeepsTheoremPromotedFalse :
  theoremPromoted canonicalNSTriadKNMixedTailBKMProjectionSmallnessReceipt ≡ false
bkmProjectionSmallnessKeepsTheoremPromotedFalse = refl

bkmProjectionSmallnessKeepsFullNSPromotedFalse :
  fullNSPromoted canonicalNSTriadKNMixedTailBKMProjectionSmallnessReceipt ≡ false
bkmProjectionSmallnessKeepsFullNSPromotedFalse = refl

bkmProjectionSmallnessKeepsBKMExclusionFalse :
  bkmExclusionProved canonicalNSTriadKNMixedTailBKMProjectionSmallnessReceipt ≡ false
bkmProjectionSmallnessKeepsBKMExclusionFalse = refl

bkmProjectionSmallnessKeepsClayPromotedFalse :
  clayPromoted canonicalNSTriadKNMixedTailBKMProjectionSmallnessReceipt ≡ false
bkmProjectionSmallnessKeepsClayPromotedFalse = refl

bkmProjectionSmallnessKeepsTerminalPromotedFalse :
  terminalPromoted canonicalNSTriadKNMixedTailBKMProjectionSmallnessReceipt ≡ false
bkmProjectionSmallnessKeepsTerminalPromotedFalse = refl
