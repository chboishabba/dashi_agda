module DASHI.Physics.Closure.NSShahmurovAxisymmetricReductionExternalReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSShahmurovTwoPaperClaimIntakeReceipt as Intake

------------------------------------------------------------------------
-- Candidate-only external Shahmurov reduction receipt.
--
-- This records the reduction theorem in the external paper as a candidate
-- endpoint-reduction carrier only.  It is not a proof of the axisymmetric-
-- with-swirl endpoint, not a full-NS promotion, and not a Clay claim.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSShahmurovAxisymmetricReductionExternalStatus : Set where
  shahmurovReductionRecorded :
    NSShahmurovAxisymmetricReductionExternalStatus

data NSShahmurovAxisymmetricReductionExternalRow : Set where
  reductionTheoremRecorded :
    NSShahmurovAxisymmetricReductionExternalRow
  firstSingularityToAxisymmetricSwirlEndpointRecorded :
    NSShahmurovAxisymmetricReductionExternalRow
  conditionalOnASRecorded :
    NSShahmurovAxisymmetricReductionExternalRow
  noIndependentFullRegularityProofRecorded :
    NSShahmurovAxisymmetricReductionExternalRow
  terminalCompatibilityRecorded :
    NSShahmurovAxisymmetricReductionExternalRow

canonicalNSShahmurovAxisymmetricReductionExternalRows :
  List NSShahmurovAxisymmetricReductionExternalRow
canonicalNSShahmurovAxisymmetricReductionExternalRows =
  reductionTheoremRecorded
  ∷ firstSingularityToAxisymmetricSwirlEndpointRecorded
  ∷ conditionalOnASRecorded
  ∷ noIndependentFullRegularityProofRecorded
  ∷ terminalCompatibilityRecorded
  ∷ []

nSShahmurovAxisymmetricReductionExternalRowCount : Nat
nSShahmurovAxisymmetricReductionExternalRowCount =
  listLength canonicalNSShahmurovAxisymmetricReductionExternalRows

nSShahmurovAxisymmetricReductionExternalRowCountIs5 :
  nSShahmurovAxisymmetricReductionExternalRowCount ≡ 5
nSShahmurovAxisymmetricReductionExternalRowCountIs5 = refl

data NSShahmurovAxisymmetricReductionExternalCandidateLemma : Set where
  firstSingularityReductionCandidate :
    NSShahmurovAxisymmetricReductionExternalCandidateLemma
  axisymmetricSwirlEndpointCarrierCandidate :
    NSShahmurovAxisymmetricReductionExternalCandidateLemma
  compatibilityChecklistCandidate :
    NSShahmurovAxisymmetricReductionExternalCandidateLemma

canonicalNSShahmurovAxisymmetricReductionExternalCandidateLemmas :
  List NSShahmurovAxisymmetricReductionExternalCandidateLemma
canonicalNSShahmurovAxisymmetricReductionExternalCandidateLemmas =
  firstSingularityReductionCandidate
  ∷ axisymmetricSwirlEndpointCarrierCandidate
  ∷ compatibilityChecklistCandidate
  ∷ []

nSShahmurovAxisymmetricReductionExternalCandidateLemmaCount : Nat
nSShahmurovAxisymmetricReductionExternalCandidateLemmaCount =
  listLength canonicalNSShahmurovAxisymmetricReductionExternalCandidateLemmas

nSShahmurovAxisymmetricReductionExternalCandidateLemmaCountIs3 :
  nSShahmurovAxisymmetricReductionExternalCandidateLemmaCount ≡ 3
nSShahmurovAxisymmetricReductionExternalCandidateLemmaCountIs3 = refl

data NSShahmurovAxisymmetricReductionExternalOpenGap : Set where
  endpointToTrajectoryBridgeOpen :
    NSShahmurovAxisymmetricReductionExternalOpenGap
  asDependenceOpen :
    NSShahmurovAxisymmetricReductionExternalOpenGap
  noTheoremFullNSOrClayPromotion :
    NSShahmurovAxisymmetricReductionExternalOpenGap

canonicalNSShahmurovAxisymmetricReductionExternalOpenGaps :
  List NSShahmurovAxisymmetricReductionExternalOpenGap
canonicalNSShahmurovAxisymmetricReductionExternalOpenGaps =
  endpointToTrajectoryBridgeOpen
  ∷ asDependenceOpen
  ∷ noTheoremFullNSOrClayPromotion
  ∷ []

nSShahmurovAxisymmetricReductionExternalOpenGapCount : Nat
nSShahmurovAxisymmetricReductionExternalOpenGapCount =
  listLength canonicalNSShahmurovAxisymmetricReductionExternalOpenGaps

nSShahmurovAxisymmetricReductionExternalOpenGapCountIs3 :
  nSShahmurovAxisymmetricReductionExternalOpenGapCount ≡ 3
nSShahmurovAxisymmetricReductionExternalOpenGapCountIs3 = refl

data NSShahmurovAxisymmetricReductionExternalPromotion : Set where

promotionImpossibleHere :
  NSShahmurovAxisymmetricReductionExternalPromotion → ⊥
promotionImpossibleHere ()

canonicalReceiptText : String
canonicalReceiptText =
  "Candidate-only external Shahmurov reduction receipt for the first-singularity to axisymmetric-with-swirl endpoint carrier."

canonicalReadoutText : String
canonicalReadoutText =
  "The external paper states a reduction theorem: any hypothetical first singularity reduces to an axisymmetric-with-swirl endpoint, with the companion AS endpoint theorem remaining the load-bearing open target; this receipt records that interface only."

canonicalSourcePdfPath : String
canonicalSourcePdfPath =
  "/home/c/Downloads/2606.07875v1.pdf"

canonicalSourcePaperTitle : String
canonicalSourcePaperTitle =
  "Hypothetical Singularity of 3D Navier-Stokes in Clay Institute set up Reduces to Axisymmetric with Swirl class"

canonicalSourcePageCount : Nat
canonicalSourcePageCount =
  68

canonicalSourceReductionTheoremText : String
canonicalSourceReductionTheoremText =
  "Theorem 2.2 records the singular-endpoint reduction to axisymmetric-with-swirl."

canonicalSourceConditionalText : String
canonicalSourceConditionalText =
  "Corollary 2.3 is conditional: if the axisymmetric-with-swirl class is globally regular, then the full 3D smooth finite-energy statement follows."

canonicalSourceNoIndependentProofText : String
canonicalSourceNoIndependentProofText =
  "The paper explicitly says it proves a reduction theorem rather than an independent proof of the axisymmetric-with-swirl endpoint."

canonicalSourceCompatibilityText : String
canonicalSourceCompatibilityText =
  "Theorem 12.4 and the later compatibility checklist match the reduced endpoint to the companion theorem's hypotheses."

canonicalIntakeReceiptText : String
canonicalIntakeReceiptText =
  Intake.failClosedIntakeText

canonicalBridgeTargetText : String
canonicalBridgeTargetText =
  "Candidate bridge target: the reduction theorem is a structural endpoint carrier for residence-time / endpoint-exclusion reasoning, but it does not by itself discharge the AS endpoint theorem."

canonicalOText : String
canonicalOText =
  "O: record the Shahmurov reduction theorem as a candidate-only external endpoint-reduction receipt."

canonicalRText : String
canonicalRText =
  "R: isolate the first-singularity to axisymmetric-with-swirl reduction and keep the conditional AS dependence explicit."

canonicalCText : String
canonicalCText =
  "C: export the paper title, PDF path, reduction theorem, conditional corollary, compatibility text, and false promotion flags."

canonicalSText : String
canonicalSText =
  "S: the paper is a candidate reduction carrier only; no theorem authority, no full-NS promotion, and no Clay promotion are claimed here."

canonicalLText : String
canonicalLText =
  "L: first-singularity endpoint reduction -> axisymmetric-with-swirl carrier -> residence-time bridge still open."

canonicalPText : String
canonicalPText =
  "P: use the reduction theorem as the endpoint side of the residence bridge, while keeping AS as the missing theorem gate."

canonicalGText : String
canonicalGText =
  "G: keep the receipt candidate-only; the paper is a reduction carrier, not a proof of the reduced endpoint theorem."

canonicalFText : String
canonicalFText =
  "F: the open gap is endpoint exclusion for the axisymmetric-with-swirl class and the PDE bridge from reduced endpoints to trajectories."

record NSShahmurovAxisymmetricReductionExternalORCSLPGF : Set where
  constructor mkNSShahmurovAxisymmetricReductionExternalORCSLPGF
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

canonicalNSShahmurovAxisymmetricReductionExternalORCSLPGF :
  NSShahmurovAxisymmetricReductionExternalORCSLPGF
canonicalNSShahmurovAxisymmetricReductionExternalORCSLPGF =
  mkNSShahmurovAxisymmetricReductionExternalORCSLPGF
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

record NSShahmurovAxisymmetricReductionExternalReceipt : Setω where
  constructor mkNSShahmurovAxisymmetricReductionExternalReceipt
  field
    receiptName :
      String
    receiptNameIsCanonical :
      receiptName ≡ "NSShahmurovAxisymmetricReductionExternalReceipt"

    status :
      NSShahmurovAxisymmetricReductionExternalStatus
    statusIsCanonical :
      status ≡ shahmurovReductionRecorded

    receiptText :
      String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    readoutText :
      String
    readoutTextIsCanonical :
      readoutText ≡ canonicalReadoutText

    sourcePdfPath :
      String
    sourcePdfPathIsCanonical :
      sourcePdfPath ≡ canonicalSourcePdfPath

    sourcePaperTitle :
      String
    sourcePaperTitleIsCanonical :
      sourcePaperTitle ≡ canonicalSourcePaperTitle

    sourcePageCount :
      Nat
    sourcePageCountIsCanonical :
      sourcePageCount ≡ canonicalSourcePageCount

    sourceReductionTheoremText :
      String
    sourceReductionTheoremTextIsCanonical :
      sourceReductionTheoremText ≡ canonicalSourceReductionTheoremText

    sourceConditionalText :
      String
    sourceConditionalTextIsCanonical :
      sourceConditionalText ≡ canonicalSourceConditionalText

    sourceNoIndependentProofText :
      String
    sourceNoIndependentProofTextIsCanonical :
      sourceNoIndependentProofText ≡ canonicalSourceNoIndependentProofText

    sourceCompatibilityText :
      String
    sourceCompatibilityTextIsCanonical :
      sourceCompatibilityText ≡ canonicalSourceCompatibilityText

    canonicalIntakeReceiptTextField :
      String
    canonicalIntakeReceiptTextFieldIsCanonical :
      canonicalIntakeReceiptTextField ≡ canonicalIntakeReceiptText

    bridgeTargetText :
      String
    bridgeTargetTextIsCanonical :
      bridgeTargetText ≡ canonicalBridgeTargetText

    rows :
      List NSShahmurovAxisymmetricReductionExternalRow
    rowsAreCanonical :
      rows ≡ canonicalNSShahmurovAxisymmetricReductionExternalRows

    candidateLemmas :
      List NSShahmurovAxisymmetricReductionExternalCandidateLemma
    candidateLemmasAreCanonical :
      candidateLemmas ≡ canonicalNSShahmurovAxisymmetricReductionExternalCandidateLemmas

    openGaps :
      List NSShahmurovAxisymmetricReductionExternalOpenGap
    openGapsAreCanonical :
      openGaps ≡ canonicalNSShahmurovAxisymmetricReductionExternalOpenGaps

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

    promotionFlags :
      List NSShahmurovAxisymmetricReductionExternalPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    orcslpgf :
      NSShahmurovAxisymmetricReductionExternalORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSShahmurovAxisymmetricReductionExternalORCSLPGF

open NSShahmurovAxisymmetricReductionExternalReceipt public

canonicalNSShahmurovAxisymmetricReductionExternalReceipt :
  NSShahmurovAxisymmetricReductionExternalReceipt
canonicalNSShahmurovAxisymmetricReductionExternalReceipt =
  mkNSShahmurovAxisymmetricReductionExternalReceipt
    "NSShahmurovAxisymmetricReductionExternalReceipt"
    refl
    shahmurovReductionRecorded
    refl
    canonicalReceiptText
    refl
    canonicalReadoutText
    refl
    canonicalSourcePdfPath
    refl
    canonicalSourcePaperTitle
    refl
    68
    refl
    canonicalSourceReductionTheoremText
    refl
    canonicalSourceConditionalText
    refl
    canonicalSourceNoIndependentProofText
    refl
    canonicalSourceCompatibilityText
    refl
    canonicalIntakeReceiptText
    refl
    canonicalBridgeTargetText
    refl
    canonicalNSShahmurovAxisymmetricReductionExternalRows
    refl
    canonicalNSShahmurovAxisymmetricReductionExternalCandidateLemmas
    refl
    canonicalNSShahmurovAxisymmetricReductionExternalOpenGaps
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
    []
    refl
    canonicalNSShahmurovAxisymmetricReductionExternalORCSLPGF
    refl

shahmurovBridgeKeepsTheoremPromotedFalse :
  theoremPromoted canonicalNSShahmurovAxisymmetricReductionExternalReceipt ≡ false
shahmurovBridgeKeepsTheoremPromotedFalse = refl

shahmurovBridgeKeepsFullNSPromotedFalse :
  fullNSPromoted canonicalNSShahmurovAxisymmetricReductionExternalReceipt ≡ false
shahmurovBridgeKeepsFullNSPromotedFalse = refl

shahmurovBridgeKeepsClayPromotedFalse :
  clayPromoted canonicalNSShahmurovAxisymmetricReductionExternalReceipt ≡ false
shahmurovBridgeKeepsClayPromotedFalse = refl
