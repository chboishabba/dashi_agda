module DASHI.Physics.Closure.NSLayerKornLiteratureClosureReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- LayerKorn literature closure receipt.
--
-- This module is fail-closed and records the literature route surface only.
-- It captures the required assumptions/targets:
--   * GST25 lower-dimensional trace Korn theorem for interior level-set surface
--     Σ = ∂Ω_K (theorem applicability is still open),
--   * Bauer-Pauly 2015 tangential Korn constant support (non-mathematized),
--   * trace H¹(Nε) → H^{1/2}(Σ),
--   * bounded second fundamental form and nondegenerate ∇λ₂.
-- It also records that LayerKorn is literature-closeable only once theorem
-- applicability and proof terms are verified; it does not discharge h_delta1 or
-- Clay NS.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSLayerKornLiteratureClosureStatus : Set where
  layerKornLiteratureReceiptRecorded :
    NSLayerKornLiteratureClosureStatus

data NSLayerKornLiteratureClosureStage : Set where
  gst25TraceKornStageRecorded :
    NSLayerKornLiteratureClosureStage
  gST25ForInteriorLevelSetSurfaceRecorded :
    NSLayerKornLiteratureClosureStage
  bauerPauly2015TangentialKornConstantRecorded :
    NSLayerKornLiteratureClosureStage
  traceH1ToHalfRecorded :
    NSLayerKornLiteratureClosureStage
  boundedSecondFundamentalFormRecorded :
    NSLayerKornLiteratureClosureStage
  nondegenerateGradLambda2Recorded :
    NSLayerKornLiteratureClosureStage
  layerKornLiteratureCloseableRecorded :
    NSLayerKornLiteratureClosureStage
  theoremApplicabilityVerificationPendingRecorded :
    NSLayerKornLiteratureClosureStage
  proofTermVerificationPendingRecorded :
    NSLayerKornLiteratureClosureStage
  hDelta1NotDischargedRecorded :
    NSLayerKornLiteratureClosureStage
  clayNSNotDischargedRecorded :
    NSLayerKornLiteratureClosureStage

canonicalNSLayerKornLiteratureClosureStages :
  List NSLayerKornLiteratureClosureStage
canonicalNSLayerKornLiteratureClosureStages =
  gst25TraceKornStageRecorded
  ∷ gST25ForInteriorLevelSetSurfaceRecorded
  ∷ bauerPauly2015TangentialKornConstantRecorded
  ∷ traceH1ToHalfRecorded
  ∷ boundedSecondFundamentalFormRecorded
  ∷ nondegenerateGradLambda2Recorded
  ∷ layerKornLiteratureCloseableRecorded
  ∷ theoremApplicabilityVerificationPendingRecorded
  ∷ proofTermVerificationPendingRecorded
  ∷ hDelta1NotDischargedRecorded
  ∷ clayNSNotDischargedRecorded
  ∷ []

data NSLayerKornLiteratureClosureBlocker : Set where
  gst25TraceKornTheoremNeedsApplicabilityCheck :
    NSLayerKornLiteratureClosureBlocker
  bauerPauly2015ConstantSupportNeedsExternalJustification :
    NSLayerKornLiteratureClosureBlocker
  traceH1ToHalfNeedsBoundaryTraceJustification :
    NSLayerKornLiteratureClosureBlocker
  secondFundamentalFormBoundNeedsProof :
    NSLayerKornLiteratureClosureBlocker
  gradLambda2NondegeneracyNeedsVerification :
    NSLayerKornLiteratureClosureBlocker
  theoremApplicabilityRequiresProof :
    NSLayerKornLiteratureClosureBlocker
  proofTermsOpen :
    NSLayerKornLiteratureClosureBlocker
  hDelta1NotDischargedBlocker :
    NSLayerKornLiteratureClosureBlocker
  clayNSNotDischargedBlocker :
    NSLayerKornLiteratureClosureBlocker

canonicalNSLayerKornLiteratureClosureBlockers :
  List NSLayerKornLiteratureClosureBlocker
canonicalNSLayerKornLiteratureClosureBlockers =
  gst25TraceKornTheoremNeedsApplicabilityCheck
  ∷ bauerPauly2015ConstantSupportNeedsExternalJustification
  ∷ traceH1ToHalfNeedsBoundaryTraceJustification
  ∷ secondFundamentalFormBoundNeedsProof
  ∷ gradLambda2NondegeneracyNeedsVerification
  ∷ theoremApplicabilityRequiresProof
  ∷ proofTermsOpen
  ∷ hDelta1NotDischargedBlocker
  ∷ clayNSNotDischargedBlocker
  ∷ []

gst25SurfaceText : String
gst25SurfaceText =
  "GST25 lower-dimensional trace Korn theorem is recorded for interior Σ = ∂Ω_K; applicability is explicitly unverified and conditional."

bauerPaulyText : String
bauerPaulyText =
  "Bauer-Pauly 2015 tangential Korn constant support is recorded as a literature dependency."

traceText : String
traceText =
  "Trace target H¹(Nε) → H^{1/2}(Σ) is recorded as a required boundary trace estimate."

geometryText : String
geometryText =
  "Geometric assumptions recorded: bounded second fundamental form on Σ and nondegenerate ∇λ₂."

closeableText : String
closeableText =
  "LayerKorn is recorded as literature-closeable, but not promoted until theorem applicability and proof terms are verified."

verificationText : String
verificationText =
  "Theorem applicability remains open, proof-term transfer remains open, h_delta1 is not discharged, and Clay NS is not promoted."

receiptBoundaryText : List String
receiptBoundaryText =
  "GST25 lower-dimensional trace Korn for Σ = ∂Ω_K"
  ∷ "Bauer-Pauly 2015 tangential Korn constant support"
  ∷ "trace H¹(Nε) → H^{1/2}(Σ)"
  ∷ "bounded second fundamental form assumption"
  ∷ "nondegenerate ∇λ₂ condition"
  ∷ "LayerKorn marked literature-closeable with explicit theorem+proof-term verification guards"
  ∷ "h_delta1 is not discharged"
  ∷ "Clay NS is not promoted"
  ∷ "Route is empirical/conditional/didactic and remains fail-closed"
  ∷ []

canonicalBoundaryText : String
canonicalBoundaryText =
  "LayerKorn literature closure surface: Σ = ∂Ω_K with GST25-style trace Korn and tangential Korn dependence, trace H¹(Nε)→H^{1/2}(Σ), geometric bounded-curvature/nondegenerate ∇λ₂ assumptions, and explicit verification gates preventing promotion until theorem and proof terms are checked."

data NSLayerKornLiteratureClosurePromotion : Set where

layerKornLiteratureClosurePromotionImpossibleHere :
  NSLayerKornLiteratureClosurePromotion → ⊥
layerKornLiteratureClosurePromotionImpossibleHere ()

record NSLayerKornLiteratureClosureReceipt : Setω where
  constructor mkNSLayerKornLiteratureClosureReceipt
  field
    status :
      NSLayerKornLiteratureClosureStatus
    statusIsCanonical :
      status ≡ layerKornLiteratureReceiptRecorded

    stageTrail :
      List NSLayerKornLiteratureClosureStage
    stageTrailIsCanonical :
      stageTrail ≡ canonicalNSLayerKornLiteratureClosureStages
    stageCount :
      Nat
    stageCountIsCanonical :
      stageCount ≡ listLength canonicalNSLayerKornLiteratureClosureStages

    blockerTrail :
      List NSLayerKornLiteratureClosureBlocker
    blockerTrailIsCanonical :
      blockerTrail ≡ canonicalNSLayerKornLiteratureClosureBlockers
    blockerCount :
      Nat
    blockerCountIsCanonical :
      blockerCount ≡ listLength canonicalNSLayerKornLiteratureClosureBlockers

    gst25SurfaceTextField :
      String
    gst25SurfaceTextFieldIsCanonical :
      gst25SurfaceTextField ≡ gst25SurfaceText
    bauerPaulyTextField :
      String
    bauerPaulyTextFieldIsCanonical :
      bauerPaulyTextField ≡ bauerPaulyText
    traceTextField :
      String
    traceTextFieldIsCanonical :
      traceTextField ≡ traceText
    geometryTextField :
      String
    geometryTextFieldIsCanonical :
      geometryTextField ≡ geometryText
    closeableTextField :
      String
    closeableTextFieldIsCanonical :
      closeableTextField ≡ closeableText
    verificationTextField :
      String
    verificationTextFieldIsCanonical :
      verificationTextField ≡ verificationText

    gst25Applicable :
      Bool
    gst25ApplicableIsFalse :
      gst25Applicable ≡ false

    bauerPaulySupportRecorded :
      Bool
    bauerPaulySupportRecordedIsTrue :
      bauerPaulySupportRecorded ≡ true

    traceH1ToHalfSurfaceRecorded :
      Bool
    traceH1ToHalfSurfaceRecordedIsTrue :
      traceH1ToHalfSurfaceRecorded ≡ true

    secondFundamentalFormBounded :
      Bool
    secondFundamentalFormBoundedIsTrue :
      secondFundamentalFormBounded ≡ true

    gradLambda2Nondegenerate :
      Bool
    gradLambda2NondegenerateIsTrue :
      gradLambda2Nondegenerate ≡ true

    layerKornLiteratureCloseable :
      Bool
    layerKornLiteratureCloseableIsTrue :
      layerKornLiteratureCloseable ≡ true

    theoremApplicabilityVerified :
      Bool
    theoremApplicabilityVerifiedIsFalse :
      theoremApplicabilityVerified ≡ false

    proofTermsVerified :
      Bool
    proofTermsVerifiedIsFalse :
      proofTermsVerified ≡ false

    hDelta1Discharged :
      Bool
    hDelta1DischargedIsFalse :
      hDelta1Discharged ≡ false

    clayNavierStokesPromoted :
      Bool
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    layerKornPromoted :
      Bool
    layerKornPromotedIsFalse :
      layerKornPromoted ≡ false

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryText
    receiptBoundaryParagraph :
      String
    receiptBoundaryParagraphIsCanonical :
      receiptBoundaryParagraph ≡ canonicalBoundaryText

open NSLayerKornLiteratureClosureReceipt public

canonicalNSLayerKornLiteratureClosureReceipt :
  NSLayerKornLiteratureClosureReceipt
canonicalNSLayerKornLiteratureClosureReceipt =
  mkNSLayerKornLiteratureClosureReceipt
    layerKornLiteratureReceiptRecorded
    refl
    canonicalNSLayerKornLiteratureClosureStages
    refl
    (listLength canonicalNSLayerKornLiteratureClosureStages)
    refl
    canonicalNSLayerKornLiteratureClosureBlockers
    refl
    (listLength canonicalNSLayerKornLiteratureClosureBlockers)
    refl
    gst25SurfaceText
    refl
    bauerPaulyText
    refl
    traceText
    refl
    geometryText
    refl
    closeableText
    refl
    verificationText
    refl
    false
    refl
    true
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
    receiptBoundaryText
    refl
    canonicalBoundaryText
    refl

canonicalLayerKornLiteratureStageTrailIsCanonical :
  stageTrail canonicalNSLayerKornLiteratureClosureReceipt ≡
  canonicalNSLayerKornLiteratureClosureStages
canonicalLayerKornLiteratureStageTrailIsCanonical = refl

canonicalLayerKornLiteratureBlockerTrailIsCanonical :
  blockerTrail canonicalNSLayerKornLiteratureClosureReceipt ≡
  canonicalNSLayerKornLiteratureClosureBlockers
canonicalLayerKornLiteratureBlockerTrailIsCanonical = refl

canonicalLayerKornLiteratureStageCountIsCanonical :
  stageCount canonicalNSLayerKornLiteratureClosureReceipt ≡
  listLength canonicalNSLayerKornLiteratureClosureStages
canonicalLayerKornLiteratureStageCountIsCanonical = refl

canonicalLayerKornLiteratureBlockerCountIsCanonical :
  blockerCount canonicalNSLayerKornLiteratureClosureReceipt ≡
  listLength canonicalNSLayerKornLiteratureClosureBlockers
canonicalLayerKornLiteratureBlockerCountIsCanonical = refl

canonicalLayerKornLiteratureGST25SurfaceTextIsCanonical :
  gst25SurfaceTextField canonicalNSLayerKornLiteratureClosureReceipt ≡ gst25SurfaceText
canonicalLayerKornLiteratureGST25SurfaceTextIsCanonical = refl

canonicalLayerKornLiteratureBauerPaulyTextIsCanonical :
  bauerPaulyTextField canonicalNSLayerKornLiteratureClosureReceipt ≡ bauerPaulyText
canonicalLayerKornLiteratureBauerPaulyTextIsCanonical = refl

canonicalLayerKornLiteratureTraceTextIsCanonical :
  traceTextField canonicalNSLayerKornLiteratureClosureReceipt ≡ traceText
canonicalLayerKornLiteratureTraceTextIsCanonical = refl

canonicalLayerKornLiteratureGeometryTextIsCanonical :
  geometryTextField canonicalNSLayerKornLiteratureClosureReceipt ≡ geometryText
canonicalLayerKornLiteratureGeometryTextIsCanonical = refl

canonicalLayerKornLiteratureCloseableTextIsCanonical :
  closeableTextField canonicalNSLayerKornLiteratureClosureReceipt ≡ closeableText
canonicalLayerKornLiteratureCloseableTextIsCanonical = refl

canonicalLayerKornLiteratureVerificationTextIsCanonical :
  verificationTextField canonicalNSLayerKornLiteratureClosureReceipt ≡ verificationText
canonicalLayerKornLiteratureVerificationTextIsCanonical = refl

canonicalLayerKornLiteratureReceiptBoundaryIsCanonical :
  receiptBoundary canonicalNSLayerKornLiteratureClosureReceipt ≡ receiptBoundaryText
canonicalLayerKornLiteratureReceiptBoundaryIsCanonical = refl

canonicalLayerKornLiteratureReceiptBoundaryParagraphIsCanonical :
  receiptBoundaryParagraph canonicalNSLayerKornLiteratureClosureReceipt ≡ canonicalBoundaryText
canonicalLayerKornLiteratureReceiptBoundaryParagraphIsCanonical = refl

canonicalLayerKornLiteratureGst25ApplicableIsFalse :
  gst25Applicable canonicalNSLayerKornLiteratureClosureReceipt ≡ false
canonicalLayerKornLiteratureGst25ApplicableIsFalse = refl

canonicalLayerKornLiteratureProofTermsVerifiedIsFalse :
  proofTermsVerified canonicalNSLayerKornLiteratureClosureReceipt ≡ false
canonicalLayerKornLiteratureProofTermsVerifiedIsFalse = refl

canonicalLayerKornLiteratureLayerKornPromotedIsFalse :
  layerKornPromoted canonicalNSLayerKornLiteratureClosureReceipt ≡ false
canonicalLayerKornLiteratureLayerKornPromotedIsFalse = refl

canonicalLayerKornLiteratureHDelta1DischargedIsFalse :
  hDelta1Discharged canonicalNSLayerKornLiteratureClosureReceipt ≡ false
canonicalLayerKornLiteratureHDelta1DischargedIsFalse = refl

canonicalLayerKornLiteratureClayPromotionIsFalse :
  clayNavierStokesPromoted canonicalNSLayerKornLiteratureClosureReceipt ≡ false
canonicalLayerKornLiteratureClayPromotionIsFalse = refl
