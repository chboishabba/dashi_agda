module DASHI.Physics.Closure.MillenniumTowerDHRSMInstanceReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MillenniumTowerSchemaReceipt as Schema
import DASHI.Physics.QFT.ConditionalGDHRSMPromotionReceipt as Conditional
import DASHI.Physics.QFT.DHRGaugeReceiptSurface as DHR
import DASHI.Physics.QFT.DHROriginalPaperAuthorityReceipt as OriginalDHR
import DASHI.Physics.QFT.DHRTensorDualGroupReconstruction as TensorDR
import DASHI.Physics.QFT.TannakaKreinFibreFunctorReceipt as Tannaka

------------------------------------------------------------------------
-- DHR/SM instance of the shared tower schema.

record MillenniumTowerDHRSMInstanceReceipt : Setω where
  field
    schema :
      Schema.MillenniumTowerSchemaReceipt

    schemaIsCanonical :
      schema ≡ Schema.canonicalMillenniumTowerSchemaReceipt

    finiteAxiomPack :
      DHR.DHRDRInternalAxiomReceiptPack

    originalDHRAuthority :
      OriginalDHR.DHROriginalPaperAuthorityReceipt

    drReconstructionAuthority :
      TensorDR.DHRDoplicherRobertsReconstructionAuthorityReceipt

    tannakaAuthority :
      Tannaka.TannakaKreinFibreFunctorReceipt

    conditionalPromotion :
      Conditional.ConditionalGDHRSMPromotionReceipt

    finitePrimeLaneAxiomsInhabited :
      Bool

    finitePrimeLaneAxiomsInhabitedIsTrue :
      finitePrimeLaneAxiomsInhabited ≡ true

    conditionalOnDRAuthorityRecorded :
      Conditional.GDHRSMPromotionStatus

    conditionalOnDRAuthorityRecordedIsCanonical :
      conditionalOnDRAuthorityRecorded
      ≡
      Conditional.conditionalOnDRAuthority

    fullGDHREqualsGSMPromoted :
      Bool

    fullGDHREqualsGSMPromotedIsFalse :
      fullGDHREqualsGSMPromoted ≡ false

    compactGaugeGroupConstructedInternally :
      Bool

    compactGaugeGroupConstructedInternallyIsFalse :
      compactGaugeGroupConstructedInternally ≡ false

    drTheoremAppliedHere :
      Bool

    drTheoremAppliedHereIsFalse :
      drTheoremAppliedHere ≡ false

    drCompactGaugeGroupConstructedHere :
      Bool

    drCompactGaugeGroupConstructedHereIsFalse :
      drCompactGaugeGroupConstructedHere ≡ false

    postCompletionConsumerRouteRecorded :
      Bool

    postCompletionConsumerRouteRecordedIsTrue :
      postCompletionConsumerRouteRecorded ≡ true

    consumerRouteShape :
      List String

    consumerRouteIsGaugeReconstructionTheorem :
      Bool

    consumerRouteIsGaugeReconstructionTheoremIsFalse :
      consumerRouteIsGaugeReconstructionTheorem ≡ false

    consumerRouteConstructsFullDHRReconstruction :
      Bool

    consumerRouteConstructsFullDHRReconstructionIsFalse :
      consumerRouteConstructsFullDHRReconstruction ≡ false

    consumerRouteIdentifiesGDHRWithGSM :
      Bool

    consumerRouteIdentifiesGDHRWithGSMIsFalse :
      consumerRouteIdentifiesGDHRWithGSM ≡ false

    instanceBoundary :
      List String

open MillenniumTowerDHRSMInstanceReceipt public

canonicalMillenniumTowerDHRSMInstanceReceipt :
  MillenniumTowerDHRSMInstanceReceipt
canonicalMillenniumTowerDHRSMInstanceReceipt =
  record
    { schema =
        Schema.canonicalMillenniumTowerSchemaReceipt
    ; schemaIsCanonical =
        refl
    ; finiteAxiomPack =
        DHR.canonicalDHRDRInternalAxiomReceiptPack
    ; originalDHRAuthority =
        OriginalDHR.canonicalDHROriginalPaperAuthorityReceipt
    ; drReconstructionAuthority =
        TensorDR.canonicalDHRDoplicherRobertsReconstructionAuthorityReceipt
    ; tannakaAuthority =
        Tannaka.canonicalTannakaKreinFibreFunctorReceipt
    ; conditionalPromotion =
        Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; finitePrimeLaneAxiomsInhabited =
        DHR.DHRDRInternalAxiomReceiptPack.allFiveInternalAxiomReceiptsTyped
          DHR.canonicalDHRDRInternalAxiomReceiptPack
    ; finitePrimeLaneAxiomsInhabitedIsTrue =
        DHR.DHRDRInternalAxiomReceiptPack.allFiveInternalAxiomReceiptsTypedIsTrue
          DHR.canonicalDHRDRInternalAxiomReceiptPack
    ; conditionalOnDRAuthorityRecorded =
        Conditional.ConditionalGDHRSMPromotionReceipt.conditionalStatus
          Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; conditionalOnDRAuthorityRecordedIsCanonical =
        Conditional.ConditionalGDHRSMPromotionReceipt.conditionalStatusIsConditionalOnDRAuthority
          Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; fullGDHREqualsGSMPromoted =
        Conditional.ConditionalGDHRSMPromotionReceipt.unconditionalGDHREqualsGSMPromoted
          Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; fullGDHREqualsGSMPromotedIsFalse =
        Conditional.ConditionalGDHRSMPromotionReceipt.unconditionalGDHREqualsGSMPromotedIsFalse
          Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; compactGaugeGroupConstructedInternally =
        Conditional.ConditionalGDHRSMPromotionReceipt.compactGaugeGroupConstructedInternally
          Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; compactGaugeGroupConstructedInternallyIsFalse =
        Conditional.ConditionalGDHRSMPromotionReceipt.compactGaugeGroupConstructedInternallyIsFalse
          Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; drTheoremAppliedHere =
        TensorDR.DHRDoplicherRobertsReconstructionAuthorityReceipt.drTheoremAppliedHere
          TensorDR.canonicalDHRDoplicherRobertsReconstructionAuthorityReceipt
    ; drTheoremAppliedHereIsFalse =
        TensorDR.DHRDoplicherRobertsReconstructionAuthorityReceipt.drTheoremAppliedHereIsFalse
          TensorDR.canonicalDHRDoplicherRobertsReconstructionAuthorityReceipt
    ; drCompactGaugeGroupConstructedHere =
        TensorDR.DHRDoplicherRobertsReconstructionAuthorityReceipt.compactGaugeGroupConstructedHere
          TensorDR.canonicalDHRDoplicherRobertsReconstructionAuthorityReceipt
    ; drCompactGaugeGroupConstructedHereIsFalse =
        TensorDR.DHRDoplicherRobertsReconstructionAuthorityReceipt.compactGaugeGroupConstructedHereIsFalse
          TensorDR.canonicalDHRDoplicherRobertsReconstructionAuthorityReceipt
    ; postCompletionConsumerRouteRecorded =
        true
    ; postCompletionConsumerRouteRecordedIsTrue =
        refl
    ; consumerRouteShape =
        "JvN polarization/Hilbert consumer"
        ∷ "C* completion consumer"
        ∷ "DHR sectors as Hilbert bimodules consumer"
        ∷ []
    ; consumerRouteIsGaugeReconstructionTheorem =
        false
    ; consumerRouteIsGaugeReconstructionTheoremIsFalse =
        refl
    ; consumerRouteConstructsFullDHRReconstruction =
        false
    ; consumerRouteConstructsFullDHRReconstructionIsFalse =
        refl
    ; consumerRouteIdentifiesGDHRWithGSM =
        false
    ; consumerRouteIdentifiesGDHRWithGSMIsFalse =
        refl
    ; instanceBoundary =
        "T0 finiteControl: finite p2/p3/p5 DHR localised-endomorphism, star, conjugate, braiding, hexagon, and statistics receipts are inhabited"
        ∷ "T1 depthFamily: the finite prime-lane carrier ledger supplies the depth-indexed sector witnesses"
        ∷ "T2 consumerShape: the post-completion consumer route is recorded explicitly as JvN -> C* completion -> DHR sectors as Hilbert bimodules"
        ∷ "T3 controlledConsumerBoundary: DHR original-paper, Doplicher-Roberts reconstruction, and Tannaka authority receipts are consumed only to record a controlled consumer route and conditionalOnDRAuthority"
        ∷ "T4 reconstructionBoundary: this file does not prove full DHR reconstruction, does not internally construct the compact gauge group, and does not apply the DR theorem in-repo"
        ∷ "T5 continuumObligation: arbitrary localized endomorphism symmetric-monoidal structure and full category-level reconstruction remain external"
        ∷ "T6 authorityBoundary: compact G_DHR construction, unconditional G_DHR ~= G_SM promotion, and any internal compact-group or gauge-reconstruction theorem remain false"
        ∷ []
    }

millenniumTowerDHRSMNoFullPromotion :
  fullGDHREqualsGSMPromoted canonicalMillenniumTowerDHRSMInstanceReceipt
  ≡
  false
millenniumTowerDHRSMNoFullPromotion =
  refl
