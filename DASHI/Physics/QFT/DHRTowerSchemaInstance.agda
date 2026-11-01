module DASHI.Physics.QFT.DHRTowerSchemaInstance where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MillenniumTowerSchemaReceipt as Schema
import DASHI.Physics.QFT.ConditionalGDHRSMPromotionReceipt as Conditional
import DASHI.Physics.QFT.DHRGaugeReceiptSurface as DHR
import DASHI.Physics.QFT.DHROriginalPaperAuthorityReceipt as OriginalDHR
import DASHI.Physics.QFT.TannakaKreinFibreFunctorReceipt as Tannaka

------------------------------------------------------------------------
-- DHR/QFT instance of the shared tower schema.
--
-- This adapter maps finite DHR axioms, original DHR/DR authority,
-- Tannaka-Krein fibre-functor authority, and the conditional G_DHR/SM
-- receipt into the common schema.  The conditional authority boundary is
-- recorded, while the full G_DHR ~= G_SM promotion remains false.

data DHRTowerSchemaInstanceStatus : Set where
  dhrFiniteAxiomsAuthorityConditionalMappedFullSMFalse :
    DHRTowerSchemaInstanceStatus

record DHRTowerSchemaInstance : Setω where
  field
    status :
      DHRTowerSchemaInstanceStatus

    schemaReceipt :
      Schema.MillenniumTowerSchemaReceipt

    schemaReceiptIsCanonical :
      schemaReceipt ≡ Schema.canonicalMillenniumTowerSchemaReceipt

    schemaFullUnificationIsFalse :
      Schema.fullUnification schemaReceipt ≡ false

    finiteDHRInternalAxiomPackSelectedCanonical :
      Bool

    finiteDHRInternalAxiomPackSelectedCanonicalIsTrue :
      finiteDHRInternalAxiomPackSelectedCanonical ≡ true

    allFiveFiniteAxiomReceiptsTyped :
      DHR.DHRDRInternalAxiomReceiptPack.allFiveInternalAxiomReceiptsTyped
        DHR.canonicalDHRDRInternalAxiomReceiptPack
      ≡
      true

    dhrGaugeReconstructionHereIsFalse :
      DHR.DHRDRInternalAxiomReceiptPack.reconstructsGaugeGroupHere
        DHR.canonicalDHRDRInternalAxiomReceiptPack
      ≡
      false

    originalDHRAuthoritySelectedCanonical :
      Bool

    originalDHRAuthoritySelectedCanonicalIsTrue :
      originalDHRAuthoritySelectedCanonical ≡ true

    originalDHRAuthorityRecorded :
      OriginalDHR.DHROriginalPaperAuthorityReceipt.dhrOriginalAuthorityRecorded
        OriginalDHR.canonicalDHROriginalPaperAuthorityReceipt
      ≡
      true

    originalDHRTheoremAppliedHereIsFalse :
      OriginalDHR.DHROriginalPaperAuthorityReceipt.theoremAppliedHere
        OriginalDHR.canonicalDHROriginalPaperAuthorityReceipt
      ≡
      false

    originalDHRStandardModelMatchingPromotedIsFalse :
      OriginalDHR.DHROriginalPaperAuthorityReceipt.standardModelMatchingPromoted
        OriginalDHR.canonicalDHROriginalPaperAuthorityReceipt
      ≡
      false

    tannakaFibreFunctorAuthoritySelectedCanonical :
      Bool

    tannakaFibreFunctorAuthoritySelectedCanonicalIsTrue :
      tannakaFibreFunctorAuthoritySelectedCanonical ≡ true

    tannakaFiniteFibreFunctorRecorded :
      Tannaka.TannakaKreinFibreFunctorReceipt.finiteFibreFunctorRecorded
        Tannaka.canonicalTannakaKreinFibreFunctorReceipt
      ≡
      true

    tannakaDualGroupConstructedIsFalse :
      Tannaka.TannakaKreinFibreFunctorReceipt.tannakaDualGroupConstructed
        Tannaka.canonicalTannakaKreinFibreFunctorReceipt
      ≡
      false

    tannakaGDHREqualsSMGaugePromotedIsFalse :
      Tannaka.TannakaKreinFibreFunctorReceipt.gDHREqualsSMGaugePromoted
        Tannaka.canonicalTannakaKreinFibreFunctorReceipt
      ≡
      false

    conditionalGDHRSMPromotionSelectedCanonical :
      Bool

    conditionalGDHRSMPromotionSelectedCanonicalIsTrue :
      conditionalGDHRSMPromotionSelectedCanonical ≡ true

    conditionalStatusIsConditionalOnDRAuthority :
      Conditional.ConditionalGDHRSMPromotionReceipt.conditionalStatus
        Conditional.canonicalConditionalGDHRSMPromotionReceipt
      ≡
      Conditional.conditionalOnDRAuthority

    unconditionalGDHREqualsGSMPromotedIsFalse :
      Conditional.ConditionalGDHRSMPromotionReceipt.unconditionalGDHREqualsGSMPromoted
        Conditional.canonicalConditionalGDHRSMPromotionReceipt
      ≡
      false

    fullTheoremInRepoClaimedIsFalse :
      Conditional.ConditionalGDHRSMPromotionReceipt.fullTheoremInRepoClaimed
        Conditional.canonicalConditionalGDHRSMPromotionReceipt
      ≡
      false

    fullGDHREqualsGSMPromoted :
      Bool

    fullGDHREqualsGSMPromotedIsFalse :
      fullGDHREqualsGSMPromoted ≡ false

    mappingBoundary :
      List String

open DHRTowerSchemaInstance public

canonicalDHRTowerSchemaInstance :
  DHRTowerSchemaInstance
canonicalDHRTowerSchemaInstance =
  record
    { status =
        dhrFiniteAxiomsAuthorityConditionalMappedFullSMFalse
    ; schemaReceipt =
        Schema.canonicalMillenniumTowerSchemaReceipt
    ; schemaReceiptIsCanonical =
        refl
    ; schemaFullUnificationIsFalse =
        refl
    ; finiteDHRInternalAxiomPackSelectedCanonical =
        true
    ; finiteDHRInternalAxiomPackSelectedCanonicalIsTrue =
        refl
    ; allFiveFiniteAxiomReceiptsTyped =
        DHR.DHRDRInternalAxiomReceiptPack.allFiveInternalAxiomReceiptsTypedIsTrue
          DHR.canonicalDHRDRInternalAxiomReceiptPack
    ; dhrGaugeReconstructionHereIsFalse =
        DHR.DHRDRInternalAxiomReceiptPack.reconstructsGaugeGroupHereIsFalse
          DHR.canonicalDHRDRInternalAxiomReceiptPack
    ; originalDHRAuthoritySelectedCanonical =
        true
    ; originalDHRAuthoritySelectedCanonicalIsTrue =
        refl
    ; originalDHRAuthorityRecorded =
        OriginalDHR.DHROriginalPaperAuthorityReceipt.dhrOriginalAuthorityRecordedIsTrue
          OriginalDHR.canonicalDHROriginalPaperAuthorityReceipt
    ; originalDHRTheoremAppliedHereIsFalse =
        OriginalDHR.DHROriginalPaperAuthorityReceipt.theoremAppliedHereIsFalse
          OriginalDHR.canonicalDHROriginalPaperAuthorityReceipt
    ; originalDHRStandardModelMatchingPromotedIsFalse =
        OriginalDHR.canonicalDHROriginalAuthorityStillFailClosedForSM
    ; tannakaFibreFunctorAuthoritySelectedCanonical =
        true
    ; tannakaFibreFunctorAuthoritySelectedCanonicalIsTrue =
        refl
    ; tannakaFiniteFibreFunctorRecorded =
        Tannaka.tannakaKreinFiniteFibreFunctorRecorded
    ; tannakaDualGroupConstructedIsFalse =
        Tannaka.tannakaKreinDualGroupNotConstructed
    ; tannakaGDHREqualsSMGaugePromotedIsFalse =
        refl
    ; conditionalGDHRSMPromotionSelectedCanonical =
        true
    ; conditionalGDHRSMPromotionSelectedCanonicalIsTrue =
        refl
    ; conditionalStatusIsConditionalOnDRAuthority =
        Conditional.canonicalConditionalGDHRSMPromotionStatus
    ; unconditionalGDHREqualsGSMPromotedIsFalse =
        refl
    ; fullTheoremInRepoClaimedIsFalse =
        Conditional.canonicalConditionalGDHRSMPromotionNoFullTheorem
    ; fullGDHREqualsGSMPromoted =
        false
    ; fullGDHREqualsGSMPromotedIsFalse =
        refl
    ; mappingBoundary =
        "Finite DHR/DR internal axiom receipts are consumed as the finite p2/p3/p5 axiom pack"
        ∷ "Original DHR authority and Tannaka-Krein fibre-functor authority are recorded as authority boundaries"
        ∷ "The conditional G_DHR/SM receipt is threaded with status conditionalOnDRAuthority"
        ∷ "No internal compact gauge group construction, full theorem-in-repo token, full G_DHR ~= G_SM promotion, or schema full-unification promotion is introduced"
        ∷ []
    }

dhrTowerSchemaFullGDHREqualsGSMFalse :
  fullGDHREqualsGSMPromoted canonicalDHRTowerSchemaInstance
  ≡
  false
dhrTowerSchemaFullGDHREqualsGSMFalse =
  refl
