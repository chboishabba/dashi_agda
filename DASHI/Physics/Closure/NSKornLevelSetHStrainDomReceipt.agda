module DASHI.Physics.Closure.NSKornLevelSetHStrainDomReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Post-Calc-10 KornLevelSet / h_strain_dom receipt.
--
-- This file records the corrected package shape only.  The Calc 10 alpha
-- band is retained as empirical candidate evidence, and the promotion gates
-- remain explicitly blocked.

data NSKornLevelSetReceiptStatus : Set where
  candidateOnlyFailClosed :
    NSKornLevelSetReceiptStatus

data NSKornLevelSetPromotionGate : Set where
  noAnalyticKornLevelSetProof :
    NSKornLevelSetPromotionGate
  calc10EvidenceOnly :
    NSKornLevelSetPromotionGate
  noHStrainDomPromotion :
    NSKornLevelSetPromotionGate
  noClayPromotion :
    NSKornLevelSetPromotionGate
  noTheoremCollapse :
    NSKornLevelSetPromotionGate

canonicalNSKornLevelSetPromotionGates :
  List NSKornLevelSetPromotionGate
canonicalNSKornLevelSetPromotionGates =
  noAnalyticKornLevelSetProof
  ∷ calc10EvidenceOnly
  ∷ noHStrainDomPromotion
  ∷ noClayPromotion
  ∷ noTheoremCollapse
  ∷ []

record NSKornLevelSetProofPackageShape : Set where
  field
    h_bxRowName :
      String
    h_bxRowNameIsCanonical :
      h_bxRowName ≡ "h_bx"

    h_gapRowName :
      String
    h_gapRowNameIsCanonical :
      h_gapRowName ≡ "h_gap"

    h_sdRowName :
      String
    h_sdRowNameIsCanonical :
      h_sdRowName ≡ "h_sd"

    correctedLayerInequalityText :
      String
    correctedLayerInequalityTextIsCanonical :
      correctedLayerInequalityText ≡
      "||∂S||²_layer >= alpha_s * ||∇²u||²_layer"

    calc10AlphaRangeCandidateText :
      String
    calc10AlphaRangeCandidateTextIsCanonical :
      calc10AlphaRangeCandidateText ≡
      "Calc 10 empirical alpha range only: alpha_s in [0.49648633477014364, 0.49956437854373653]"

    boundaryConclusionText :
      String
    boundaryConclusionTextIsCanonical :
      boundaryConclusionText ≡
      "integral boundary max B_k >= (2*alpha_s/9)*layer denominator"

    packageRows :
      List String
    packageRowsIsCanonical :
      packageRows ≡
      "h_bx"
      ∷ "h_gap"
      ∷ "h_sd"
      ∷ "||∂S||²_layer >= alpha_s * ||∇²u||²_layer"
      ∷ "Calc 10 empirical alpha range only: alpha_s in [0.49648633477014364, 0.49956437854373653]"
      ∷ "integral boundary max B_k >= (2*alpha_s/9)*layer denominator"
      ∷ "non-promotion gates remain explicit and closed"
      ∷ []

canonicalNSKornLevelSetProofPackageShape :
  NSKornLevelSetProofPackageShape
canonicalNSKornLevelSetProofPackageShape =
  record
    { h_bxRowName = "h_bx"
    ; h_bxRowNameIsCanonical = refl
    ; h_gapRowName = "h_gap"
    ; h_gapRowNameIsCanonical = refl
    ; h_sdRowName = "h_sd"
    ; h_sdRowNameIsCanonical = refl
    ; correctedLayerInequalityText =
        "||∂S||²_layer >= alpha_s * ||∇²u||²_layer"
    ; correctedLayerInequalityTextIsCanonical = refl
    ; calc10AlphaRangeCandidateText =
        "Calc 10 empirical alpha range only: alpha_s in [0.49648633477014364, 0.49956437854373653]"
    ; calc10AlphaRangeCandidateTextIsCanonical = refl
    ; boundaryConclusionText =
        "integral boundary max B_k >= (2*alpha_s/9)*layer denominator"
    ; boundaryConclusionTextIsCanonical = refl
    ; packageRows =
        "h_bx"
        ∷ "h_gap"
        ∷ "h_sd"
        ∷ "||∂S||²_layer >= alpha_s * ||∇²u||²_layer"
        ∷ "Calc 10 empirical alpha range only: alpha_s in [0.49648633477014364, 0.49956437854373653]"
        ∷ "integral boundary max B_k >= (2*alpha_s/9)*layer denominator"
        ∷ "non-promotion gates remain explicit and closed"
        ∷ []
    ; packageRowsIsCanonical = refl
    }

record NSKornLevelSetHStrainDomReceipt : Set where
  field
    status :
      NSKornLevelSetReceiptStatus
    statusIsCanonical :
      status ≡ candidateOnlyFailClosed

    proofPackageShape :
      NSKornLevelSetProofPackageShape
    proofPackageShapeIsCanonical :
      proofPackageShape ≡ canonicalNSKornLevelSetProofPackageShape

    calc10EvidenceOnlyRecorded :
      Bool
    calc10EvidenceOnlyRecordedIsTrue :
      calc10EvidenceOnlyRecorded ≡ true

    kornLevelSetPromoted :
      Bool
    kornLevelSetPromotedIsFalse :
      kornLevelSetPromoted ≡ false

    hStrainDomPromoted :
      Bool
    hStrainDomPromotedIsFalse :
      hStrainDomPromoted ≡ false

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotionGates :
      List NSKornLevelSetPromotionGate
    promotionGatesIsCanonical :
      promotionGates ≡ canonicalNSKornLevelSetPromotionGates

    receiptText :
      String
    receiptTextIsCanonical :
      receiptText ≡
      "Post-Calc-10 KornLevelSet / h_strain_dom receipt: h_bx, h_gap, and h_sd are recorded with the corrected layer inequality ||∂S||²_layer >= alpha_s * ||∇²u||²_layer; Calc 10 alpha_s in [0.49648633477014364, 0.49956437854373653] is candidate evidence only; the conclusion is integral boundary max B_k >= (2*alpha_s/9)*layer denominator; no analytic KornLevelSet proof, no h_strain_dom promotion, and no Clay promotion are claimed."

canonicalNSKornLevelSetHStrainDomReceipt :
  NSKornLevelSetHStrainDomReceipt
canonicalNSKornLevelSetHStrainDomReceipt =
  record
    { status = candidateOnlyFailClosed
    ; statusIsCanonical = refl
    ; proofPackageShape = canonicalNSKornLevelSetProofPackageShape
    ; proofPackageShapeIsCanonical = refl
    ; calc10EvidenceOnlyRecorded = true
    ; calc10EvidenceOnlyRecordedIsTrue = refl
    ; kornLevelSetPromoted = false
    ; kornLevelSetPromotedIsFalse = refl
    ; hStrainDomPromoted = false
    ; hStrainDomPromotedIsFalse = refl
    ; clayPromoted = false
    ; clayPromotedIsFalse = refl
    ; promotionGates = canonicalNSKornLevelSetPromotionGates
    ; promotionGatesIsCanonical = refl
    ; receiptText =
        "Post-Calc-10 KornLevelSet / h_strain_dom receipt: h_bx, h_gap, and h_sd are recorded with the corrected layer inequality ||∂S||²_layer >= alpha_s * ||∇²u||²_layer; Calc 10 alpha_s in [0.49648633477014364, 0.49956437854373653] is candidate evidence only; the conclusion is integral boundary max B_k >= (2*alpha_s/9)*layer denominator; no analytic KornLevelSet proof, no h_strain_dom promotion, and no Clay promotion are claimed."
    ; receiptTextIsCanonical = refl
    }

open NSKornLevelSetProofPackageShape public
open NSKornLevelSetHStrainDomReceipt public
