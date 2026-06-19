module DASHI.Physics.Closure.NSKornLevelSetHStrainDomReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Post-Calc-11 KornLevelSet / h_strain_dom receipt.
--
-- This file records the corrected package shape only.  The Calc 10/11 alpha
-- band is retained as empirical candidate evidence, the sufficient
-- h_omega_ctrl relation is recorded explicitly, and the promotion gates
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
      "h_sd = ||∂S||^2_L2(layer) >= alpha_s ||∇²u||^2_L2(layer)"

    hOmegaCtrlText :
      String
    hOmegaCtrlTextIsCanonical :
      hOmegaCtrlText ≡
      "h_omega_ctrl = ||omega||_L4(layer) <= C_omega ||S||_L4(layer)"

    alphaSRelationText :
      String
    alphaSRelationTextIsCanonical :
      alphaSRelationText ≡
      "alpha_s = 1/(1 + C_omega^2)"

    calc10AlphaRangeCandidateText :
      String
    calc10AlphaRangeCandidateTextIsCanonical :
      calc10AlphaRangeCandidateText ≡
      "Calc 10/11 empirical alpha_s≈0.5, C_omega≈1"

    noAnalyticNSProofText :
      String
    noAnalyticNSProofTextIsCanonical :
      noAnalyticNSProofText ≡
      "no analytic proof from NS"

    boundaryConclusionText :
      String
    boundaryConclusionTextIsCanonical :
      boundaryConclusionText ≡
      "∫∂C max_k B_k >= (2 alpha_s/9) ∫layer ||∇²u||²"

    packageRows :
      List String
    packageRowsIsCanonical :
      packageRows ≡
      "h_bx"
      ∷ "h_gap"
      ∷ "h_sd"
      ∷ "h_sd = ||∂S||^2_L2(layer) >= alpha_s ||∇²u||^2_L2(layer)"
      ∷ "h_omega_ctrl = ||omega||_L4(layer) <= C_omega ||S||_L4(layer)"
      ∷ "alpha_s = 1/(1 + C_omega^2)"
      ∷ "Calc 10/11 empirical alpha_s≈0.5, C_omega≈1"
      ∷ "no analytic proof from NS"
      ∷ "conditional route is publishable now only under explicit h_omega_ctrl and h_strain_dom hypotheses"
      ∷ "open route remains pressure Poisson, Calderon-Zygmund, and vorticity-strain coupling"
      ∷ "∫∂C max_k B_k >= (2 alpha_s/9) ∫layer ||∇²u||²"
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
        "h_sd = ||∂S||^2_L2(layer) >= alpha_s ||∇²u||^2_L2(layer)"
    ; correctedLayerInequalityTextIsCanonical = refl
    ; hOmegaCtrlText =
        "h_omega_ctrl = ||omega||_L4(layer) <= C_omega ||S||_L4(layer)"
    ; hOmegaCtrlTextIsCanonical = refl
    ; alphaSRelationText =
        "alpha_s = 1/(1 + C_omega^2)"
    ; alphaSRelationTextIsCanonical = refl
    ; calc10AlphaRangeCandidateText =
        "Calc 10/11 empirical alpha_s≈0.5, C_omega≈1"
    ; calc10AlphaRangeCandidateTextIsCanonical = refl
    ; noAnalyticNSProofText =
        "no analytic proof from NS"
    ; noAnalyticNSProofTextIsCanonical = refl
    ; boundaryConclusionText =
        "∫∂C max_k B_k >= (2 alpha_s/9) ∫layer ||∇²u||²"
    ; boundaryConclusionTextIsCanonical = refl
    ; packageRows =
        "h_bx"
        ∷ "h_gap"
        ∷ "h_sd"
        ∷ "h_sd = ||∂S||^2_L2(layer) >= alpha_s ||∇²u||^2_L2(layer)"
        ∷ "h_omega_ctrl = ||omega||_L4(layer) <= C_omega ||S||_L4(layer)"
        ∷ "alpha_s = 1/(1 + C_omega^2)"
        ∷ "Calc 10/11 empirical alpha_s≈0.5, C_omega≈1"
        ∷ "no analytic proof from NS"
        ∷ "conditional route is publishable now only under explicit h_omega_ctrl and h_strain_dom hypotheses"
        ∷ "open route remains pressure Poisson, Calderon-Zygmund, and vorticity-strain coupling"
        ∷ "∫∂C max_k B_k >= (2 alpha_s/9) ∫layer ||∇²u||²"
        ∷ "non-promotion gates remain explicit and closed"
        ∷ []
    ; packageRowsIsCanonical = refl
    }

data NSKornLevelSetAttackRouteStage : Set where
  pressurePoisson :
    NSKornLevelSetAttackRouteStage
  calderonZygmund :
    NSKornLevelSetAttackRouteStage
  vorticityStrainCoupling :
    NSKornLevelSetAttackRouteStage

canonicalNSKornLevelSetAttackRouteStages :
  List NSKornLevelSetAttackRouteStage
canonicalNSKornLevelSetAttackRouteStages =
  pressurePoisson
  ∷ calderonZygmund
  ∷ vorticityStrainCoupling
  ∷ []

record NSKornLevelSetConditionalRouteSurface : Set where
  field
    hOmegaCtrlHypothesisText :
      String
    hOmegaCtrlHypothesisTextIsCanonical :
      hOmegaCtrlHypothesisText ≡
      "h_omega_ctrl : ||omega||_L4(layer) <= C_omega ||S||_L4(layer)"

    hStrainDomHypothesisText :
      String
    hStrainDomHypothesisTextIsCanonical :
      hStrainDomHypothesisText ≡
      "h_strain_dom : biaxial boundary strain dominance"

    boundaryLayerOmegaControlText :
      String
    boundaryLayerOmegaControlTextIsCanonical :
      boundaryLayerOmegaControlText ≡
      "boundary layer L4 omega control by L4 strain"

    biaxialBoundaryStrainDominanceText :
      String
    biaxialBoundaryStrainDominanceTextIsCanonical :
      biaxialBoundaryStrainDominanceText ≡
      "biaxial boundary strain dominance"

    levelSetKornEstimateText :
      String
    levelSetKornEstimateTextIsCanonical :
      levelSetKornEstimateText ≡
      "boundary layer L4 omega control by L4 strain plus biaxial boundary strain dominance gives the level-set Korn estimate"

    publishableNow :
      Bool
    publishableNowIsTrue :
      publishableNow ≡ true

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

    openAttackRouteText :
      String
    openAttackRouteTextIsCanonical :
      openAttackRouteText ≡
      "open attack route: derive h_omega_ctrl from NS alone by pressure Poisson, Calderon-Zygmund, and vorticity-strain coupling"

    openAttackRouteStages :
      List NSKornLevelSetAttackRouteStage
    openAttackRouteStagesIsCanonical :
      openAttackRouteStages ≡ canonicalNSKornLevelSetAttackRouteStages

canonicalNSKornLevelSetConditionalRouteSurface :
  NSKornLevelSetConditionalRouteSurface
canonicalNSKornLevelSetConditionalRouteSurface =
  record
    { hOmegaCtrlHypothesisText =
        "h_omega_ctrl : ||omega||_L4(layer) <= C_omega ||S||_L4(layer)"
    ; hOmegaCtrlHypothesisTextIsCanonical =
        refl
    ; hStrainDomHypothesisText =
        "h_strain_dom : biaxial boundary strain dominance"
    ; hStrainDomHypothesisTextIsCanonical =
        refl
    ; boundaryLayerOmegaControlText =
        "boundary layer L4 omega control by L4 strain"
    ; boundaryLayerOmegaControlTextIsCanonical =
        refl
    ; biaxialBoundaryStrainDominanceText =
        "biaxial boundary strain dominance"
    ; biaxialBoundaryStrainDominanceTextIsCanonical =
        refl
    ; levelSetKornEstimateText =
        "boundary layer L4 omega control by L4 strain plus biaxial boundary strain dominance gives the level-set Korn estimate"
    ; levelSetKornEstimateTextIsCanonical =
        refl
    ; publishableNow =
        true
    ; publishableNowIsTrue =
        refl
    ; kornLevelSetPromoted =
        false
    ; kornLevelSetPromotedIsFalse =
        refl
    ; hStrainDomPromoted =
        false
    ; hStrainDomPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; openAttackRouteText =
        "open attack route: derive h_omega_ctrl from NS alone by pressure Poisson, Calderon-Zygmund, and vorticity-strain coupling"
    ; openAttackRouteTextIsCanonical =
        refl
    ; openAttackRouteStages =
        pressurePoisson
        ∷ calderonZygmund
        ∷ vorticityStrainCoupling
        ∷ []
    ; openAttackRouteStagesIsCanonical =
        refl
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

    conditionalRouteSurface :
      NSKornLevelSetConditionalRouteSurface
    conditionalRouteSurfaceIsCanonical :
      conditionalRouteSurface ≡
      canonicalNSKornLevelSetConditionalRouteSurface

    calc10EvidenceOnlyRecorded :
      Bool
    calc10EvidenceOnlyRecordedIsTrue :
      calc10EvidenceOnlyRecorded ≡ true

    conditionalRoutePublishableNowRecorded :
      Bool
    conditionalRoutePublishableNowRecordedIsTrue :
      conditionalRoutePublishableNowRecorded ≡ true

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
      "Post-Calc-11 KornLevelSet / h_strain_dom receipt: h_bx, h_gap, and h_sd are recorded with h_sd = ||∂S||^2_L2(layer) >= alpha_s ||∇²u||^2_L2(layer); h_omega_ctrl = ||omega||_L4(layer) <= C_omega ||S||_L4(layer) is recorded as sufficient and now sits in an explicit conditional route with h_strain_dom as a hypothesis; boundary layer L4 omega control by L4 strain plus biaxial boundary strain dominance gives the level-set Korn estimate; the open NS-alone attack route is pressure Poisson, Calderon-Zygmund, and vorticity-strain coupling; Calc 10/11 empirical alpha_s≈0.5 and C_omega≈1 remain candidate evidence only; the conclusion is ∫∂C max_k B_k >= (2 alpha_s/9) ∫layer ||∇²u||²; no analytic proof from NS, no h_strain_dom promotion, and no Clay promotion are claimed."

canonicalNSKornLevelSetHStrainDomReceipt :
  NSKornLevelSetHStrainDomReceipt
canonicalNSKornLevelSetHStrainDomReceipt =
  record
    { status = candidateOnlyFailClosed
    ; statusIsCanonical = refl
    ; proofPackageShape = canonicalNSKornLevelSetProofPackageShape
    ; proofPackageShapeIsCanonical = refl
    ; conditionalRouteSurface = canonicalNSKornLevelSetConditionalRouteSurface
    ; conditionalRouteSurfaceIsCanonical = refl
    ; calc10EvidenceOnlyRecorded = true
    ; calc10EvidenceOnlyRecordedIsTrue = refl
    ; conditionalRoutePublishableNowRecorded = true
    ; conditionalRoutePublishableNowRecordedIsTrue = refl
    ; kornLevelSetPromoted = false
    ; kornLevelSetPromotedIsFalse = refl
    ; hStrainDomPromoted = false
    ; hStrainDomPromotedIsFalse = refl
    ; clayPromoted = false
    ; clayPromotedIsFalse = refl
    ; promotionGates = canonicalNSKornLevelSetPromotionGates
    ; promotionGatesIsCanonical = refl
    ; receiptText =
        "Post-Calc-11 KornLevelSet / h_strain_dom receipt: h_bx, h_gap, and h_sd are recorded with h_sd = ||∂S||^2_L2(layer) >= alpha_s ||∇²u||^2_L2(layer); h_omega_ctrl = ||omega||_L4(layer) <= C_omega ||S||_L4(layer) is recorded as sufficient and now sits in an explicit conditional route with h_strain_dom as a hypothesis; boundary layer L4 omega control by L4 strain plus biaxial boundary strain dominance gives the level-set Korn estimate; the open NS-alone attack route is pressure Poisson, Calderon-Zygmund, and vorticity-strain coupling; Calc 10/11 empirical alpha_s≈0.5 and C_omega≈1 remain candidate evidence only; the conclusion is ∫∂C max_k B_k >= (2 alpha_s/9) ∫layer ||∇²u||²; no analytic proof from NS, no h_strain_dom promotion, and no Clay promotion are claimed."
    ; receiptTextIsCanonical = refl
    }

open NSKornLevelSetConditionalRouteSurface public
open NSKornLevelSetProofPackageShape public
open NSKornLevelSetHStrainDomReceipt public
