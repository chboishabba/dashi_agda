module DASHI.Physics.Closure.NSFlowMDLAdmissibilityCandidateReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSCarrierKolmogorovSerrinReceipt as Carrier
import DASHI.Physics.Closure.NSViscousTailDominanceReceipt as Tail

------------------------------------------------------------------------
-- Navier-Stokes flow / MDL admissibility candidate receipt.
--
-- This records the bridge suggested by TailCollapse/MDL shift machinery
-- and the two existing Navier-Stokes receipts.  It is deliberately a
-- candidate and conditional receipt.  The missing forward estimate is
-- active-depth/tail control for the actual NS evolution; no Clay or global
-- regularity claim is promoted here.

data NSFlowMDLBridgeStatus : Set where
  candidateConditional_missingForwardEstimate_claySeparate :
    NSFlowMDLBridgeStatus

data NSFlowMDLBridgeComponent : Set where
  tailCollapseShiftInstance :
    NSFlowMDLBridgeComponent

  mdlTradeoffShiftInstance :
    NSFlowMDLBridgeComponent

  viscousTailDominanceInput :
    NSFlowMDLBridgeComponent

  carrierKolmogorovSerrinBoundaryInput :
    NSFlowMDLBridgeComponent

  activeDepthForwardEstimateGap :
    NSFlowMDLBridgeComponent

  admissibilityAboveViscousCrossoverCandidate :
    NSFlowMDLBridgeComponent

canonicalNSFlowMDLBridgeComponents :
  List NSFlowMDLBridgeComponent
canonicalNSFlowMDLBridgeComponents =
  tailCollapseShiftInstance
  ∷ mdlTradeoffShiftInstance
  ∷ viscousTailDominanceInput
  ∷ carrierKolmogorovSerrinBoundaryInput
  ∷ activeDepthForwardEstimateGap
  ∷ admissibilityAboveViscousCrossoverCandidate
  ∷ []

data NSFlowMDLProofObligation : Set where
  defineNSCarrierFlowOnProjectionGrades :
    NSFlowMDLProofObligation

  proveForwardActiveDepthTailControl :
    NSFlowMDLProofObligation

  relateViscousDominanceToMDLResidualDrop :
    NSFlowMDLProofObligation

  proveAdmissibilityAtAndAboveKStarNu :
    NSFlowMDLProofObligation

  proveProjectionStabilityForNonlinearCascade :
    NSFlowMDLProofObligation

  transferFiniteDepthCarrierBoundToSerrin :
    NSFlowMDLProofObligation

  stateBoundaryAgainstClayPromotion :
    NSFlowMDLProofObligation

canonicalNSFlowMDLProofObligations :
  List NSFlowMDLProofObligation
canonicalNSFlowMDLProofObligations =
  defineNSCarrierFlowOnProjectionGrades
  ∷ proveForwardActiveDepthTailControl
  ∷ relateViscousDominanceToMDLResidualDrop
  ∷ proveAdmissibilityAtAndAboveKStarNu
  ∷ proveProjectionStabilityForNonlinearCascade
  ∷ transferFiniteDepthCarrierBoundToSerrin
  ∷ stateBoundaryAgainstClayPromotion
  ∷ []

data MissingForwardEstimate : Set where
  activeDepthTailControlForNSEvolution :
    MissingForwardEstimate

data PromotionToken : Set where

promotionImpossibleHere :
  PromotionToken →
  ⊥
promotionImpossibleHere ()

missingForwardEstimateStatement :
  String
missingForwardEstimateStatement =
  "The missing forward estimate is active-depth/tail control for the actual Navier-Stokes evolution, not the finite tail-collapse algebra itself."

viscosityMDLDominanceStatement :
  String
viscosityMDLDominanceStatement =
  "Conditional on viscous dominance above K*(nu), the MDL shift picture suggests tail description length decreases for carrier depths k >= K*(nu)."

candidateBridgeStatement :
  String
candidateBridgeStatement =
  "NSFlowMDLAdmissibility is a candidate bridge: admissibility at projection grade K should follow from viscous dominance plus a forward active-depth estimate."

proofObligationStatement :
  String
proofObligationStatement =
  "The receipt lists obligations; it does not discharge the Navier-Stokes forward estimate or prove global regularity."

boundaryStatement :
  String
boundaryStatement =
  "Candidate and conditional only: this is not a Clay Navier-Stokes solution, not a universal regularity theorem, and not a blow-up criterion."

carrierKolmogorovSerrinReceiptModule :
  String
carrierKolmogorovSerrinReceiptModule =
  "DASHI.Physics.Closure.NSCarrierKolmogorovSerrinReceipt"

record NSFlowMDLAdmissibilityCandidateReceipt : Set where
  field
    status :
      NSFlowMDLBridgeStatus

    statusIsCandidateConditional :
      status ≡ candidateConditional_missingForwardEstimate_claySeparate

    sourceViscousTailDominanceReceipt :
      Tail.NSViscousTailDominanceReceipt

    sourceViscousTailDominanceIsCanonical :
      sourceViscousTailDominanceReceipt ≡ Tail.canonicalNSViscousTailDominanceReceipt

    sourceCarrierKolmogorovSerrinReceipt :
      String

    sourceCarrierKolmogorovSerrinIsCanonical :
      sourceCarrierKolmogorovSerrinReceipt ≡ carrierKolmogorovSerrinReceiptModule

    components :
      List NSFlowMDLBridgeComponent

    componentsAreCanonical :
      components ≡ canonicalNSFlowMDLBridgeComponents

    missingForwardEstimate :
      MissingForwardEstimate

    missingForwardEstimateIsActiveDepthTailControl :
      missingForwardEstimate ≡ activeDepthTailControlForNSEvolution

    missingForwardEstimateSummary :
      String

    missingForwardEstimateSummaryIsCanonical :
      missingForwardEstimateSummary ≡ missingForwardEstimateStatement

    viscosityMDLDominanceSummary :
      String

    viscosityMDLDominanceSummaryIsCanonical :
      viscosityMDLDominanceSummary ≡ viscosityMDLDominanceStatement

    candidateBridgeSummary :
      String

    candidateBridgeSummaryIsCanonical :
      candidateBridgeSummary ≡ candidateBridgeStatement

    proofObligations :
      List NSFlowMDLProofObligation

    proofObligationsAreCanonical :
      proofObligations ≡ canonicalNSFlowMDLProofObligations

    proofObligationSummary :
      String

    proofObligationSummaryIsCanonical :
      proofObligationSummary ≡ proofObligationStatement

    candidateReceipt :
      Bool

    candidateReceiptIsTrue :
      candidateReceipt ≡ true

    conditionalOnForwardEstimate :
      Bool

    conditionalOnForwardEstimateIsTrue :
      conditionalOnForwardEstimate ≡ true

    activeDepthTailControlProvedHere :
      Bool

    activeDepthTailControlProvedHereIsFalse :
      activeDepthTailControlProvedHere ≡ false

    mdlTailDescriptionLengthDropProvedHere :
      Bool

    mdlTailDescriptionLengthDropProvedHereIsFalse :
      mdlTailDescriptionLengthDropProvedHere ≡ false

    mdlTailDescriptionLengthDropSuggestedAboveKStarNu :
      Bool

    mdlTailDescriptionLengthDropSuggestedAboveKStarNuIsTrue :
      mdlTailDescriptionLengthDropSuggestedAboveKStarNu ≡ true

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    unboundedDepthImpliesBlowup :
      Bool

    unboundedDepthImpliesBlowupIsFalse :
      unboundedDepthImpliesBlowup ≡ false

    promotionFlags :
      List PromotionToken

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ boundaryStatement

open NSFlowMDLAdmissibilityCandidateReceipt public

canonicalNSFlowMDLAdmissibilityCandidateReceipt :
  NSFlowMDLAdmissibilityCandidateReceipt
canonicalNSFlowMDLAdmissibilityCandidateReceipt =
  record
    { status =
        candidateConditional_missingForwardEstimate_claySeparate
    ; statusIsCandidateConditional =
        refl
    ; sourceViscousTailDominanceReceipt =
        Tail.canonicalNSViscousTailDominanceReceipt
    ; sourceViscousTailDominanceIsCanonical =
        refl
    ; sourceCarrierKolmogorovSerrinReceipt =
        carrierKolmogorovSerrinReceiptModule
    ; sourceCarrierKolmogorovSerrinIsCanonical =
        refl
    ; components =
        canonicalNSFlowMDLBridgeComponents
    ; componentsAreCanonical =
        refl
    ; missingForwardEstimate =
        activeDepthTailControlForNSEvolution
    ; missingForwardEstimateIsActiveDepthTailControl =
        refl
    ; missingForwardEstimateSummary =
        missingForwardEstimateStatement
    ; missingForwardEstimateSummaryIsCanonical =
        refl
    ; viscosityMDLDominanceSummary =
        viscosityMDLDominanceStatement
    ; viscosityMDLDominanceSummaryIsCanonical =
        refl
    ; candidateBridgeSummary =
        candidateBridgeStatement
    ; candidateBridgeSummaryIsCanonical =
        refl
    ; proofObligations =
        canonicalNSFlowMDLProofObligations
    ; proofObligationsAreCanonical =
        refl
    ; proofObligationSummary =
        proofObligationStatement
    ; proofObligationSummaryIsCanonical =
        refl
    ; candidateReceipt =
        true
    ; candidateReceiptIsTrue =
        refl
    ; conditionalOnForwardEstimate =
        true
    ; conditionalOnForwardEstimateIsTrue =
        refl
    ; activeDepthTailControlProvedHere =
        false
    ; activeDepthTailControlProvedHereIsFalse =
        refl
    ; mdlTailDescriptionLengthDropProvedHere =
        false
    ; mdlTailDescriptionLengthDropProvedHereIsFalse =
        refl
    ; mdlTailDescriptionLengthDropSuggestedAboveKStarNu =
        true
    ; mdlTailDescriptionLengthDropSuggestedAboveKStarNuIsTrue =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; unboundedDepthImpliesBlowup =
        false
    ; unboundedDepthImpliesBlowupIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        boundaryStatement
    ; receiptBoundaryIsCanonical =
        refl
    }

nsFlowMDLBridgeIsCandidate :
  candidateReceipt canonicalNSFlowMDLAdmissibilityCandidateReceipt ≡ true
nsFlowMDLBridgeIsCandidate =
  refl

nsFlowMDLBridgeMissingForwardEstimate :
  activeDepthTailControlProvedHere canonicalNSFlowMDLAdmissibilityCandidateReceipt ≡ false
nsFlowMDLBridgeMissingForwardEstimate =
  refl

nsFlowMDLBridgeSuggestsMDLDropAboveKStar :
  mdlTailDescriptionLengthDropSuggestedAboveKStarNu canonicalNSFlowMDLAdmissibilityCandidateReceipt ≡ true
nsFlowMDLBridgeSuggestsMDLDropAboveKStar =
  refl

nsFlowMDLBridgeNoClayPromotion :
  clayNavierStokesPromoted canonicalNSFlowMDLAdmissibilityCandidateReceipt ≡ false
nsFlowMDLBridgeNoClayPromotion =
  refl
