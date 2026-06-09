module DASHI.Physics.Closure.CKMBetaAlphaDemotionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- CKM beta/alpha demotion receipt.
--
-- Beta is only downstream of the current |Vub| estimate and gamma.  Since
-- gamma remains ungrounded and |Vub| is only a leading-order estimate, beta
-- inherits both uncertainties.  Alpha is the complement alpha = pi - beta -
-- gamma and has no independent carrier input, so it is a tautological
-- consequence rather than a prediction.

data CKMBetaDemotionStatus : Set where
  inheritsDMinus7Uncertainty :
    CKMBetaDemotionStatus

data CKMAlphaDemotionStatus : Set where
  tautologicalConsequence :
    CKMAlphaDemotionStatus

data CKMBetaDependency : Set where
  vubLeadingOrderEstimate :
    CKMBetaDependency

  gammaUngroundedDMinus7Input :
    CKMBetaDependency

canonicalBetaDependencies :
  List CKMBetaDependency
canonicalBetaDependencies =
  vubLeadingOrderEstimate
  ∷ gammaUngroundedDMinus7Input
  ∷ []

data CKMBetaAlphaBlocker : Set where
  betaDependsOnLeadingOrderVub :
    CKMBetaAlphaBlocker

  betaDependsOnUngroundedGamma :
    CKMBetaAlphaBlocker

  alphaHasNoIndependentCarrierInput :
    CKMBetaAlphaBlocker

  alphaOnlyRestatesTriangleClosure :
    CKMBetaAlphaBlocker

canonicalBetaAlphaBlockers :
  List CKMBetaAlphaBlocker
canonicalBetaAlphaBlockers =
  betaDependsOnLeadingOrderVub
  ∷ betaDependsOnUngroundedGamma
  ∷ alphaHasNoIndependentCarrierInput
  ∷ alphaOnlyRestatesTriangleClosure
  ∷ []

data CKMBetaAlphaPromotion : Set where

ckmBetaAlphaPromotionImpossibleHere :
  CKMBetaAlphaPromotion →
  ⊥
ckmBetaAlphaPromotionImpossibleHere ()

betaFormulaLabel : String
betaFormulaLabel =
  "beta = downstream function of |Vub| and gamma"

vubUncertaintyLabel : String
vubUncertaintyLabel =
  "|Vub| is retained only as a leading-order estimate"

gammaUncertaintyLabel : String
gammaUncertaintyLabel =
  "gamma is ungrounded at the D=-7 carrier input"

alphaFormulaLabel : String
alphaFormulaLabel =
  "alpha = pi - beta - gamma"

alphaBoundaryLabel : String
alphaBoundaryLabel =
  "alpha has no independent carrier input and is not a prediction"

canonicalReceiptBoundary :
  List String
canonicalReceiptBoundary =
  betaFormulaLabel
  ∷ vubUncertaintyLabel
  ∷ gammaUncertaintyLabel
  ∷ "betaStatus = inheritsDMinus7Uncertainty"
  ∷ alphaFormulaLabel
  ∷ "alphaStatus = tautologicalConsequence"
  ∷ "alphaIsNotAPrediction = true"
  ∷ "Neither beta nor alpha can be elevated from the current sources"
  ∷ []

record CKMBetaAlphaDemotionReceipt : Setω where
  field
    betaStatus :
      CKMBetaDemotionStatus

    betaStatusIsInheritsDMinus7Uncertainty :
      betaStatus ≡ inheritsDMinus7Uncertainty

    betaFormula :
      String

    betaFormulaIsDownstreamFunction :
      betaFormula ≡ betaFormulaLabel

    betaDependsOnVub :
      Bool

    betaDependsOnVubIsTrue :
      betaDependsOnVub ≡ true

    vubIsLeadingOrderEstimateOnly :
      Bool

    vubIsLeadingOrderEstimateOnlyIsTrue :
      vubIsLeadingOrderEstimateOnly ≡ true

    vubUncertaintySummary :
      String

    vubUncertaintySummaryIsCanonical :
      vubUncertaintySummary ≡ vubUncertaintyLabel

    betaDependsOnGamma :
      Bool

    betaDependsOnGammaIsTrue :
      betaDependsOnGamma ≡ true

    gammaIsUngrounded :
      Bool

    gammaIsUngroundedIsTrue :
      gammaIsUngrounded ≡ true

    gammaUncertaintySummary :
      String

    gammaUncertaintySummaryIsCanonical :
      gammaUncertaintySummary ≡ gammaUncertaintyLabel

    betaDependencies :
      List CKMBetaDependency

    betaDependenciesAreCanonical :
      betaDependencies ≡ canonicalBetaDependencies

    betaInheritsVubUncertainty :
      Bool

    betaInheritsVubUncertaintyIsTrue :
      betaInheritsVubUncertainty ≡ true

    betaInheritsGammaUncertainty :
      Bool

    betaInheritsGammaUncertaintyIsTrue :
      betaInheritsGammaUncertainty ≡ true

    betaCanBeElevatedFromSources :
      Bool

    betaCanBeElevatedFromSourcesIsFalse :
      betaCanBeElevatedFromSources ≡ false

    alphaStatus :
      CKMAlphaDemotionStatus

    alphaStatusIsTautologicalConsequence :
      alphaStatus ≡ tautologicalConsequence

    alphaFormula :
      String

    alphaFormulaIsTriangleComplement :
      alphaFormula ≡ alphaFormulaLabel

    alphaHasIndependentCarrierInput :
      Bool

    alphaHasIndependentCarrierInputIsFalse :
      alphaHasIndependentCarrierInput ≡ false

    alphaIsNotAPrediction :
      Bool

    alphaIsNotAPredictionIsTrue :
      alphaIsNotAPrediction ≡ true

    alphaBoundarySummary :
      String

    alphaBoundarySummaryIsCanonical :
      alphaBoundarySummary ≡ alphaBoundaryLabel

    alphaCanBeElevatedFromSources :
      Bool

    alphaCanBeElevatedFromSourcesIsFalse :
      alphaCanBeElevatedFromSources ≡ false

    blockers :
      List CKMBetaAlphaBlocker

    blockersAreCanonical :
      blockers ≡ canonicalBetaAlphaBlockers

    promotionFlags :
      List CKMBetaAlphaPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalReceiptBoundary

open CKMBetaAlphaDemotionReceipt public

canonicalCKMBetaAlphaDemotionReceipt :
  CKMBetaAlphaDemotionReceipt
canonicalCKMBetaAlphaDemotionReceipt =
  record
    { betaStatus =
        inheritsDMinus7Uncertainty
    ; betaStatusIsInheritsDMinus7Uncertainty =
        refl
    ; betaFormula =
        betaFormulaLabel
    ; betaFormulaIsDownstreamFunction =
        refl
    ; betaDependsOnVub =
        true
    ; betaDependsOnVubIsTrue =
        refl
    ; vubIsLeadingOrderEstimateOnly =
        true
    ; vubIsLeadingOrderEstimateOnlyIsTrue =
        refl
    ; vubUncertaintySummary =
        vubUncertaintyLabel
    ; vubUncertaintySummaryIsCanonical =
        refl
    ; betaDependsOnGamma =
        true
    ; betaDependsOnGammaIsTrue =
        refl
    ; gammaIsUngrounded =
        true
    ; gammaIsUngroundedIsTrue =
        refl
    ; gammaUncertaintySummary =
        gammaUncertaintyLabel
    ; gammaUncertaintySummaryIsCanonical =
        refl
    ; betaDependencies =
        canonicalBetaDependencies
    ; betaDependenciesAreCanonical =
        refl
    ; betaInheritsVubUncertainty =
        true
    ; betaInheritsVubUncertaintyIsTrue =
        refl
    ; betaInheritsGammaUncertainty =
        true
    ; betaInheritsGammaUncertaintyIsTrue =
        refl
    ; betaCanBeElevatedFromSources =
        false
    ; betaCanBeElevatedFromSourcesIsFalse =
        refl
    ; alphaStatus =
        tautologicalConsequence
    ; alphaStatusIsTautologicalConsequence =
        refl
    ; alphaFormula =
        alphaFormulaLabel
    ; alphaFormulaIsTriangleComplement =
        refl
    ; alphaHasIndependentCarrierInput =
        false
    ; alphaHasIndependentCarrierInputIsFalse =
        refl
    ; alphaIsNotAPrediction =
        true
    ; alphaIsNotAPredictionIsTrue =
        refl
    ; alphaBoundarySummary =
        alphaBoundaryLabel
    ; alphaBoundarySummaryIsCanonical =
        refl
    ; alphaCanBeElevatedFromSources =
        false
    ; alphaCanBeElevatedFromSourcesIsFalse =
        refl
    ; blockers =
        canonicalBetaAlphaBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        canonicalReceiptBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

canonicalBetaStatus :
  betaStatus canonicalCKMBetaAlphaDemotionReceipt
  ≡
  inheritsDMinus7Uncertainty
canonicalBetaStatus =
  refl

canonicalAlphaStatus :
  alphaStatus canonicalCKMBetaAlphaDemotionReceipt
  ≡
  tautologicalConsequence
canonicalAlphaStatus =
  refl

canonicalAlphaIsNotAPrediction :
  alphaIsNotAPrediction canonicalCKMBetaAlphaDemotionReceipt
  ≡
  true
canonicalAlphaIsNotAPrediction =
  refl

canonicalBetaCannotBeElevated :
  betaCanBeElevatedFromSources canonicalCKMBetaAlphaDemotionReceipt
  ≡
  false
canonicalBetaCannotBeElevated =
  refl

canonicalAlphaCannotBeElevated :
  alphaCanBeElevatedFromSources canonicalCKMBetaAlphaDemotionReceipt
  ≡
  false
canonicalAlphaCannotBeElevated =
  refl

canonicalNoBetaAlphaPromotion :
  CKMBetaAlphaPromotion →
  ⊥
canonicalNoBetaAlphaPromotion =
  ckmBetaAlphaPromotionImpossibleHere
