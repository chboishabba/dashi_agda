module DASHI.Physics.Closure.BetaAngleFromCarrierReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Beta angle from the carrier Vub and gamma receipts.
--
-- This receipt records the requested carrier-side unitarity-triangle beta
-- candidate.  The derivation uses |Vub| = alpha1 alpha2 and
-- gamma = arctan(sqrt(7)) * (1 - alpha1), then computes
-- R_b, rho, eta, and beta.  It is recorded as a carrier candidate only; no
-- physical CKM promotion is asserted here.

data BetaAngleFromCarrierStatus : Set where
  betaAngleCarrierCandidateRecorded :
    BetaAngleFromCarrierStatus

data BetaAngleFromCarrierSource : Set where
  vubAlpha12 :
    BetaAngleFromCarrierSource

  gammaDeltaCP :
    BetaAngleFromCarrierSource

canonicalBetaAngleFromCarrierSources :
  List BetaAngleFromCarrierSource
canonicalBetaAngleFromCarrierSources =
  vubAlpha12
  ∷ gammaDeltaCP
  ∷ []

data BetaAngleFromCarrierBlocker : Set where
  betaStillCarrierCandidate :
    BetaAngleFromCarrierBlocker

  missingCertifiedPhysicalCKMDiagonalisation :
    BetaAngleFromCarrierBlocker

  missingPDGBetaAuthorityPromotion :
    BetaAngleFromCarrierBlocker

canonicalBetaAngleFromCarrierBlockers :
  List BetaAngleFromCarrierBlocker
canonicalBetaAngleFromCarrierBlockers =
  betaStillCarrierCandidate
  ∷ missingCertifiedPhysicalCKMDiagonalisation
  ∷ missingPDGBetaAuthorityPromotion
  ∷ []

data BetaAngleFromCarrierPromotion : Set where

betaAngleFromCarrierPromotionImpossibleHere :
  BetaAngleFromCarrierPromotion →
  ⊥
betaAngleFromCarrierPromotionImpossibleHere ()

vubAlpha12FormulaLabel : String
vubAlpha12FormulaLabel =
  "|Vub| = alpha1 alpha2"

gammaDeltaCPFormulaLabel : String
gammaDeltaCPFormulaLabel =
  "gamma = arctan(sqrt(7)) * (1 - alpha1)"

rubFormulaLabel : String
rubFormulaLabel =
  "R_b = |Vub|/(A lambda^3) = alpha1 alpha2/(A lambda^3)"

rhoFormulaLabel : String
rhoFormulaLabel =
  "rho = R_b cos gamma"

etaFormulaLabel : String
etaFormulaLabel =
  "eta = R_b sin gamma"

betaFormulaLabel : String
betaFormulaLabel =
  "beta = arctan(eta/(1-rho))"

record BetaAngleFromCarrierReceipt : Set where
  field
    status :
      BetaAngleFromCarrierStatus

    vubFormula :
      String

    vubFormulaIsAlpha12 :
      vubFormula ≡ vubAlpha12FormulaLabel

    gammaFormula :
      String

    gammaFormulaIsDeltaCP :
      gammaFormula ≡ gammaDeltaCPFormulaLabel

    rubFormula :
      String

    rubFormulaIsCanonical :
      rubFormula ≡ rubFormulaLabel

    betaFormula :
      String

    betaFormulaIsCanonical :
      betaFormula ≡ betaFormulaLabel

    betaCarrierPrediction :
      Float

    betaCarrierPredictionDegrees :
      Float

    betaPDG :
      Float

    betaPDGDegrees :
      Float

    betaError :
      Float

    vubAlpha12Value :
      Float

    gammaRadians :
      Float

    rbCarrier :
      Float

    rhoFormula :
      String

    rhoFormulaIsCanonical :
      rhoFormula ≡ rhoFormulaLabel

    rhoCarrier :
      Float

    etaFormula :
      String

    etaFormulaIsCanonical :
      etaFormula ≡ etaFormulaLabel

    etaCarrier :
      Float

    oneMinusRhoCarrier :
      Float

    etaOverOneMinusRho :
      Float

    betaCarrierCandidate :
      Bool

    betaCarrierCandidateIsTrue :
      betaCarrierCandidate ≡ true

    physicalBetaPromoted :
      Bool

    physicalBetaPromotedIsFalse :
      physicalBetaPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    derivedFrom :
      List BetaAngleFromCarrierSource

    derivedFromIsCanonical :
      derivedFrom ≡ canonicalBetaAngleFromCarrierSources

    blockers :
      List BetaAngleFromCarrierBlocker

    blockersAreCanonical :
      blockers ≡ canonicalBetaAngleFromCarrierBlockers

    promotionFlags :
      List BetaAngleFromCarrierPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open BetaAngleFromCarrierReceipt public

canonicalBetaAngleFromCarrierReceipt :
  BetaAngleFromCarrierReceipt
canonicalBetaAngleFromCarrierReceipt =
  record
    { status =
        betaAngleCarrierCandidateRecorded
    ; vubFormula =
        vubAlpha12FormulaLabel
    ; vubFormulaIsAlpha12 =
        refl
    ; gammaFormula =
        gammaDeltaCPFormulaLabel
    ; gammaFormulaIsDeltaCP =
        refl
    ; rubFormula =
        rubFormulaLabel
    ; rubFormulaIsCanonical =
        refl
    ; betaFormula =
        betaFormulaLabel
    ; betaFormulaIsCanonical =
        refl
    ; betaCarrierPrediction =
        0.3973
    ; betaCarrierPredictionDegrees =
        22.77
    ; betaPDG =
        0.3747
    ; betaPDGDegrees =
        21.47
    ; betaError =
        6.04
    ; vubAlpha12Value =
        0.00359
    ; gammaRadians =
        1.1596
    ; rbCarrier =
        0.3870
    ; rhoFormula =
        rhoFormulaLabel
    ; rhoFormulaIsCanonical =
        refl
    ; rhoCarrier =
        0.1547
    ; etaFormula =
        etaFormulaLabel
    ; etaFormulaIsCanonical =
        refl
    ; etaCarrier =
        0.3547
    ; oneMinusRhoCarrier =
        0.8453
    ; etaOverOneMinusRho =
        0.4196
    ; betaCarrierCandidate =
        true
    ; betaCarrierCandidateIsTrue =
        refl
    ; physicalBetaPromoted =
        false
    ; physicalBetaPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; derivedFrom =
        canonicalBetaAngleFromCarrierSources
    ; derivedFromIsCanonical =
        refl
    ; blockers =
        canonicalBetaAngleFromCarrierBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Given |Vub| = alpha1 alpha2 and gamma = arctan(sqrt(7))*(1-alpha1)"
        ∷ "R_b = |Vub|/(A lambda^3) = alpha1 alpha2/(A lambda^3) = 0.3870"
        ∷ "rho = R_b cos gamma = 0.1547"
        ∷ "eta = R_b sin gamma = 0.3547"
        ∷ "beta = arctan(eta/(1-rho)) = arctan(0.3547/0.8453) = 0.3973 rad = 22.77 deg"
        ∷ "PDG beta = 0.3747 rad = 21.47 deg"
        ∷ "The recorded relative error is 6.04 percent"
        ∷ "derivedFrom is [vubAlpha12, gammaDeltaCP], and betaCarrierCandidate is true"
        ∷ "physical beta and CKM promotion remain false"
        ∷ []
    }

betaAngleFromCarrierCandidateIsRecorded :
  betaCarrierCandidate canonicalBetaAngleFromCarrierReceipt ≡ true
betaAngleFromCarrierCandidateIsRecorded =
  refl

betaAngleFromCarrierDerivedFromCanonicalSources :
  derivedFrom canonicalBetaAngleFromCarrierReceipt
  ≡
  canonicalBetaAngleFromCarrierSources
betaAngleFromCarrierDerivedFromCanonicalSources =
  refl

betaAngleFromCarrierDoesNotPromoteCKM :
  physicalCKMPromoted canonicalBetaAngleFromCarrierReceipt ≡ false
betaAngleFromCarrierDoesNotPromoteCKM =
  refl
