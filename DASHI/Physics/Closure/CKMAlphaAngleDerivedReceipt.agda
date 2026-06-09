module DASHI.Physics.Closure.CKMAlphaAngleDerivedReceipt where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- CKM alpha angle derived from the already-recorded beta and gamma.
--
-- No new carrier input is introduced here.  The alpha angle is recorded as
-- the unitarity-triangle complement alpha = pi - beta - gamma.

data CKMAlphaAngleDerivedStatus : Set where
  carrierConsequenceDerived :
    CKMAlphaAngleDerivedStatus

alphaFormulaLabel : String
alphaFormulaLabel =
  "alpha = pi - beta - gamma"

radUnitLabel : String
radUnitLabel =
  "rad"

degreeUnitLabel : String
degreeUnitLabel =
  "degree"

percentUnitLabel : String
percentUnitLabel =
  "percent"

record CKMAlphaAngleDerivedReceipt : Set where
  field
    statusUpgrade :
      CKMAlphaAngleDerivedStatus

    statusUpgradeIsCarrierConsequenceDerived :
      statusUpgrade ≡ carrierConsequenceDerived

    alphaFormula :
      String

    alphaFormulaIsBetaGammaComplement :
      alphaFormula ≡ alphaFormulaLabel

    betaInput :
      Float

    betaInputUnit :
      String

    betaInputUnitIsRad :
      betaInputUnit ≡ radUnitLabel

    gammaInput :
      Float

    gammaInputUnit :
      String

    gammaInputUnitIsRad :
      gammaInputUnit ≡ radUnitLabel

    alphaCarrier :
      Float

    alphaCarrierUnit :
      String

    alphaCarrierUnitIsRad :
      alphaCarrierUnit ≡ radUnitLabel

    alphaCarrierDegrees :
      Float

    alphaCarrierDegreesUnit :
      String

    alphaCarrierDegreesUnitIsDegree :
      alphaCarrierDegreesUnit ≡ degreeUnitLabel

    alphaPDG :
      Float

    alphaPDGUnit :
      String

    alphaPDGUnitIsRad :
      alphaPDGUnit ≡ radUnitLabel

    alphaPDGDegrees :
      Float

    alphaPDGDegreesUnit :
      String

    alphaPDGDegreesUnitIsDegree :
      alphaPDGDegreesUnit ≡ degreeUnitLabel

    alphaError :
      Float

    alphaErrorUnit :
      String

    alphaErrorUnitIsPercent :
      alphaErrorUnit ≡ percentUnitLabel

    derivedFromBetaAndGamma :
      Bool

    derivedFromBetaAndGammaIsTrue :
      derivedFromBetaAndGamma ≡ true

    noNewCarrierInputRequired :
      Bool

    noNewCarrierInputRequiredIsTrue :
      noNewCarrierInputRequired ≡ true

    nearNinetyDegreePredictionIsCarrierConsequence :
      Bool

    nearNinetyDegreePredictionIsCarrierConsequenceIsTrue :
      nearNinetyDegreePredictionIsCarrierConsequence ≡ true

    receiptBoundary :
      List String

open CKMAlphaAngleDerivedReceipt public

canonicalCKMAlphaAngleDerivedReceipt :
  CKMAlphaAngleDerivedReceipt
canonicalCKMAlphaAngleDerivedReceipt =
  record
    { statusUpgrade =
        carrierConsequenceDerived
    ; statusUpgradeIsCarrierConsequenceDerived =
        refl
    ; alphaFormula =
        alphaFormulaLabel
    ; alphaFormulaIsBetaGammaComplement =
        refl
    ; betaInput =
        0.3973
    ; betaInputUnit =
        radUnitLabel
    ; betaInputUnitIsRad =
        refl
    ; gammaInput =
        1.1596
    ; gammaInputUnit =
        radUnitLabel
    ; gammaInputUnitIsRad =
        refl
    ; alphaCarrier =
        1.5847
    ; alphaCarrierUnit =
        radUnitLabel
    ; alphaCarrierUnitIsRad =
        refl
    ; alphaCarrierDegrees =
        90.80
    ; alphaCarrierDegreesUnit =
        degreeUnitLabel
    ; alphaCarrierDegreesUnitIsDegree =
        refl
    ; alphaPDG =
        1.5889
    ; alphaPDGUnit =
        radUnitLabel
    ; alphaPDGUnitIsRad =
        refl
    ; alphaPDGDegrees =
        91.04
    ; alphaPDGDegreesUnit =
        degreeUnitLabel
    ; alphaPDGDegreesUnitIsDegree =
        refl
    ; alphaError =
        0.3
    ; alphaErrorUnit =
        percentUnitLabel
    ; alphaErrorUnitIsPercent =
        refl
    ; derivedFromBetaAndGamma =
        true
    ; derivedFromBetaAndGammaIsTrue =
        refl
    ; noNewCarrierInputRequired =
        true
    ; noNewCarrierInputRequiredIsTrue =
        refl
    ; nearNinetyDegreePredictionIsCarrierConsequence =
        true
    ; nearNinetyDegreePredictionIsCarrierConsequenceIsTrue =
        refl
    ; receiptBoundary =
        "alpha is derived as alpha = pi - beta - gamma"
        ∷ "The beta input is 0.3973 rad"
        ∷ "The gamma input is 1.1596 rad"
        ∷ "The carrier alpha prediction is 1.5847 rad = 90.80 degrees"
        ∷ "The PDG alpha comparison is 1.5889 rad = 91.04 degrees"
        ∷ "The recorded alpha error is 0.3 percent"
        ∷ "No new carrier input is required"
        ∷ "The near-90-degree prediction is a carrier consequence"
        ∷ []
    }

ckmAlphaCarrierValue :
  alphaCarrier canonicalCKMAlphaAngleDerivedReceipt ≡ 1.5847
ckmAlphaCarrierValue =
  refl

ckmAlphaPDGValue :
  alphaPDG canonicalCKMAlphaAngleDerivedReceipt ≡ 1.5889
ckmAlphaPDGValue =
  refl

ckmAlphaErrorValue :
  alphaError canonicalCKMAlphaAngleDerivedReceipt ≡ 0.3
ckmAlphaErrorValue =
  refl

ckmAlphaDerivedFromBetaAndGamma :
  derivedFromBetaAndGamma canonicalCKMAlphaAngleDerivedReceipt ≡ true
ckmAlphaDerivedFromBetaAndGamma =
  refl

ckmAlphaNoNewCarrierInputRequired :
  noNewCarrierInputRequired canonicalCKMAlphaAngleDerivedReceipt ≡ true
ckmAlphaNoNewCarrierInputRequired =
  refl

ckmAlphaNearNinetyDegreeCarrierConsequence :
  nearNinetyDegreePredictionIsCarrierConsequence
    canonicalCKMAlphaAngleDerivedReceipt
    ≡ true
ckmAlphaNearNinetyDegreeCarrierConsequence =
  refl
