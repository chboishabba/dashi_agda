module DASHI.Physics.Moonshine.KroneckerLimitAlphaCorrectionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Moonshine.ModularJInvariantAlphaReceipt as Alpha

------------------------------------------------------------------------
-- Kronecker-limit alpha correction frontier.
--
-- The modular-j numerical check finds the near-hit
-- 72 / 1728 = 1/24 = 0.041666666667 against
-- alpha1 = sqrt(mu/mc) = 0.0412406 from PDG 2024 MSbar masses at 2 GeV,
-- with about 1.03% discrepancy and no alpha2 formula.  This receipt records
-- the next admissible correction target: identify the 0.98977 correction using
-- an independently normalized
-- Kronecker-limit / eta / Gamma expression.  It does not identify the factor.

data KroneckerLimitAlphaCorrectionBlocker : Set where
  missingEtaIClosedFormNormalization :
    KroneckerLimitAlphaCorrectionBlocker

  missingGammaPiCorrectionIdentity :
    KroneckerLimitAlphaCorrectionBlocker

  missingCarrierMetricNormalization :
    KroneckerLimitAlphaCorrectionBlocker

  missingAlphaTwoKroneckerLimitMatch :
    KroneckerLimitAlphaCorrectionBlocker

  missingFormalKLToCarrierAlphaMap :
    KroneckerLimitAlphaCorrectionBlocker

canonicalKroneckerLimitAlphaCorrectionBlockers :
  List KroneckerLimitAlphaCorrectionBlocker
canonicalKroneckerLimitAlphaCorrectionBlockers =
  missingEtaIClosedFormNormalization
  ∷ missingGammaPiCorrectionIdentity
  ∷ missingCarrierMetricNormalization
  ∷ missingAlphaTwoKroneckerLimitMatch
  ∷ missingFormalKLToCarrierAlphaMap
  ∷ []

kroneckerLimitFormulaLabel : String
kroneckerLimitFormulaLabel =
  "KL(i) = 2*pi*(gamma - log 2 - log |eta(i)|^2), with eta(i) expressible using Gamma(1/4); no carrier-alpha normalization is proved"

alphaOneCorrectionTargetLabel : String
alphaOneCorrectionTargetLabel =
  "72/1728 = 1/24 = 0.041666666667; alpha1=sqrt(mu/mc)=0.0412406 from PDG 2024 MSbar masses at 2 GeV; discrepancy is about 1.03%; alpha1/(1/24) = 0.98977 is an unidentified correction target; no alpha2 formula or alpha promotion is supplied"

record KroneckerLimitAlphaCorrectionReceipt : Setω where
  field
    modularJAlphaReceipt :
      Alpha.ModularJInvariantAlphaReceipt

    alphaOneNearHitRecorded :
      Alpha.alphaOneNumericalNearHit modularJAlphaReceipt
      ≡
      true

    alphaOnePDGMassRatioRecorded :
      Alpha.alphaOnePDGMassRatioStatement modularJAlphaReceipt
      ≡
      Alpha.alphaOnePDGMassRatioLabel

    alphaOnePDGRatioCheckRecorded :
      Alpha.alphaOnePDGRatioCheckStatement modularJAlphaReceipt
      ≡
      Alpha.alphaOnePDGRatioCheckLabel

    alphaOneModularNaturalComparisonRecorded :
      Alpha.alphaOneModularNaturalComparison modularJAlphaReceipt
      ≡
      Alpha.alphaOneModularNaturalComparisonLabel

    alphaOneSquaredModularComparisonRecorded :
      Alpha.alphaOneSquaredModularComparison modularJAlphaReceipt
      ≡
      Alpha.alphaOneSquaredModularComparisonLabel

    alphaOneCorrectionStillUnidentified :
      Alpha.alphaOneCorrectionIdentified modularJAlphaReceipt
      ≡
      false

    alphaTwoNoHitRecorded :
      Alpha.alphaTwoNumericalMatch modularJAlphaReceipt
      ≡
      false

    alphaDerivedFromModularGeometryStillFalse :
      Alpha.alphaDerivedFromModularGeometry modularJAlphaReceipt
      ≡
      false

    kroneckerLimitFormulaRecorded :
      Bool

    kroneckerLimitFormulaRecordedIsTrue :
      kroneckerLimitFormulaRecorded ≡ true

    etaGammaNormalizationConstructed :
      Bool

    etaGammaNormalizationConstructedIsFalse :
      etaGammaNormalizationConstructed ≡ false

    correctionFactorIdentified :
      Bool

    correctionFactorIdentifiedIsFalse :
      correctionFactorIdentified ≡ false

    alphaTwoKroneckerLimitMatchFound :
      Bool

    alphaTwoKroneckerLimitMatchFoundIsFalse :
      alphaTwoKroneckerLimitMatchFound ≡ false

    formalKLToCarrierAlphaMapConstructed :
      Bool

    formalKLToCarrierAlphaMapConstructedIsFalse :
      formalKLToCarrierAlphaMapConstructed ≡ false

    alphaDerivedFromModularGeometry :
      Bool

    alphaDerivedFromModularGeometryIsFalse :
      alphaDerivedFromModularGeometry ≡ false

    blockers :
      List KroneckerLimitAlphaCorrectionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalKroneckerLimitAlphaCorrectionBlockers

    kroneckerLimitFormula :
      String

    kroneckerLimitFormulaIsCanonical :
      kroneckerLimitFormula ≡ kroneckerLimitFormulaLabel

    alphaOneCorrectionTarget :
      String

    alphaOneCorrectionTargetIsCanonical :
      alphaOneCorrectionTarget ≡ alphaOneCorrectionTargetLabel

    receiptBoundary :
      List String

open KroneckerLimitAlphaCorrectionReceipt public

canonicalKroneckerLimitAlphaCorrectionReceipt :
  KroneckerLimitAlphaCorrectionReceipt
canonicalKroneckerLimitAlphaCorrectionReceipt =
  record
    { modularJAlphaReceipt =
        Alpha.canonicalModularJInvariantAlphaReceipt
    ; alphaOneNearHitRecorded =
        Alpha.modularJInvariantAlphaReceiptRecordsAlphaOneNearHit
    ; alphaOnePDGMassRatioRecorded =
        Alpha.modularJInvariantAlphaReceiptRecordsPDGMassRatioAlphaOne
    ; alphaOnePDGRatioCheckRecorded =
        Alpha.modularJInvariantAlphaReceiptRecordsPDGRatioCheck
    ; alphaOneModularNaturalComparisonRecorded =
        Alpha.modularJInvariantAlphaReceiptRecordsModularNaturalComparison
    ; alphaOneSquaredModularComparisonRecorded =
        Alpha.modularJInvariantAlphaReceiptRecordsSquaredModularComparison
    ; alphaOneCorrectionStillUnidentified =
        Alpha.modularJInvariantAlphaReceiptKeepsAlphaOneCorrectionUnidentified
    ; alphaTwoNoHitRecorded =
        Alpha.modularJInvariantAlphaReceiptRecordsAlphaTwoNoHit
    ; alphaDerivedFromModularGeometryStillFalse =
        Alpha.modularJInvariantAlphaReceiptKeepsDerivationClosed
    ; kroneckerLimitFormulaRecorded =
        true
    ; kroneckerLimitFormulaRecordedIsTrue =
        refl
    ; etaGammaNormalizationConstructed =
        false
    ; etaGammaNormalizationConstructedIsFalse =
        refl
    ; correctionFactorIdentified =
        false
    ; correctionFactorIdentifiedIsFalse =
        refl
    ; alphaTwoKroneckerLimitMatchFound =
        false
    ; alphaTwoKroneckerLimitMatchFoundIsFalse =
        refl
    ; formalKLToCarrierAlphaMapConstructed =
        false
    ; formalKLToCarrierAlphaMapConstructedIsFalse =
        refl
    ; alphaDerivedFromModularGeometry =
        false
    ; alphaDerivedFromModularGeometryIsFalse =
        refl
    ; blockers =
        canonicalKroneckerLimitAlphaCorrectionBlockers
    ; blockersAreCanonical =
        refl
    ; kroneckerLimitFormula =
        kroneckerLimitFormulaLabel
    ; kroneckerLimitFormulaIsCanonical =
        refl
    ; alphaOneCorrectionTarget =
        alphaOneCorrectionTargetLabel
    ; alphaOneCorrectionTargetIsCanonical =
        refl
    ; receiptBoundary =
        "The Kronecker-limit expression is recorded as the next admissible correction target for the alpha1 near-hit 72/1728 = 1/24 versus alpha1=sqrt(mu/mc)=0.0412406 from PDG 2024 MSbar masses at 2 GeV"
        ∷ "No eta/Gamma/pi normalization is proved to equal the 0.98977 correction alpha1/(1/24)"
        ∷ "The receipt preserves the modular-natural comparison: 1/24 is within about 1-2% of alpha1, and (1/24)^2 is within about 2% of mu/mc"
        ∷ "No alpha2 Kronecker-limit match is found"
        ∷ "alphaDerivedFromModularGeometry remains false"
        ∷ []
    }

kroneckerLimitCorrectionStillOpen :
  correctionFactorIdentified canonicalKroneckerLimitAlphaCorrectionReceipt
  ≡
  false
kroneckerLimitCorrectionStillOpen =
  refl

kroneckerLimitCarriesPDGMassRatioAlphaOne :
  Alpha.alphaOnePDGMassRatioStatement
    (modularJAlphaReceipt canonicalKroneckerLimitAlphaCorrectionReceipt)
  ≡
  Alpha.alphaOnePDGMassRatioLabel
kroneckerLimitCarriesPDGMassRatioAlphaOne =
  refl

kroneckerLimitCarriesPDGRatioCheck :
  Alpha.alphaOnePDGRatioCheckStatement
    (modularJAlphaReceipt canonicalKroneckerLimitAlphaCorrectionReceipt)
  ≡
  Alpha.alphaOnePDGRatioCheckLabel
kroneckerLimitCarriesPDGRatioCheck =
  refl

kroneckerLimitCarriesModularNaturalComparison :
  Alpha.alphaOneModularNaturalComparison
    (modularJAlphaReceipt canonicalKroneckerLimitAlphaCorrectionReceipt)
  ≡
  Alpha.alphaOneModularNaturalComparisonLabel
kroneckerLimitCarriesModularNaturalComparison =
  refl

kroneckerLimitCarriesSquaredModularComparison :
  Alpha.alphaOneSquaredModularComparison
    (modularJAlphaReceipt canonicalKroneckerLimitAlphaCorrectionReceipt)
  ≡
  Alpha.alphaOneSquaredModularComparisonLabel
kroneckerLimitCarriesSquaredModularComparison =
  refl

kroneckerLimitDoesNotDeriveAlpha :
  alphaDerivedFromModularGeometry canonicalKroneckerLimitAlphaCorrectionReceipt
  ≡
  false
kroneckerLimitDoesNotDeriveAlpha =
  refl
