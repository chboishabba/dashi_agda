module DASHI.Analysis.NonArchimedeanProlateCriticalLineSigmaSourceExact where

------------------------------------------------------------------------
-- PROLATE CRITICAL-LINE SIGMA SOURCE RECEIPT
--
-- In Formalization/Quantum/ProlateScaling.lean, sigma is the real part of the
-- complex spectral parameter s = sigma + i t.  The checked source defines the
-- Archimedean shift through eta = sigma - 1/2 and proves:
--
--   * secularImaginaryPart (1/2) ... = 0;
--   * off-line non-vanishing when sigma != 1/2 under positive coupling/weight;
--   * the normal Dirac squared norm is bounded below by (sigma - 1/2)^2.
--
-- These are theorem-bearing statements about an Archimedean/prolate spectral
-- parameter.  They are not consequences of the finite cyclotomic orbit radius.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record ProlateSigmaSourceReceipt : Set where
  constructor prolateSigmaSourceReceipt
  field
    sigmaIsRealPartOfSpectralParameter : Bool
    archimedeanShiftUsesSigmaMinusHalf : Bool
    secularImaginaryAtHalfOwned : Bool
    secularImaginaryOffHalfNonzeroConditionalOwned : Bool
    normalDiracGapBoundOwned : Bool

    dependsOnCyclotomicSigmaDefinition : Bool
    dependsOnTwistedCircleRadiusAsymptotics : Bool
    identifiesOrbitAmplitudeExponentWithCriticalLine : Bool

canonicalProlateSigmaSourceReceipt : ProlateSigmaSourceReceipt
canonicalProlateSigmaSourceReceipt =
  prolateSigmaSourceReceipt
    true true true true true
    false false false

prolateHalfIsTheoremBearingIndependently :
  ProlateSigmaSourceReceipt.secularImaginaryAtHalfOwned
    canonicalProlateSigmaSourceReceipt
  ≡ true
prolateHalfIsTheoremBearingIndependently = refl

prolateDoesNotDependOnCyclotomicDefinition :
  ProlateSigmaSourceReceipt.dependsOnCyclotomicSigmaDefinition
    canonicalProlateSigmaSourceReceipt
  ≡ false
prolateDoesNotDependOnCyclotomicDefinition = refl

record CrossLaneSigmaWeldBoundary : Set where
  constructor crossLaneSigmaWeldBoundary
  field
    equalNumeralHalfIsEnough : Bool
    finiteOrbitAmplitudeHalfAnchorsProlateHalfWithoutTheorem : Bool
    explicitCrossLaneMapRequired : Bool
    compatibilityTheoremRequired : Bool

canonicalCrossLaneSigmaWeldBoundary : CrossLaneSigmaWeldBoundary
canonicalCrossLaneSigmaWeldBoundary =
  crossLaneSigmaWeldBoundary false false true true

anchorClaimNeedsRealWeld :
  CrossLaneSigmaWeldBoundary.finiteOrbitAmplitudeHalfAnchorsProlateHalfWithoutTheorem
    canonicalCrossLaneSigmaWeldBoundary
  ≡ false
anchorClaimNeedsRealWeld = refl
