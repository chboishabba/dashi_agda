module DASHI.Physics.Closure.BothwellYe2022RedshiftComparisonExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (_+_; _*_; _≤ᵇ_)
open import Data.Rational.Base using (ℚ; _/_)

import DASHI.Physics.Closure.BothwellYe2022PublishedGradientPayloadExact as Payload
import DASHI.Physics.Closure.QuantumClockProperTimeRedshiftBridge as Redshift

------------------------------------------------------------------------
-- Same-scale comparison for the public Bothwell/Ye 2022 numbers.
--
-- Common comparison unit: 1e-21 per millimetre.
-- Published prediction:       -109
-- corrected observed result:   -98 +/- 23
-- synchronous result:         -128 +/- 27
--
-- Therefore the absolute residuals are 11 and 19 respectively, each less
-- than one quoted total uncertainty.  This is a source-bounded consistency
-- receipt, not a proof of GR and not a replacement for unpublished raw data.
------------------------------------------------------------------------

gravityFormulaReference : String
gravityFormulaReference =
  "DASHI.Physics.Closure.QuantumClockProperTimeRedshiftBridge: Delta f / f = Delta U / c^2; locally Delta U = a h"

speedOfLightExactSIReference : String
speedOfLightExactSIReference =
  "DASHI.Constants.Registry.canonicalSIDefiningConstants.c = 299792458 m s^-1"

comparisonUnit : String
comparisonUnit = "1e-21 mm^-1"

publishedPredictedMagnitudeUnits : Nat
publishedPredictedMagnitudeUnits = 109

publishedCorrectedObservedMagnitudeUnits : Nat
publishedCorrectedObservedMagnitudeUnits = 98

publishedCorrectedObservedUncertaintyUnits : Nat
publishedCorrectedObservedUncertaintyUnits = 23

publishedCorrectedAbsoluteResidualUnits : Nat
publishedCorrectedAbsoluteResidualUnits = 11

publishedSynchronousObservedMagnitudeUnits : Nat
publishedSynchronousObservedMagnitudeUnits = 128

publishedSynchronousObservedUncertaintyUnits : Nat
publishedSynchronousObservedUncertaintyUnits = 27

publishedSynchronousAbsoluteResidualUnits : Nat
publishedSynchronousAbsoluteResidualUnits = 19

canonicalPublishedCorrectedResidualIdentity :
  publishedPredictedMagnitudeUnits ≡
  publishedCorrectedObservedMagnitudeUnits + publishedCorrectedAbsoluteResidualUnits
canonicalPublishedCorrectedResidualIdentity = refl

canonicalPublishedSynchronousResidualIdentity :
  publishedSynchronousObservedMagnitudeUnits ≡
  publishedPredictedMagnitudeUnits + publishedSynchronousAbsoluteResidualUnits
canonicalPublishedSynchronousResidualIdentity = refl

publishedCorrectedWithinOneQuotedUncertainty : Bool
publishedCorrectedWithinOneQuotedUncertainty =
  publishedCorrectedAbsoluteResidualUnits ≤ᵇ publishedCorrectedObservedUncertaintyUnits

canonicalPublishedCorrectedWithinOneQuotedUncertainty :
  publishedCorrectedWithinOneQuotedUncertainty ≡ true
canonicalPublishedCorrectedWithinOneQuotedUncertainty = refl

publishedSynchronousWithinOneQuotedUncertainty : Bool
publishedSynchronousWithinOneQuotedUncertainty =
  publishedSynchronousAbsoluteResidualUnits ≤ᵇ publishedSynchronousObservedUncertaintyUnits

canonicalPublishedSynchronousWithinOneQuotedUncertainty :
  publishedSynchronousWithinOneQuotedUncertainty ≡ true
canonicalPublishedSynchronousWithinOneQuotedUncertainty = refl

------------------------------------------------------------------------
-- Exact gh/c^2 carrier in the same 1e-21 mm^-1 magnitude unit.
--
-- |a| = 9.796 m s^-2 = 9796/1000
-- c = 299792458 m s^-1 exactly in SI
-- gradient per mm = |a| / c^2 * 1e-3
-- expressed in units 1e-21/mm: |a| * 1e18 / c^2.
--
-- Before fraction reduction the exact carrier is
--
--   (9796 * 10^15) / (299792458^2)
-- = 9796000000000000000 / 89875517873681764
-- = 2449000000000000000 / 22468879468420441
-- ~ 108.99519949.
--
-- This avoids inserting floating arithmetic into the proof surface.
------------------------------------------------------------------------

sourceAccelerationMilliUnits : Nat
sourceAccelerationMilliUnits = 9796

speedOfLightInteger : Nat
speedOfLightInteger = 299792458

formulaScaleAfterAccelerationMilli : Nat
formulaScaleAfterAccelerationMilli = 1000000000000000

unreducedTheoryNumerator : Nat
unreducedTheoryNumerator =
  sourceAccelerationMilliUnits * formulaScaleAfterAccelerationMilli

unreducedTheoryDenominator : Nat
unreducedTheoryDenominator = speedOfLightInteger * speedOfLightInteger

canonicalUnreducedTheoryNumerator :
  unreducedTheoryNumerator ≡ 9796000000000000000
canonicalUnreducedTheoryNumerator = refl

canonicalUnreducedTheoryDenominator :
  unreducedTheoryDenominator ≡ 89875517873681764
canonicalUnreducedTheoryDenominator = refl

ghOverCSquaredScaledExact : ℚ
ghOverCSquaredScaledExact =
  + 2449000000000000000 / 22468879468420441

-- Cross-multiplication certificate for nearest-integer rounding to 109:
-- 217/2 <= exact < 219/2.
exactTheoryNumerator : Nat
exactTheoryNumerator = 2449000000000000000

exactTheoryDenominator : Nat
exactTheoryDenominator = 22468879468420441

lowerRoundingCrossProduct : Nat
lowerRoundingCrossProduct = 217 * exactTheoryDenominator

doubledTheoryNumerator : Nat
doubledTheoryNumerator = 2 * exactTheoryNumerator

upperRoundingCrossProduct : Nat
upperRoundingCrossProduct = 219 * exactTheoryDenominator

lowerRoundingBoundHolds : Bool
lowerRoundingBoundHolds = lowerRoundingCrossProduct ≤ᵇ doubledTheoryNumerator

upperRoundingBoundHolds : Bool
upperRoundingBoundHolds = doubledTheoryNumerator ≤ᵇ upperRoundingCrossProduct

canonicalLowerRoundingBoundHolds : lowerRoundingBoundHolds ≡ true
canonicalLowerRoundingBoundHolds = refl

canonicalUpperRoundingBoundHolds : upperRoundingBoundHolds ≡ true
canonicalUpperRoundingBoundHolds = refl

record BothwellYe2022ComparisonReceipt : Set where
  field
    payload : Payload.PublishedGradientPayload
    payloadIsCanonical : payload ≡ Payload.canonicalPublishedGradientPayload
    symbolicLaw : Redshift.QuantumClockProperTimeRedshiftBridge
    symbolicLawIsCanonical : symbolicLaw ≡ Redshift.canonicalQuantumClockProperTimeRedshiftBridge
    publishedPredictionRoundedFromGhOverCSquared : Bool
    publishedPredictionRoundedFromGhOverCSquaredIsTrue :
      publishedPredictionRoundedFromGhOverCSquared ≡ true
    correctedResultWithinOneQuotedUncertainty : Bool
    correctedResultWithinOneQuotedUncertaintyIsTrue :
      correctedResultWithinOneQuotedUncertainty ≡ true
    synchronousResultWithinOneQuotedUncertainty : Bool
    synchronousResultWithinOneQuotedUncertaintyIsTrue :
      synchronousResultWithinOneQuotedUncertainty ≡ true
    comparisonProvesGeneralRelativity : Bool
    comparisonProvesGeneralRelativityIsFalse : comparisonProvesGeneralRelativity ≡ false
    comparisonUsesRawUnpublishedData : Bool
    comparisonUsesRawUnpublishedDataIsFalse : comparisonUsesRawUnpublishedData ≡ false
    reading : List String

open BothwellYe2022ComparisonReceipt public

canonicalBothwellYe2022ComparisonReceipt : BothwellYe2022ComparisonReceipt
canonicalBothwellYe2022ComparisonReceipt = record
  { payload = Payload.canonicalPublishedGradientPayload
  ; payloadIsCanonical = refl
  ; symbolicLaw = Redshift.canonicalQuantumClockProperTimeRedshiftBridge
  ; symbolicLawIsCanonical = refl
  ; publishedPredictionRoundedFromGhOverCSquared = true
  ; publishedPredictionRoundedFromGhOverCSquaredIsTrue = refl
  ; correctedResultWithinOneQuotedUncertainty = publishedCorrectedWithinOneQuotedUncertainty
  ; correctedResultWithinOneQuotedUncertaintyIsTrue = canonicalPublishedCorrectedWithinOneQuotedUncertainty
  ; synchronousResultWithinOneQuotedUncertainty = publishedSynchronousWithinOneQuotedUncertainty
  ; synchronousResultWithinOneQuotedUncertaintyIsTrue = canonicalPublishedSynchronousWithinOneQuotedUncertainty
  ; comparisonProvesGeneralRelativity = false
  ; comparisonProvesGeneralRelativityIsFalse = refl
  ; comparisonUsesRawUnpublishedData = false
  ; comparisonUsesRawUnpublishedDataIsFalse = refl
  ; reading =
      "The public laboratory acceleration and exact SI c map gh/c^2 into 108.995... units of 1e-21 mm^-1, rounding to the paper's 109-unit predicted gradient magnitude."
      ∷ "The corrected measured magnitude differs from the published prediction by 11 units against a quoted total uncertainty of 23 units."
      ∷ "The synchronous two-region result differs by 19 units against a quoted uncertainty of 27 units."
      ∷ "These are direct public-number consistency checks; neither is promoted to a proof of general relativity."
      ∷ []
  }
