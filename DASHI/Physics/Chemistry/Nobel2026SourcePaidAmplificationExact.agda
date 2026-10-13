module DASHI.Physics.Chemistry.Nobel2026SourcePaidAmplificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Chemistry.Nobel2026ChiralitySourceAtlasExact as Atlas

------------------------------------------------------------------------
-- SOURCE-PAID QUANTITATIVE EE SURFACE
--
-- Enantiomeric excess is stored as an exact rational coordinate relative to
-- full scale (1 = 100% ee), without importing a real-number implementation.
-- A source may report a lower/upper threshold instead of an exact endpoint;
-- that relation is retained rather than silently replaced by equality.
------------------------------------------------------------------------

data EndpointRelation : Set where
  exactEndpoint : EndpointRelation
  greaterThanThreshold : EndpointRelation
  approximatelyInitial : EndpointRelation

record RationalEE : Set where
  constructor rationalEE
  field
    numerator : Nat
    denominator : Nat

open RationalEE public

record AmplificationObservation : Set where
  constructor amplificationObservation
  field
    source : Source.AttributedSource
    initialEE : RationalEE
    initialRelation : EndpointRelation
    terminalEE : RationalEE
    terminalRelation : EndpointRelation
    cycles : Nat
    sourceReading : String

open AmplificationObservation public

------------------------------------------------------------------------
-- Sato/Urabe/Ishiguro/Shibata/Soai 2003.
--
-- 0.00005% ee as a fraction of full ee is 1 / 2,000,000.
-- 99.5% ee is 199 / 200.  The publication says the initial value is about the
-- former and the endpoint is greater than the latter after three cycles.
------------------------------------------------------------------------

sato2003Initial : RationalEE
sato2003Initial = rationalEE 1 2000000

sato2003Threshold : RationalEE
sato2003Threshold = rationalEE 199 200

sato2003Amplification : AmplificationObservation
sato2003Amplification =
  amplificationObservation
    Atlas.sato2003
    sato2003Initial
    approximatelyInitial
    sato2003Threshold
    greaterThanThreshold
    3
    "about 0.00005% ee is amplified to greater than 99.5% ee after three asymmetric-autocatalysis cycles"

sato2003CycleCount : cycles sato2003Amplification ≡ 3
sato2003CycleCount = refl

sato2003InitialNumerator : numerator (initialEE sato2003Amplification) ≡ 1
sato2003InitialNumerator = refl

sato2003InitialDenominator : denominator (initialEE sato2003Amplification) ≡ 2000000
sato2003InitialDenominator = refl

sato2003ThresholdNumerator : numerator (terminalEE sato2003Amplification) ≡ 199
sato2003ThresholdNumerator = refl

sato2003ThresholdDenominator : denominator (terminalEE sato2003Amplification) ≡ 200
sato2003ThresholdDenominator = refl

-- Cross-products are exposed explicitly for downstream ordered-rational owners.
-- No hidden floating-point conversion is required.
satoInitialCrossProduct : Nat
satoInitialCrossProduct =
  numerator sato2003Initial * denominator sato2003Threshold

satoThresholdCrossProduct : Nat
satoThresholdCrossProduct =
  numerator sato2003Threshold * denominator sato2003Initial

satoInitialCrossProductValue : satoInitialCrossProduct ≡ 200
satoInitialCrossProductValue = refl

satoThresholdCrossProductValue : satoThresholdCrossProduct ≡ 398000000
satoThresholdCrossProductValue = refl

------------------------------------------------------------------------
-- Kagan 1986 is welded at the level actually paid by the accessible primary
-- source: nonlinear effects in asymmetric synthesis are the subject of the
-- primary paper.  No exact ee graph point is fabricated from a secondary plot.
------------------------------------------------------------------------

data NonlinearEffectKind : Set where
  positiveNLE : NonlinearEffectKind
  negativeNLE : NonlinearEffectKind
  nonlinearEffectWithoutNumericPointHere : NonlinearEffectKind

record KaganSourceWeld : Set where
  constructor kaganSourceWeld
  field
    source : Source.AttributedSource
    sourceOwnsNonlinearEffectObservation : Bool
    sourceOwnsNonlinearEffectObservationIsTrue :
      sourceOwnsNonlinearEffectObservation ≡ true
    exactNumericGraphPointImportedHere : Bool
    exactNumericGraphPointImportedHereIsFalse :
      exactNumericGraphPointImportedHere ≡ false
    retainedKind : NonlinearEffectKind

kagan1986Weld : KaganSourceWeld
kagan1986Weld =
  kaganSourceWeld
    Atlas.kagan1986
    true refl
    false refl
    nonlinearEffectWithoutNumericPointHere

record SourcePaidAmplificationBoundary : Set where
  constructor sourcePaidAmplificationBoundary
  field
    satoInitialEERationalisedExactly : Bool
    satoTerminalThresholdRationalisedExactly : Bool
    sourceThresholdRetainedAsThreshold : Bool
    threeCycleCountRetained : Bool
    kaganPrimaryNLESourceWelded : Bool
    secondaryPlotPromotedToPrimaryNumericDatum : Bool

canonicalSourcePaidAmplificationBoundary : SourcePaidAmplificationBoundary
canonicalSourcePaidAmplificationBoundary =
  sourcePaidAmplificationBoundary true true true true true false
