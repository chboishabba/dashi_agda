module DASHI.Physics.Chemistry.Nobel2026SourcePaidAmplificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Chemistry.Nobel2026ChiralitySourceAtlasExact as Atlas

------------------------------------------------------------------------
-- SOURCE-PAID QUANTITATIVE EE SURFACE
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
-- Shibata et al. 1996: direct exact numeric source surface, 8.9% -> 88.1%.
-- Relative to full-scale ee these are 89/1000 and 881/1000.
------------------------------------------------------------------------

shibata1996Initial : RationalEE
shibata1996Initial = rationalEE 89 1000

shibata1996Terminal : RationalEE
shibata1996Terminal = rationalEE 881 1000

shibata1996Amplification : AmplificationObservation
shibata1996Amplification =
  amplificationObservation
    Atlas.shibata1996
    shibata1996Initial exactEndpoint
    shibata1996Terminal exactEndpoint
    0
    "the article abstract reports ee increasing from 8.9% to 88.1% by a series of asymmetric autocatalytic alkylations; no exact cycle count is encoded here"

shibataInitialNumerator : numerator (initialEE shibata1996Amplification) ≡ 89
shibataInitialNumerator = refl

shibataTerminalNumerator : numerator (terminalEE shibata1996Amplification) ≡ 881
shibataTerminalNumerator = refl

------------------------------------------------------------------------
-- Sato et al. 2003: about 0.00005% ee -> greater than 99.5% after 3 cycles.
-- 0.00005% of full scale is 1/2,000,000; 99.5% is 199/200.
------------------------------------------------------------------------

sato2003Initial : RationalEE
sato2003Initial = rationalEE 1 2000000

sato2003Threshold : RationalEE
sato2003Threshold = rationalEE 199 200

sato2003Amplification : AmplificationObservation
sato2003Amplification =
  amplificationObservation
    Atlas.sato2003
    sato2003Initial approximatelyInitial
    sato2003Threshold greaterThanThreshold
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

------------------------------------------------------------------------
-- Kagan 1986 source weld.  The accessible primary metadata/article surface pays
-- the nonlinear-effect observation identity; no secondary plot is promoted to
-- a primary exact graph point.
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
    sourceOwnsNonlinearEffectObservationIsTrue : sourceOwnsNonlinearEffectObservation ≡ true
    exactNumericGraphPointImportedHere : Bool
    exactNumericGraphPointImportedHereIsFalse : exactNumericGraphPointImportedHere ≡ false
    retainedKind : NonlinearEffectKind

kagan1986Weld : KaganSourceWeld
kagan1986Weld =
  kaganSourceWeld Atlas.kagan1986 true refl false refl nonlinearEffectWithoutNumericPointHere

record SourcePaidAmplificationBoundary : Set where
  constructor sourcePaidAmplificationBoundary
  field
    direct1996NumericAmplificationPaid : Bool
    satoInitialEERationalisedExactly : Bool
    satoTerminalThresholdRationalisedExactly : Bool
    sourceThresholdRetainedAsThreshold : Bool
    threeCycleCountRetained : Bool
    kaganPrimaryNLESourceWelded : Bool
    secondaryPlotPromotedToPrimaryNumericDatum : Bool

canonicalSourcePaidAmplificationBoundary : SourcePaidAmplificationBoundary
canonicalSourcePaidAmplificationBoundary =
  sourcePaidAmplificationBoundary true true true true true true false
