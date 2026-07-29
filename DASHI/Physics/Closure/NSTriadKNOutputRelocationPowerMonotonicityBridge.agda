module DASHI.Physics.Closure.NSTriadKNOutputRelocationPowerMonotonicityBridge where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Zachary Murray; Viktor Csimma;
-- Agda standard-library contributors; DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Analysis in the Agda Proof
-- Assistant"; and "Minimal base-two exponent-antitonicity bridge for output
-- relocation".
-- Venue/year: Springer, 1985; arXiv, 2022; maintained constructive-real
-- continuation; Agda standard library; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.48550/arXiv.2205.08354; the repository
-- bridge has no DOI.
-- Uses: the pinned constructive-real candidate audit and the exact rational
-- finite geometric envelope proved internally in DASHI.
-- Relationship: rational/integer exponentiation now closes all finite sums.
-- It does not by itself compare a non-integral H^s factor 2^(-delta n) with
-- the rational sequences (1/4)^n and (1/32)^n.  The power layer therefore has
-- exactly two remaining comparison lemmas.  Literal signed-coefficient
-- domination is a separate operator bridge, not a third power lemma.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNConstructiveRealPowerBridge as Power
import DASHI.Physics.Closure.NSTriadKNMurrayThesisCommitSourceInspection as Murray
import DASHI.Physics.Closure.NSTriadKNOutputRelocationIntegerGeometricEnvelope as Envelope
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Rational
import DASHI.Physics.Closure.NSTriadKNOutputRelocationEmbeddedEnvelopeClosure as Embedded

record BaseTwoExponentAntitoneCarrier {r : Level} : Set (lsuc r) where
  field
    Real : Set r
    zero one two : Real
    natEmbed : Nat → Real
    add multiply negate : Real → Real → Real
    _≤_ _<_ : Real → Real → Set r
    twoPow : Real → Real

    twoStrictlyAboveOne : one < two
    exponentOrderReversesAfterNegation :
      ∀ {left right} → left ≤ right → negate right ≤ negate left
    twoPowMonotone :
      ∀ {left right} → left ≤ right → twoPow left ≤ twoPow right
    twoPowAdditive :
      ∀ left right →
      twoPow (add left right) ≡ multiply (twoPow left) (twoPow right)
    integerNegativeTwoMeaning : Set r
    integerNegativeFiveMeaning : Set r

open BaseTwoExponentAntitoneCarrier public

record OutputRelocationPowerEnvelopeBridge {r : Level}
    (C : BaseTwoExponentAntitoneCarrier {r}) : Set (lsuc r) where
  field
    sobolevExponent fiveHalves : Real C
    targetSobolevInterval : Set r

    lowDecayExponent gapDecayExponent : Real C
    lowDecayAboveTwo : Set r
    gapDecayAboveFive : Set r

    lowShellFactor : Nat → Real C
    gapFactor : Nat → Real C
    quarterPower : Nat → Real C
    thirtySecondPower : Nat → Real C

    lowShellDominatedByQuarter :
      ∀ shell → _≤_ C (lowShellFactor shell) (quarterPower shell)
    gapDominatedByThirtySecond :
      ∀ gap → _≤_ C (gapFactor gap) (thirtySecondPower gap)

open OutputRelocationPowerEnvelopeBridge public

record PowerMonotonicityBridgeReceipt : Set where
  constructor receipt
  field
    murraySourcePinned : Murray.murrayThesisCommitPinned ≡ true
    broadPowerAdapterStillOpen :
      Power.stage3ConstructiveRealPowerAdapterClosed ≡ false
    integerEnvelopeClosed :
      Envelope.outputRelocationIntegerEnvelopeExponentsClosed ≡ true
    rationalConstantsClosed :
      Envelope.outputRelocationRationalGeometricConstantsClosed ≡ true
    rationalFiniteSummationClosed :
      Rational.rationalFiniteGeometricEnvelopeClosed ≡ true
    arbitraryRatioSeriesNotRequired :
      Envelope.outputRelocationArbitraryRatioGeometricTheoremRequired ≡ false
    orderedEmbeddingClosureTheoremClosed :
      Embedded.orderedRationalEmbeddingClosureTheoremClosed ≡ true
    concreteOrderedCarrierAdapterStillOpen :
      Embedded.concreteOrderedCarrierAdapterClosed ≡ false

open PowerMonotonicityBridgeReceipt public

powerMonotonicityBridgeReceipt : PowerMonotonicityBridgeReceipt
powerMonotonicityBridgeReceipt = receipt
  Murray.murrayThesisCommitPinnedIsTrue
  Power.stage3ConstructiveRealPowerAdapterClosedIsFalse
  Envelope.outputRelocationIntegerEnvelopeExponentsClosedIsTrue
  Envelope.outputRelocationRationalGeometricConstantsClosedIsTrue
  Rational.rationalFiniteGeometricEnvelopeClosedIsTrue
  Envelope.outputRelocationArbitraryRatioGeometricTheoremRequiredIsFalse
  Embedded.orderedRationalEmbeddingClosureTheoremClosedIsTrue
  Embedded.concreteOrderedCarrierAdapterClosedIsFalse

outputRelocationMinimalPowerBridgeSpecified : Bool
outputRelocationMinimalPowerBridgeSpecified = true

outputRelocationOnlyTwoPowerDominationLemmasRequired : Bool
outputRelocationOnlyTwoPowerDominationLemmasRequired = true

outputRelocationRationalFiniteSummationClosed : Bool
outputRelocationRationalFiniteSummationClosed = true

outputRelocationIntegerPowersAloneCloseNonIntegralHsComparison : Bool
outputRelocationIntegerPowersAloneCloseNonIntegralHsComparison = false

outputRelocationGeneralRealRatioSeriesRequired : Bool
outputRelocationGeneralRealRatioSeriesRequired = false

outputRelocationConcreteOrderedCarrierAdapterClosed : Bool
outputRelocationConcreteOrderedCarrierAdapterClosed = false

outputRelocationConcretePowerEnvelopeBridgeClosed : Bool
outputRelocationConcretePowerEnvelopeBridgeClosed = false

outputRelocationMinimalPowerBridgeSpecifiedIsTrue :
  outputRelocationMinimalPowerBridgeSpecified ≡ true
outputRelocationMinimalPowerBridgeSpecifiedIsTrue = refl

outputRelocationOnlyTwoPowerDominationLemmasRequiredIsTrue :
  outputRelocationOnlyTwoPowerDominationLemmasRequired ≡ true
outputRelocationOnlyTwoPowerDominationLemmasRequiredIsTrue = refl

outputRelocationRationalFiniteSummationClosedIsTrue :
  outputRelocationRationalFiniteSummationClosed ≡ true
outputRelocationRationalFiniteSummationClosedIsTrue = refl

outputRelocationIntegerPowersAloneCloseNonIntegralHsComparisonIsFalse :
  outputRelocationIntegerPowersAloneCloseNonIntegralHsComparison ≡ false
outputRelocationIntegerPowersAloneCloseNonIntegralHsComparisonIsFalse = refl

outputRelocationGeneralRealRatioSeriesRequiredIsFalse :
  outputRelocationGeneralRealRatioSeriesRequired ≡ false
outputRelocationGeneralRealRatioSeriesRequiredIsFalse = refl

outputRelocationConcreteOrderedCarrierAdapterClosedIsFalse :
  outputRelocationConcreteOrderedCarrierAdapterClosed ≡ false
outputRelocationConcreteOrderedCarrierAdapterClosedIsFalse = refl

outputRelocationConcretePowerEnvelopeBridgeClosedIsFalse :
  outputRelocationConcretePowerEnvelopeBridgeClosed ≡ false
outputRelocationConcretePowerEnvelopeBridgeClosedIsFalse = refl
