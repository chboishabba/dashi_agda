module DASHI.Physics.Closure.NSTriadKNOutputRelocationPowerMonotonicityBridge where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Zachary Murray; Viktor Csimma;
-- Agda standard-library contributors; DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Analysis in the Agda Proof
-- Assistant"; and "Base-two exponent-antitonicity derivation for the
-- output-relocation shell envelopes".
-- Venue/year: Springer, 1985; arXiv, 2022; maintained constructive-real
-- continuation; Agda standard library; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.48550/arXiv.2205.08354; the repository
-- derivation has no DOI.
-- Uses: the pinned constructive-real candidate audit, exact rational finite
-- geometric envelopes, monotonicity of x |-> 2^x, order reversal under
-- negation, monotonicity of multiplication by a natural shell index, and the
-- exact anchors 2^(-2n)=(1/4)^n and 2^(-5n)=(1/32)^n.
-- Relationship: proves lowShellDominatedByQuarter and
-- gapDominatedByThirtySecond from coherent base-two power data.  Those two
-- inequalities are theorem outputs rather than independent caller-supplied
-- fields.  A concrete constructive-real base-two implementation and the
-- literal coefficient majorant remain separate inhabitants.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNConstructiveRealPowerBridge as Power
import DASHI.Physics.Closure.NSTriadKNMurrayThesisCommitSourceInspection as Murray
import DASHI.Physics.Closure.NSTriadKNOutputRelocationIntegerGeometricEnvelope as Envelope
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Rational
import DASHI.Physics.Closure.NSTriadKNOutputRelocationEmbeddedEnvelopeClosure as Embedded

record BaseTwoExponentAntitoneCarrier {r : Level} : Set (lsuc r) where
  field
    Real : Set r
    zero one two : Real
    add multiply : Real → Real → Real
    negate : Real → Real
    _≤_ _<_ : Real → Real → Set r
    twoPow : Real → Real

    orderReflexive : ∀ value → value ≤ value
    orderTransitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right
    twoStrictlyAboveOne : one < two
    exponentOrderReversesAfterNegation :
      ∀ {left right} → left ≤ right → negate right ≤ negate left
    twoPowMonotone :
      ∀ {left right} → left ≤ right → twoPow left ≤ twoPow right
    twoPowAdditive :
      ∀ left right →
      twoPow (add left right) ≡ multiply (twoPow left) (twoPow right)

open BaseTwoExponentAntitoneCarrier public

record BaseTwoIntegerPowerAnchors {r : Level}
    (C : BaseTwoExponentAntitoneCarrier {r}) : Set (lsuc r) where
  field
    twoExponent fiveExponent : Real C
    scaleByNat : Real C → Nat → Real C
    scaleByNatMonotone : ∀ {left right} →
      _≤_ C left right →
      ∀ shell → _≤_ C (scaleByNat left shell) (scaleByNat right shell)

    quarterPower thirtySecondPower : Nat → Real C
    negativeTwoAnchor : ∀ shell →
      twoPow C (negate C (scaleByNat twoExponent shell))
      ≡ quarterPower shell
    negativeFiveAnchor : ∀ gap →
      twoPow C (negate C (scaleByNat fiveExponent gap))
      ≡ thirtySecondPower gap

open BaseTwoIntegerPowerAnchors public

record OutputRelocationDecayExponentData {r : Level}
    {C : BaseTwoExponentAntitoneCarrier {r}}
    (anchors : BaseTwoIntegerPowerAnchors C) : Set (lsuc r) where
  field
    lowDecayExponent gapDecayExponent : Real C
    lowDecayAtLeastTwo :
      _≤_ C (twoExponent anchors) lowDecayExponent
    gapDecayAtLeastFive :
      _≤_ C (fiveExponent anchors) gapDecayExponent

open OutputRelocationDecayExponentData public

lowShellFactor : ∀ {r}
    {C : BaseTwoExponentAntitoneCarrier {r}}
    (anchors : BaseTwoIntegerPowerAnchors C) →
    OutputRelocationDecayExponentData anchors →
    Nat → Real C
lowShellFactor {C = C} anchors decay shell =
  twoPow C
    (negate C
      (scaleByNat anchors (lowDecayExponent decay) shell))

gapShellFactor : ∀ {r}
    {C : BaseTwoExponentAntitoneCarrier {r}}
    (anchors : BaseTwoIntegerPowerAnchors C) →
    OutputRelocationDecayExponentData anchors →
    Nat → Real C
gapShellFactor {C = C} anchors decay gap =
  twoPow C
    (negate C
      (scaleByNat anchors (gapDecayExponent decay) gap))

lowShellDominatedByQuarter : ∀ {r}
    {C : BaseTwoExponentAntitoneCarrier {r}}
    (anchors : BaseTwoIntegerPowerAnchors C)
    (decay : OutputRelocationDecayExponentData anchors)
    shell →
  _≤_ C
    (lowShellFactor anchors decay shell)
    (quarterPower anchors shell)
lowShellDominatedByQuarter {C = C} anchors decay shell =
  subst
    (λ upper →
      _≤_ C (lowShellFactor anchors decay shell) upper)
    (negativeTwoAnchor anchors shell)
    (twoPowMonotone C
      (exponentOrderReversesAfterNegation C
        (scaleByNatMonotone anchors
          (lowDecayAtLeastTwo decay)
          shell)))

gapDominatedByThirtySecond : ∀ {r}
    {C : BaseTwoExponentAntitoneCarrier {r}}
    (anchors : BaseTwoIntegerPowerAnchors C)
    (decay : OutputRelocationDecayExponentData anchors)
    gap →
  _≤_ C
    (gapShellFactor anchors decay gap)
    (thirtySecondPower anchors gap)
gapDominatedByThirtySecond {C = C} anchors decay gap =
  subst
    (λ upper →
      _≤_ C (gapShellFactor anchors decay gap) upper)
    (negativeFiveAnchor anchors gap)
    (twoPowMonotone C
      (exponentOrderReversesAfterNegation C
        (scaleByNatMonotone anchors
          (gapDecayAtLeastFive decay)
          gap)))

record OutputRelocationPowerEnvelopeBridge {r : Level}
    (C : BaseTwoExponentAntitoneCarrier {r}) : Set (lsuc r) where
  field
    lowFactor gapFactor : Nat → Real C
    quarterEnvelope thirtySecondEnvelope : Nat → Real C
    lowFactorDominated : ∀ shell →
      _≤_ C (lowFactor shell) (quarterEnvelope shell)
    gapFactorDominated : ∀ gap →
      _≤_ C (gapFactor gap) (thirtySecondEnvelope gap)

open OutputRelocationPowerEnvelopeBridge public

derivedOutputRelocationPowerEnvelopeBridge : ∀ {r}
    {C : BaseTwoExponentAntitoneCarrier {r}}
    (anchors : BaseTwoIntegerPowerAnchors C)
    (decay : OutputRelocationDecayExponentData anchors) →
  OutputRelocationPowerEnvelopeBridge C
derivedOutputRelocationPowerEnvelopeBridge anchors decay = record
  { lowFactor = lowShellFactor anchors decay
  ; gapFactor = gapShellFactor anchors decay
  ; quarterEnvelope = quarterPower anchors
  ; thirtySecondEnvelope = thirtySecondPower anchors
  ; lowFactorDominated = lowShellDominatedByQuarter anchors decay
  ; gapFactorDominated = gapDominatedByThirtySecond anchors decay
  }

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

outputRelocationMinimalPowerBridgeSpecified : Bool
outputRelocationMinimalPowerBridgeSpecified = true

outputRelocationTwoPowerDominationTheoremsClosed : Bool
outputRelocationTwoPowerDominationTheoremsClosed = true

outputRelocationOnlyTwoPowerDominationLemmasRequired : Bool
outputRelocationOnlyTwoPowerDominationLemmasRequired = true

outputRelocationRationalFiniteSummationClosed : Bool
outputRelocationRationalFiniteSummationClosed = true

outputRelocationIntegerPowersAloneCloseNonIntegralHsComparison : Bool
outputRelocationIntegerPowersAloneCloseNonIntegralHsComparison = false

outputRelocationGeneralRealRatioSeriesRequired : Bool
outputRelocationGeneralRealRatioSeriesRequired = false

outputRelocationConcreteBaseTwoPowerDataClosed : Bool
outputRelocationConcreteBaseTwoPowerDataClosed = false

outputRelocationConcretePowerEnvelopeBridgeClosed : Bool
outputRelocationConcretePowerEnvelopeBridgeClosed = false

outputRelocationMinimalPowerBridgeSpecifiedIsTrue :
  outputRelocationMinimalPowerBridgeSpecified ≡ true
outputRelocationMinimalPowerBridgeSpecifiedIsTrue = refl

outputRelocationTwoPowerDominationTheoremsClosedIsTrue :
  outputRelocationTwoPowerDominationTheoremsClosed ≡ true
outputRelocationTwoPowerDominationTheoremsClosedIsTrue = refl

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

outputRelocationConcreteBaseTwoPowerDataClosedIsFalse :
  outputRelocationConcreteBaseTwoPowerDataClosed ≡ false
outputRelocationConcreteBaseTwoPowerDataClosedIsFalse = refl

outputRelocationConcretePowerEnvelopeBridgeClosedIsFalse :
  outputRelocationConcretePowerEnvelopeBridgeClosed ≡ false
outputRelocationConcretePowerEnvelopeBridgeClosedIsFalse = refl
