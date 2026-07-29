module DASHI.Physics.Closure.NSTriadKNOutputRelocationPowerMonotonicityBridge where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Zachary Murray; Viktor Csimma;
-- DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Analysis in the Agda Proof
-- Assistant"; and "Minimal base-two exponent-antitonicity bridge for output
-- relocation".
-- Venue/year: Springer, 1985; arXiv, 2022; maintained constructive-real
-- continuation and DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.48550/arXiv.2205.08354; the repository
-- bridge has no DOI.
-- Uses: ordered constructive reals, the pinned Murray thesis snapshot, and the
-- integer geometric envelope already derived for output relocation.
-- Relationship: replaces the earlier broad fixed-base exponential/geometric
-- API target by exactly two domination lemmas: the low-shell real power is
-- bounded by 4^-j and the gap real power by 32^-d.  It does not claim that the
-- pinned external repository already exposes these lemmas or builds against
-- the current DASHI toolchain.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNConstructiveRealPowerBridge as Power
import DASHI.Physics.Closure.NSTriadKNMurrayThesisCommitSourceInspection as Murray
import DASHI.Physics.Closure.NSTriadKNOutputRelocationIntegerGeometricEnvelope as Envelope

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
    arbitraryRatioSeriesNotRequired :
      Envelope.outputRelocationArbitraryRatioGeometricTheoremRequired ≡ false

open PowerMonotonicityBridgeReceipt public

powerMonotonicityBridgeReceipt : PowerMonotonicityBridgeReceipt
powerMonotonicityBridgeReceipt = receipt
  Murray.murrayThesisCommitPinnedIsTrue
  Power.stage3ConstructiveRealPowerAdapterClosedIsFalse
  Envelope.outputRelocationIntegerEnvelopeExponentsClosedIsTrue
  Envelope.outputRelocationRationalGeometricConstantsClosedIsTrue
  Envelope.outputRelocationArbitraryRatioGeometricTheoremRequiredIsFalse

outputRelocationMinimalPowerBridgeSpecified : Bool
outputRelocationMinimalPowerBridgeSpecified = true

outputRelocationOnlyTwoPowerDominationLemmasRequired : Bool
outputRelocationOnlyTwoPowerDominationLemmasRequired = true

outputRelocationGeneralRealRatioSeriesRequired : Bool
outputRelocationGeneralRealRatioSeriesRequired = false

outputRelocationConcretePowerEnvelopeBridgeClosed : Bool
outputRelocationConcretePowerEnvelopeBridgeClosed = false

outputRelocationMinimalPowerBridgeSpecifiedIsTrue :
  outputRelocationMinimalPowerBridgeSpecified ≡ true
outputRelocationMinimalPowerBridgeSpecifiedIsTrue = refl

outputRelocationOnlyTwoPowerDominationLemmasRequiredIsTrue :
  outputRelocationOnlyTwoPowerDominationLemmasRequired ≡ true
outputRelocationOnlyTwoPowerDominationLemmasRequiredIsTrue = refl

outputRelocationGeneralRealRatioSeriesRequiredIsFalse :
  outputRelocationGeneralRealRatioSeriesRequired ≡ false
outputRelocationGeneralRealRatioSeriesRequiredIsFalse = refl

outputRelocationConcretePowerEnvelopeBridgeClosedIsFalse :
  outputRelocationConcretePowerEnvelopeBridgeClosed ≡ false
outputRelocationConcretePowerEnvelopeBridgeClosedIsFalse = refl
