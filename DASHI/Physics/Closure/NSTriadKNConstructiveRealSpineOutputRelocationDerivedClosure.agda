module DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputRelocationDerivedClosure where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Zachary Murray; Viktor Csimma;
-- Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin; Loukas
-- Grafakos; Rodolfo H. Torres; DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Analysis in the Agda Proof
-- Assistant"; "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires"; "Fourier Analysis and
-- Nonlinear Partial Differential Equations"; "A Multilinear Schur Test and
-- Multiplier Operators"; and "Semantically pinned native-spine closure of the
-- output-relocation shell theorem".
-- Venue/year: Springer, 1985 and 2011; arXiv, 2022; Annales scientifiques de
-- l'Ecole Normale Superieure 14 (1981); Journal of Functional Analysis 187
-- (2001), 1--24; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.48550/arXiv.2205.08354;
-- 10.24033/asens.1404; 10.1007/978-3-642-16830-7;
-- 10.1006/jfan.2001.3804; the repository composition theorem has no DOI.
-- Uses: the unital ConstructiveRealSpine adapter, coherent base-two powers,
-- exact Sobolev decay formulas, and the absolute-magnitude coefficient bridge.
-- Relationship: the four former raw fields and both factor-nonnegativity facts
-- are constructed here.  The decay exponents are pinned to 2s-5/2 and 2s on
-- the target interval 5/2 < s < 3.  The remaining genuinely operator-specific
-- input is one literal absolute-coefficient estimate, together with concrete
-- native real/power capability inhabitants.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 1ℚ; _/_; _+_)

import DASHI.Analysis.ConstructiveRealSpine as Spine
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNOutputRelocationEmbeddedEnvelopeClosure as Embedded
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPowerMonotonicityBridge as Power
import DASHI.Physics.Closure.NSTriadKNOutputRelocationAbsoluteCoefficientBridge as Absolute
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputEnvelopeAdapter as Adapter

twoRational : ℚ
twoRational = 1ℚ + 1ℚ

threeRational : ℚ
threeRational = twoRational + 1ℚ

fiveRational : ℚ
fiveRational = (twoRational + twoRational) + 1ℚ

fiveHalvesRational : ℚ
fiveHalvesRational = Int.+ 5 / 2

record ConstructiveRealSpineBaseTwoPowerCapability
    (R : Spine.ConstructedOrderedCompleteReal)
    (capability : Adapter.ConstructiveRealSpineEnvelopeCapability R) : Set₁ where
  field
    two five : Spine.Real R
    twoMeaning : two ≡ Adapter.rationalEmbed capability twoRational
    fiveMeaning : five ≡ Adapter.rationalEmbed capability fiveRational

    twoPow : Spine.Real R → Spine.Real R
    twoStrictlyAboveOne : Spine._<_ R (Spine.one R) two
    twoPowNonnegative : ∀ exponent →
      Spine._≤_ R (Spine.zero R) (twoPow exponent)
    twoPowMonotone : ∀ {left right} →
      Spine._≤_ R left right →
      Spine._≤_ R (twoPow left) (twoPow right)
    twoPowZero : twoPow (Spine.zero R) ≡ Spine.one R
    twoPowOne : twoPow (Spine.one R) ≡ two
    twoPowAdditive : ∀ left right →
      twoPow (Spine._+_ R left right)
      ≡ Spine._*_ R (twoPow left) (twoPow right)

    scaleByNat : Spine.Real R → Nat → Spine.Real R
    scaleByNatZero : ∀ exponent →
      scaleByNat exponent zero ≡ Spine.zero R
    scaleByNatSuc : ∀ exponent shell →
      scaleByNat exponent (suc shell)
      ≡ Spine._+_ R exponent (scaleByNat exponent shell)
    scaleByNatMonotone : ∀ {left right} →
      Spine._≤_ R left right →
      ∀ shell →
      Spine._≤_ R
        (scaleByNat left shell)
        (scaleByNat right shell)

    negativeTwoAnchor : ∀ shell →
      twoPow (Spine.neg R (scaleByNat two shell))
      ≡ Adapter.rationalEmbed capability (Geo.pow Geo.quarter shell)
    negativeFiveAnchor : ∀ gap →
      twoPow (Spine.neg R (scaleByNat five gap))
      ≡ Adapter.rationalEmbed capability (Geo.pow Geo.thirtySecond gap)

open ConstructiveRealSpineBaseTwoPowerCapability public

asBaseTwoExponentAntitoneCarrier : ∀ R capability →
  ConstructiveRealSpineBaseTwoPowerCapability R capability →
  Power.BaseTwoExponentAntitoneCarrier
asBaseTwoExponentAntitoneCarrier R capability power = record
  { Real = Spine.Real R
  ; zero = Spine.zero R
  ; one = Spine.one R
  ; two = two power
  ; add = Spine._+_ R
  ; multiply = Spine._*_ R
  ; negate = Spine.neg R
  ; _≤_ = Spine._≤_ R
  ; _<_ = Spine._<_ R
  ; twoPow = twoPow power
  ; orderReflexive = Adapter.leqReflexive capability
  ; orderTransitive = Adapter.leqTransitive capability
  ; twoStrictlyAboveOne = twoStrictlyAboveOne power
  ; exponentOrderReversesAfterNegation = Adapter.negateAntitone capability
  ; twoPowNonnegative = twoPowNonnegative power
  ; twoPowMonotone = twoPowMonotone power
  ; twoPowZero = twoPowZero power
  ; twoPowOne = twoPowOne power
  ; twoPowAdditive = twoPowAdditive power
  }

asBaseTwoIntegerPowerAnchors : ∀ R capability
    (power : ConstructiveRealSpineBaseTwoPowerCapability R capability) →
  Power.BaseTwoIntegerPowerAnchors
    (asBaseTwoExponentAntitoneCarrier R capability power)
asBaseTwoIntegerPowerAnchors R capability power = record
  { twoExponent = two power
  ; fiveExponent = five power
  ; scaleByNat = scaleByNat power
  ; scaleByNatZero = scaleByNatZero power
  ; scaleByNatSuc = scaleByNatSuc power
  ; scaleByNatMonotone = scaleByNatMonotone power
  ; quarterPower = λ shell →
      Adapter.rationalEmbed capability (Geo.pow Geo.quarter shell)
  ; thirtySecondPower = λ gap →
      Adapter.rationalEmbed capability (Geo.pow Geo.thirtySecond gap)
  ; negativeTwoAnchor = negativeTwoAnchor power
  ; negativeFiveAnchor = negativeFiveAnchor power
  }

record ConstructiveRealSpineOutputDecayData
    (R : Spine.ConstructedOrderedCompleteReal)
    (capability : Adapter.ConstructiveRealSpineEnvelopeCapability R)
    (power : ConstructiveRealSpineBaseTwoPowerCapability R capability) : Set₁ where
  field
    sobolevExponent fiveHalves three : Spine.Real R
    fiveHalvesMeaning :
      fiveHalves ≡ Adapter.rationalEmbed capability fiveHalvesRational
    threeMeaning :
      three ≡ Adapter.rationalEmbed capability threeRational
    sobolevAboveFiveHalves : Spine._<_ R fiveHalves sobolevExponent
    sobolevBelowThree : Spine._<_ R sobolevExponent three

    lowDecayExponent gapDecayExponent : Spine.Real R
    lowDecayMeaning :
      lowDecayExponent
      ≡ Spine._-_ R
          (Spine._+_ R sobolevExponent sobolevExponent)
          fiveHalves
    gapDecayMeaning :
      gapDecayExponent
      ≡ Spine._+_ R sobolevExponent sobolevExponent

    lowDecayAtLeastTwo : Spine._≤_ R (two power) lowDecayExponent
    gapDecayAtLeastFive : Spine._≤_ R (five power) gapDecayExponent

open ConstructiveRealSpineOutputDecayData public

asOutputRelocationDecayExponentData : ∀ R capability power →
  ConstructiveRealSpineOutputDecayData R capability power →
  Power.OutputRelocationDecayExponentData
    (asBaseTwoIntegerPowerAnchors R capability power)
asOutputRelocationDecayExponentData R capability power decay = record
  { lowDecayExponent = lowDecayExponent decay
  ; gapDecayExponent = gapDecayExponent decay
  ; lowDecayAtLeastTwo = lowDecayAtLeastTwo decay
  ; gapDecayAtLeastFive = gapDecayAtLeastFive decay
  }

spineLowFactor : ∀ R capability power →
  ConstructiveRealSpineOutputDecayData R capability power →
  Nat → Spine.Real R
spineLowFactor R capability power decay =
  Power.lowShellFactor
    (asBaseTwoIntegerPowerAnchors R capability power)
    (asOutputRelocationDecayExponentData R capability power decay)

spineGapFactor : ∀ R capability power →
  ConstructiveRealSpineOutputDecayData R capability power →
  Nat → Spine.Real R
spineGapFactor R capability power decay =
  Power.gapShellFactor
    (asBaseTwoIntegerPowerAnchors R capability power)
    (asOutputRelocationDecayExponentData R capability power decay)

record ConstructiveRealSpineAbsoluteOrderCapability
    (R : Spine.ConstructedOrderedCompleteReal)
    (capability : Adapter.ConstructiveRealSpineEnvelopeCapability R) : Set₁ where
  field
    valueBelowAbsolute : ∀ value →
      Spine._≤_ R value (Spine.abs R value)
    negativeAbsoluteBelowValue : ∀ value →
      Spine._≤_ R (Spine.neg R (Spine.abs R value)) value

open ConstructiveRealSpineAbsoluteOrderCapability public

asAbsoluteValueOrderCapability : ∀ R capability →
  ConstructiveRealSpineAbsoluteOrderCapability R capability →
  Absolute.AbsoluteValueOrderCapability
    (Adapter.asOrderedRationalEnvelopeCarrier R capability)
asAbsoluteValueOrderCapability R capability absoluteOrder = record
  { absolute = Spine.abs R
  ; valueBelowAbsolute = valueBelowAbsolute absoluteOrder
  ; negativeAbsoluteBelowValue = negativeAbsoluteBelowValue absoluteOrder
  }

record ConstructiveRealSpineLiteralMagnitudeData
    (R : Spine.ConstructedOrderedCompleteReal)
    (capability : Adapter.ConstructiveRealSpineEnvelopeCapability R)
    (power : ConstructiveRealSpineBaseTwoPowerCapability R capability)
    (decay : ConstructiveRealSpineOutputDecayData R capability power)
    (absoluteOrder : ConstructiveRealSpineAbsoluteOrderCapability R capability) : Set₁ where
  field
    signedCoefficient : Nat → Nat → Spine.Real R
    absoluteCoefficientDominatedByFactors : ∀ lowShell gap →
      Spine._≤_ R
        (Spine.abs R (signedCoefficient lowShell gap))
        (Spine._*_ R
          (spineLowFactor R capability power decay lowShell)
          (spineGapFactor R capability power decay gap))

open ConstructiveRealSpineLiteralMagnitudeData public

asAbsoluteOutputRelocationShellData : ∀ R capability power decay absoluteOrder →
  ConstructiveRealSpineLiteralMagnitudeData
    R capability power decay absoluteOrder →
  Absolute.AbsoluteOutputRelocationShellData
    (asAbsoluteValueOrderCapability R capability absoluteOrder)
asAbsoluteOutputRelocationShellData
    R capability power decay absoluteOrder magnitude = record
  { lowFactor = spineLowFactor R capability power decay
  ; gapFactor = spineGapFactor R capability power decay
  ; signedCoefficient = signedCoefficient magnitude
  ; lowFactorNonnegative =
      Power.lowShellFactorNonnegative
        (asBaseTwoIntegerPowerAnchors R capability power)
        (asOutputRelocationDecayExponentData R capability power decay)
  ; gapFactorNonnegative =
      Power.gapShellFactorNonnegative
        (asBaseTwoIntegerPowerAnchors R capability power)
        (asOutputRelocationDecayExponentData R capability power decay)
  ; lowShellDominatedByQuarter =
      Power.lowShellDominatedByQuarter
        (asBaseTwoIntegerPowerAnchors R capability power)
        (asOutputRelocationDecayExponentData R capability power decay)
  ; gapDominatedByThirtySecond =
      Power.gapDominatedByThirtySecond
        (asBaseTwoIntegerPowerAnchors R capability power)
        (asOutputRelocationDecayExponentData R capability power decay)
  ; absoluteCoefficientDominatedByFactors =
      absoluteCoefficientDominatedByFactors magnitude
  }

asConstructiveRealSpineOutputShellData : ∀ R capability power decay absoluteOrder →
  (magnitude : ConstructiveRealSpineLiteralMagnitudeData
    R capability power decay absoluteOrder) →
  Adapter.ConstructiveRealSpineOutputShellData R capability
asConstructiveRealSpineOutputShellData
    R capability power decay absoluteOrder magnitude =
  let
    absoluteData =
      asAbsoluteOutputRelocationShellData
        R capability power decay absoluteOrder magnitude

    embeddedBridge =
      Absolute.asEmbeddedOutputRelocationShellBridge
        (asAbsoluteValueOrderCapability R capability absoluteOrder)
        absoluteData
  in
  record
    { lowFactor = spineLowFactor R capability power decay
    ; gapFactor = spineGapFactor R capability power decay
    ; signedCoefficient = signedCoefficient magnitude
    ; lowFactorNonnegative =
        Embedded.lowFactorNonnegative embeddedBridge
    ; gapFactorNonnegative =
        Embedded.gapFactorNonnegative embeddedBridge
    ; lowShellDominatedByQuarter =
        Embedded.lowShellDominatedByQuarter embeddedBridge
    ; gapDominatedByThirtySecond =
        Embedded.gapDominatedByThirtySecond embeddedBridge
    ; signedCoefficientUpper =
        Embedded.signedCoefficientUpper embeddedBridge
    ; signedCoefficientLower =
        Embedded.signedCoefficientLower embeddedBridge
    }

constructiveRealSpineDerivedOutputRelocationTheorem : ∀
    R capability power decay absoluteOrder
    (magnitude : ConstructiveRealSpineLiteralMagnitudeData
      R capability power decay absoluteOrder) →
  Embedded.EmbeddedConditionalArchetypeTheorem
    (Adapter.asOrderedRationalEnvelopeCarrier R capability)
    (Adapter.asEmbeddedOutputRelocationShellBridge
      R capability
      (asConstructiveRealSpineOutputShellData
        R capability power decay absoluteOrder magnitude))
constructiveRealSpineDerivedOutputRelocationTheorem
    R capability power decay absoluteOrder magnitude =
  Adapter.constructiveRealSpineOutputRelocationTheorem
    R capability
    (asConstructiveRealSpineOutputShellData
      R capability power decay absoluteOrder magnitude)

fourFormerRawBridgeFieldsDerived : Bool
fourFormerRawBridgeFieldsDerived = true

factorNonnegativityDerived : Bool
factorNonnegativityDerived = true

nativePowerConstantsPinnedToRationals : Bool
nativePowerConstantsPinnedToRationals = true

nativePowerZeroOneAndScalingPinned : Bool
nativePowerZeroOneAndScalingPinned = true

nativeOutputDecayFormulaPinned : Bool
nativeOutputDecayFormulaPinned = true

baseTwoPowerEnvelopeDerivationIntegrated : Bool
baseTwoPowerEnvelopeDerivationIntegrated = true

absoluteCoefficientDerivationIntegrated : Bool
absoluteCoefficientDerivationIntegrated = true

nativeSpineDerivedClosureTheoremClosed : Bool
nativeSpineDerivedClosureTheoremClosed = true

concreteNativeBaseTwoPowerCapabilityClosed : Bool
concreteNativeBaseTwoPowerCapabilityClosed = false

concreteLiteralAbsoluteCoefficientEstimateClosed : Bool
concreteLiteralAbsoluteCoefficientEstimateClosed = false

concreteOutputRelocationTheoremClosed : Bool
concreteOutputRelocationTheoremClosed = false

fourFormerRawBridgeFieldsDerivedIsTrue :
  fourFormerRawBridgeFieldsDerived ≡ true
fourFormerRawBridgeFieldsDerivedIsTrue = refl

factorNonnegativityDerivedIsTrue :
  factorNonnegativityDerived ≡ true
factorNonnegativityDerivedIsTrue = refl

nativePowerConstantsPinnedToRationalsIsTrue :
  nativePowerConstantsPinnedToRationals ≡ true
nativePowerConstantsPinnedToRationalsIsTrue = refl

nativePowerZeroOneAndScalingPinnedIsTrue :
  nativePowerZeroOneAndScalingPinned ≡ true
nativePowerZeroOneAndScalingPinnedIsTrue = refl

nativeOutputDecayFormulaPinnedIsTrue :
  nativeOutputDecayFormulaPinned ≡ true
nativeOutputDecayFormulaPinnedIsTrue = refl

baseTwoPowerEnvelopeDerivationIntegratedIsTrue :
  baseTwoPowerEnvelopeDerivationIntegrated ≡ true
baseTwoPowerEnvelopeDerivationIntegratedIsTrue = refl

absoluteCoefficientDerivationIntegratedIsTrue :
  absoluteCoefficientDerivationIntegrated ≡ true
absoluteCoefficientDerivationIntegratedIsTrue = refl

nativeSpineDerivedClosureTheoremClosedIsTrue :
  nativeSpineDerivedClosureTheoremClosed ≡ true
nativeSpineDerivedClosureTheoremClosedIsTrue = refl

concreteNativeBaseTwoPowerCapabilityClosedIsFalse :
  concreteNativeBaseTwoPowerCapabilityClosed ≡ false
concreteNativeBaseTwoPowerCapabilityClosedIsFalse = refl

concreteLiteralAbsoluteCoefficientEstimateClosedIsFalse :
  concreteLiteralAbsoluteCoefficientEstimateClosed ≡ false
concreteLiteralAbsoluteCoefficientEstimateClosedIsFalse = refl

concreteOutputRelocationTheoremClosedIsFalse :
  concreteOutputRelocationTheoremClosed ≡ false
concreteOutputRelocationTheoremClosedIsFalse = refl
