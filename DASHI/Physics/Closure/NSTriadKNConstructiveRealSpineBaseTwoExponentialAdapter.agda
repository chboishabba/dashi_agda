module DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineBaseTwoExponentialAdapter where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Zachary Murray; Viktor Csimma;
-- DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Analysis in the Agda Proof
-- Assistant"; and "Base-two powers from the native constructive exponential".
-- Venue/year: Springer, 1985; arXiv, 2022; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.48550/arXiv.2205.08354;
-- the repository adapter has no DOI.
-- Uses: the existing ConstructedRealExponential with exp(x+y)=exp(x)exp(y),
-- the definition 2^x = exp(x log 2), distributivity, and recursively defined
-- natural scaling.
-- Relationship: exponent additivity, zero/one meanings and natural scaling are
-- derived.  A concrete backend still supplies log 2, its order transport,
-- exp(log 2)=2 and the exact negative-integer anchors used by the rational
-- quarter and thirty-second envelopes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Analysis.ConstructiveRealSpine as Spine
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputRelocationDerivedClosure as Derived
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOrderedFieldCapabilityAdapter as Ordered
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

scaleByNat : ∀ {R : Spine.ConstructedOrderedCompleteReal} →
  Spine.Real R → Nat → Spine.Real R
scaleByNat {R} exponent zero = Spine.zero R
scaleByNat {R} exponent (suc shell) =
  Spine._+_ R exponent (scaleByNat exponent shell)

scaleByNatZero : ∀ {R : Spine.ConstructedOrderedCompleteReal} exponent →
  scaleByNat {R} exponent zero ≡ Spine.zero R
scaleByNatZero exponent = refl

scaleByNatSuc : ∀ {R : Spine.ConstructedOrderedCompleteReal} exponent shell →
  scaleByNat {R} exponent (suc shell)
  ≡ Spine._+_ R exponent (scaleByNat exponent shell)
scaleByNatSuc exponent shell = refl

scaleByNatMonotone : ∀ {R : Spine.ConstructedOrderedCompleteReal}
    (field : Ordered.ConstructiveRealSpineOrderedFieldCapability R)
    {left right} →
  Spine._≤_ R left right →
  ∀ shell →
  Spine._≤_ R (scaleByNat left shell) (scaleByNat right shell)
scaleByNatMonotone {R} field left≤right zero =
  Ordered.leqReflexive field (Spine.zero R)
scaleByNatMonotone field left≤right (suc shell) =
  Ordered.addMonotone field
    left≤right
    (scaleByNatMonotone field left≤right shell)

record BaseTwoExponentialBridgeData
    (R : Spine.ConstructedOrderedCompleteReal)
    (field : Ordered.ConstructiveRealSpineOrderedFieldCapability R)
    (E : Spine.ConstructedRealExponential R) : Set₁ where
  field
    logTwo two five : Spine.Real R
    twoMeaning :
      two ≡ Ordered.rationalEmbed field Derived.twoRational
    fiveMeaning :
      five ≡ Ordered.rationalEmbed field Derived.fiveRational

    twoStrictlyAboveOne : Spine._<_ R (Spine.one R) two
    zeroMultiplyLogTwo :
      Spine._*_ R (Spine.zero R) logTwo ≡ Spine.zero R
    expLogTwo : Spine.exp E logTwo ≡ two

    expNonnegative : ∀ exponent →
      Spine._≤_ R (Spine.zero R) (Spine.exp E exponent)
    expMonotoneLe : ∀ {left right} →
      Spine._≤_ R left right →
      Spine._≤_ R (Spine.exp E left) (Spine.exp E right)
    multiplyByLogTwoMonotone : ∀ {left right} →
      Spine._≤_ R left right →
      Spine._≤_ R
        (Spine._*_ R left logTwo)
        (Spine._*_ R right logTwo)

    negativeTwoAnchor : ∀ shell →
      Spine.exp E
        (Spine._*_ R
          (Spine.neg R (scaleByNat two shell))
          logTwo)
      ≡ Ordered.rationalEmbed field (Geo.pow Geo.quarter shell)
    negativeFiveAnchor : ∀ gap →
      Spine.exp E
        (Spine._*_ R
          (Spine.neg R (scaleByNat five gap))
          logTwo)
      ≡ Ordered.rationalEmbed field (Geo.pow Geo.thirtySecond gap)

open BaseTwoExponentialBridgeData public

twoPow : ∀ {R field E} →
  BaseTwoExponentialBridgeData R field E →
  Spine.Real R → Spine.Real R
twoPow {R} {E = E} data exponent =
  Spine.exp E (Spine._*_ R exponent (logTwo data))

twoPowZero : ∀ {R field E}
    (data : BaseTwoExponentialBridgeData R field E) →
  twoPow data (Spine.zero R) ≡ Spine.one R
twoPowZero {R} {E = E} data =
  trans
    (cong (Spine.exp E) (zeroMultiplyLogTwo data))
    (Spine.expZero E)

twoPowOne : ∀ {R field E}
    (data : BaseTwoExponentialBridgeData R field E) →
  twoPow data (Spine.one R) ≡ two data
twoPowOne {R} {E = E} data =
  trans
    (cong (Spine.exp E) (Spine.mulOneLeft R (logTwo data)))
    (expLogTwo data)

twoPowAdditive : ∀ {R field E}
    (data : BaseTwoExponentialBridgeData R field E)
    left right →
  twoPow data (Spine._+_ R left right)
  ≡ Spine._*_ R (twoPow data left) (twoPow data right)
twoPowAdditive {R} {E = E} data left right =
  trans
    (cong (Spine.exp E)
      (Spine.distribRight R left right (logTwo data)))
    (Spine.expAdd E
      (Spine._*_ R left (logTwo data))
      (Spine._*_ R right (logTwo data)))

twoPowNonnegative : ∀ {R field E}
    (data : BaseTwoExponentialBridgeData R field E)
    exponent →
  Spine._≤_ R (Spine.zero R) (twoPow data exponent)
twoPowNonnegative data exponent = expNonnegative data exponent

twoPowMonotone : ∀ {R field E}
    (data : BaseTwoExponentialBridgeData R field E)
    {left right} →
  Spine._≤_ R left right →
  Spine._≤_ R (twoPow data left) (twoPow data right)
twoPowMonotone data left≤right =
  expMonotoneLe data (multiplyByLogTwoMonotone data left≤right)

asBaseTwoPowerCapability : ∀ R field E →
  BaseTwoExponentialBridgeData R field E →
  Derived.ConstructiveRealSpineBaseTwoPowerCapability
    R (Ordered.asEnvelopeCapability R field)
asBaseTwoPowerCapability R field E data = record
  { two = two data
  ; five = five data
  ; twoMeaning = twoMeaning data
  ; fiveMeaning = fiveMeaning data
  ; twoPow = twoPow data
  ; twoStrictlyAboveOne = twoStrictlyAboveOne data
  ; twoPowNonnegative = twoPowNonnegative data
  ; twoPowMonotone = twoPowMonotone data
  ; twoPowZero = twoPowZero data
  ; twoPowOne = twoPowOne data
  ; twoPowAdditive = twoPowAdditive data
  ; scaleByNat = scaleByNat
  ; scaleByNatZero = scaleByNatZero
  ; scaleByNatSuc = scaleByNatSuc
  ; scaleByNatMonotone = scaleByNatMonotone field
  ; negativeTwoAnchor = negativeTwoAnchor data
  ; negativeFiveAnchor = negativeFiveAnchor data
  }

baseTwoPowerConstructedFromNativeExponential : Bool
baseTwoPowerConstructedFromNativeExponential = true

naturalScalingDerivedRecursively : Bool
naturalScalingDerivedRecursively = true

concreteLogTwoAndAnchorDataClosed : Bool
concreteLogTwoAndAnchorDataClosed = false

baseTwoPowerConstructedFromNativeExponentialIsTrue :
  baseTwoPowerConstructedFromNativeExponential ≡ true
baseTwoPowerConstructedFromNativeExponentialIsTrue = refl

naturalScalingDerivedRecursivelyIsTrue :
  naturalScalingDerivedRecursively ≡ true
naturalScalingDerivedRecursivelyIsTrue = refl

concreteLogTwoAndAnchorDataClosedIsFalse :
  concreteLogTwoAndAnchorDataClosed ≡ false
concreteLogTwoAndAnchorDataClosedIsFalse = refl
