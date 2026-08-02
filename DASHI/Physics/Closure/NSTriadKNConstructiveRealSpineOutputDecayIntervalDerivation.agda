module DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputDecayIntervalDerivation where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Zachary Murray; Viktor Csimma;
-- Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin;
-- DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Analysis in the Agda Proof
-- Assistant"; "Fourier Analysis and Nonlinear Partial Differential
-- Equations"; and "Native derivation of the output-relocation decay endpoint
-- inequalities".
-- Venue/year: Springer, 1985 and 2011; arXiv, 2022; DASHI formal development,
-- 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.48550/arXiv.2205.08354;
-- 10.1007/978-3-642-16830-7; the repository order derivation has no DOI.
-- Uses: 5/2 < s, strict monotonicity of addition and subtraction, transitivity,
-- the embedding identities 5 = 5/2 + 5/2 and 5 - 5/2 = 5/2, and 2 < 5/2.
-- Relationship: derives
--   2 <= 2s - 5/2  and  5 <= 2s
-- instead of accepting those endpoint comparisons as independent fields.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Analysis.ConstructiveRealSpine as Spine
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputEnvelopeAdapter as Adapter
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputRelocationDerivedClosure as Derived

record StrictOrderedSubtractionCapability
    (R : Spine.ConstructedOrderedCompleteReal) : Set₁ where
  field
    ltTransitive : ∀ {a b c} →
      Spine._<_ R a b → Spine._<_ R b c → Spine._<_ R a c
    ltToLe : ∀ {a b} → Spine._<_ R a b → Spine._≤_ R a b
    addStrictMonotone : ∀ {a b c d} →
      Spine._<_ R a b → Spine._<_ R c d →
      Spine._<_ R (Spine._+_ R a c) (Spine._+_ R b d)
    subtractSameRightStrict : ∀ {a b} →
      Spine._<_ R a b → ∀ right →
      Spine._<_ R
        (Spine._-_ R a right)
        (Spine._-_ R b right)

open StrictOrderedSubtractionCapability public

record ConstructiveRealSpineSobolevIntervalData
    (R : Spine.ConstructedOrderedCompleteReal)
    (capability : Adapter.ConstructiveRealSpineEnvelopeCapability R)
    (power : Derived.ConstructiveRealSpineBaseTwoPowerCapability
      R capability) : Set₁ where
  field
    sobolevExponent fiveHalves three : Spine.Real R
    fiveHalvesMeaning :
      fiveHalves ≡ Adapter.rationalEmbed capability Derived.fiveHalvesRational
    threeMeaning :
      three ≡ Adapter.rationalEmbed capability Derived.threeRational
    sobolevAboveFiveHalves : Spine._<_ R fiveHalves sobolevExponent
    sobolevBelowThree : Spine._<_ R sobolevExponent three

    twoBelowFiveHalves : Spine._<_ R (Derived.two power) fiveHalves
    fiveIsTwoFiveHalves :
      Derived.five power ≡ Spine._+_ R fiveHalves fiveHalves
    fiveMinusFiveHalvesIsFiveHalves :
      Spine._-_ R (Derived.five power) fiveHalves ≡ fiveHalves

open ConstructiveRealSpineSobolevIntervalData public

twiceSobolev : ∀ R capability power →
  ConstructiveRealSpineSobolevIntervalData R capability power →
  Spine.Real R
twiceSobolev R capability power interval =
  Spine._+_ R
    (sobolevExponent interval)
    (sobolevExponent interval)

lowDecay : ∀ R capability power →
  ConstructiveRealSpineSobolevIntervalData R capability power →
  Spine.Real R
lowDecay R capability power interval =
  Spine._-_ R
    (twiceSobolev R capability power interval)
    (fiveHalves interval)

fiveBelowTwiceSobolev : ∀ R capability power
    (order : StrictOrderedSubtractionCapability R)
    (interval : ConstructiveRealSpineSobolevIntervalData
      R capability power) →
  Spine._<_ R
    (Derived.five power)
    (twiceSobolev R capability power interval)
fiveBelowTwiceSobolev R capability power order interval =
  subst
    (λ lower →
      Spine._<_ R lower
        (twiceSobolev R capability power interval))
    (sym (fiveIsTwoFiveHalves interval))
    (addStrictMonotone order
      (sobolevAboveFiveHalves interval)
      (sobolevAboveFiveHalves interval))

fiveHalvesBelowLowDecay : ∀ R capability power
    (order : StrictOrderedSubtractionCapability R)
    (interval : ConstructiveRealSpineSobolevIntervalData
      R capability power) →
  Spine._<_ R
    (fiveHalves interval)
    (lowDecay R capability power interval)
fiveHalvesBelowLowDecay R capability power order interval =
  subst
    (λ lower →
      Spine._<_ R lower
        (lowDecay R capability power interval))
    (fiveMinusFiveHalvesIsFiveHalves interval)
    (subtractSameRightStrict order
      (fiveBelowTwiceSobolev R capability power order interval)
      (fiveHalves interval))

twoBelowLowDecay : ∀ R capability power
    (order : StrictOrderedSubtractionCapability R)
    (interval : ConstructiveRealSpineSobolevIntervalData
      R capability power) →
  Spine._<_ R
    (Derived.two power)
    (lowDecay R capability power interval)
twoBelowLowDecay R capability power order interval =
  ltTransitive order
    (twoBelowFiveHalves interval)
    (fiveHalvesBelowLowDecay R capability power order interval)

outputDecayDataFromInterval : ∀ R capability power →
  StrictOrderedSubtractionCapability R →
  ConstructiveRealSpineSobolevIntervalData R capability power →
  Derived.ConstructiveRealSpineOutputDecayData R capability power
outputDecayDataFromInterval R capability power order interval = record
  { sobolevExponent = sobolevExponent interval
  ; fiveHalves = fiveHalves interval
  ; three = three interval
  ; fiveHalvesMeaning = fiveHalvesMeaning interval
  ; threeMeaning = threeMeaning interval
  ; sobolevAboveFiveHalves = sobolevAboveFiveHalves interval
  ; sobolevBelowThree = sobolevBelowThree interval
  ; lowDecayExponent = lowDecay R capability power interval
  ; gapDecayExponent = twiceSobolev R capability power interval
  ; lowDecayMeaning = refl
  ; gapDecayMeaning = refl
  ; lowDecayAtLeastTwo =
      ltToLe order (twoBelowLowDecay R capability power order interval)
  ; gapDecayAtLeastFive =
      ltToLe order
        (fiveBelowTwiceSobolev R capability power order interval)
  }

nativeOutputDecayEndpointInequalitiesDerived : Bool
nativeOutputDecayEndpointInequalitiesDerived = true

concreteStrictOrderedSubtractionCapabilityClosed : Bool
concreteStrictOrderedSubtractionCapabilityClosed = false

nativeOutputDecayEndpointInequalitiesDerivedIsTrue :
  nativeOutputDecayEndpointInequalitiesDerived ≡ true
nativeOutputDecayEndpointInequalitiesDerivedIsTrue = refl

concreteStrictOrderedSubtractionCapabilityClosedIsFalse :
  concreteStrictOrderedSubtractionCapabilityClosed ≡ false
concreteStrictOrderedSubtractionCapabilityClosedIsFalse = refl
