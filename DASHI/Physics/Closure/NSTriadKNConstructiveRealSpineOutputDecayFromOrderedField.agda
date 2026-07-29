module DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputDecayFromOrderedField where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Herman Geuvers; Milad Niqui;
-- Zachary Murray; Viktor Csimma; Jean-Michel Bony; Hajer Bahouri;
-- Jean-Yves Chemin; Raphael Danchin; DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Reals in Coq: Axioms and
-- Categoricity"; "Constructive Analysis in the Agda Proof Assistant";
-- "Fourier Analysis and Nonlinear Partial Differential Equations"; and
-- "Output-relocation decay data derived from the native ordered field".
-- Venue/year: Springer, 1985 and 2011; Types for Proofs and Programs,
-- LNCS 2277 (2002), 79--95; arXiv, 2022; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.1007/3-540-45842-5_6;
-- 10.48550/arXiv.2205.08354; 10.1007/978-3-642-16830-7;
-- the repository derivation has no DOI.
-- Uses: the unified ordered rational embedding, exact rational identities
-- 5 = 5/2 + 5/2 and 5 - 5/2 = 5/2, the rational inequality 2 < 5/2,
-- and the native target interval 5/2 < s < 3.
-- Relationship: constructs all endpoint arithmetic required by
-- ConstructiveRealSpineOutputDecayData.  The caller no longer supplies native
-- versions of the 2, 5/2 and 5 identities independently.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (_+_; _-_; _<_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Analysis.ConstructiveRealSpine as Spine
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputRelocationDerivedClosure as Derived
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOrderedFieldCapabilityAdapter as Ordered
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputDecayIntervalDerivation as Interval

record NativeSobolevExponentInTargetInterval
    (R : Spine.ConstructedOrderedCompleteReal)
    (field : Ordered.ConstructiveRealSpineOrderedFieldCapability R) : Set₁ where
  field
    sobolevExponent : Spine.Real R
    aboveFiveHalves :
      Spine._<_ R
        (Ordered.rationalEmbed field Derived.fiveHalvesRational)
        sobolevExponent
    belowThree :
      Spine._<_ R
        sobolevExponent
        (Ordered.rationalEmbed field Derived.threeRational)

open NativeSobolevExponentInTargetInterval public

record ExactRationalOutputDecayEndpointWitness : Set where
  field
    twoBelowFiveHalves :
      Derived.twoRational < Derived.fiveHalvesRational

open ExactRationalOutputDecayEndpointWitness public

fiveAsTwoFiveHalves :
  Derived.fiveRational
  ≡ Derived.fiveHalvesRational + Derived.fiveHalvesRational
fiveAsTwoFiveHalves = solve []

fiveMinusFiveHalves :
  Derived.fiveRational - Derived.fiveHalvesRational
  ≡ Derived.fiveHalvesRational
fiveMinusFiveHalves = solve []

nativeTwoBelowFiveHalves : ∀ R field power →
  ExactRationalOutputDecayEndpointWitness →
  Spine._<_ R
    (Derived.two power)
    (Ordered.rationalEmbed field Derived.fiveHalvesRational)
nativeTwoBelowFiveHalves R field power witness =
  subst
    (λ lower →
      Spine._<_ R lower
        (Ordered.rationalEmbed field Derived.fiveHalvesRational))
    (sym (Derived.twoMeaning power))
    (Ordered.embedStrictOrder field (twoBelowFiveHalves witness))

nativeFiveIsTwoFiveHalves : ∀ R field power →
  Derived.five power
  ≡ Spine._+_ R
      (Ordered.rationalEmbed field Derived.fiveHalvesRational)
      (Ordered.rationalEmbed field Derived.fiveHalvesRational)
nativeFiveIsTwoFiveHalves R field power =
  trans
    (Derived.fiveMeaning power)
    (trans
      (cong (Ordered.rationalEmbed field) fiveAsTwoFiveHalves)
      (Ordered.embedAdd field
        Derived.fiveHalvesRational
        Derived.fiveHalvesRational))

nativeFiveMinusFiveHalvesIsFiveHalves : ∀ R field power →
  Spine._-_ R
    (Derived.five power)
    (Ordered.rationalEmbed field Derived.fiveHalvesRational)
  ≡ Ordered.rationalEmbed field Derived.fiveHalvesRational
nativeFiveMinusFiveHalvesIsFiveHalves R field power =
  trans
    (cong
      (λ left →
        Spine._-_ R left
          (Ordered.rationalEmbed field Derived.fiveHalvesRational))
      (Derived.fiveMeaning power))
    (trans
      (sym (Ordered.embedSubtract field
        Derived.fiveRational
        Derived.fiveHalvesRational))
      (cong (Ordered.rationalEmbed field) fiveMinusFiveHalves))

asSobolevIntervalData : ∀ R field power →
  ExactRationalOutputDecayEndpointWitness →
  NativeSobolevExponentInTargetInterval R field →
  Interval.ConstructiveRealSpineSobolevIntervalData
    R (Ordered.asEnvelopeCapability R field) power
asSobolevIntervalData R field power rationalWitness interval = record
  { sobolevExponent = sobolevExponent interval
  ; fiveHalves = Ordered.rationalEmbed field Derived.fiveHalvesRational
  ; three = Ordered.rationalEmbed field Derived.threeRational
  ; fiveHalvesMeaning = refl
  ; threeMeaning = refl
  ; sobolevAboveFiveHalves = aboveFiveHalves interval
  ; sobolevBelowThree = belowThree interval
  ; twoBelowFiveHalves =
      nativeTwoBelowFiveHalves R field power rationalWitness
  ; fiveIsTwoFiveHalves = nativeFiveIsTwoFiveHalves R field power
  ; fiveMinusFiveHalvesIsFiveHalves =
      nativeFiveMinusFiveHalvesIsFiveHalves R field power
  }

outputDecayDataFromOrderedField : ∀ R field power →
  ExactRationalOutputDecayEndpointWitness →
  NativeSobolevExponentInTargetInterval R field →
  Derived.ConstructiveRealSpineOutputDecayData
    R (Ordered.asEnvelopeCapability R field) power
outputDecayDataFromOrderedField R field power rationalWitness interval =
  Interval.outputDecayDataFromInterval
    R
    (Ordered.asEnvelopeCapability R field)
    power
    (Ordered.asStrictOrderedSubtractionCapability R field)
    (asSobolevIntervalData R field power rationalWitness interval)

rationalEndpointIdentitiesClosed : Bool
rationalEndpointIdentitiesClosed = true

nativeEndpointInequalitiesDerivedFromTargetInterval : Bool
nativeEndpointInequalitiesDerivedFromTargetInterval = true

concreteSobolevExponentIntervalInhabited : Bool
concreteSobolevExponentIntervalInhabited = false

rationalEndpointIdentitiesClosedIsTrue :
  rationalEndpointIdentitiesClosed ≡ true
rationalEndpointIdentitiesClosedIsTrue = refl

nativeEndpointInequalitiesDerivedFromTargetIntervalIsTrue :
  nativeEndpointInequalitiesDerivedFromTargetInterval ≡ true
nativeEndpointInequalitiesDerivedFromTargetIntervalIsTrue = refl

concreteSobolevExponentIntervalInhabitedIsFalse :
  concreteSobolevExponentIntervalInhabited ≡ false
concreteSobolevExponentIntervalInhabitedIsFalse = refl
