module DASHI.Physics.Closure.NSTriadKNFiniteOverlapTransportConstants where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Fabian Waleffe; Oleg Kiriukhin; Hajer Bahouri; Jean-Yves Chemin;
-- Raphael Danchin; DASHI repository contributors.
-- Title: "Explicit orbit, helicity and reality transport constants for the
-- nine finite-overlap Stage-3 conditions".
-- Venue/year: Physics of Fluids A 4 (1992); arXiv:2604.12188v1; Fourier
-- Analysis and Nonlinear Partial Differential Equations, Springer, 2011;
-- DASHI formal development, 2026.
-- DOI: 10.1063/1.858309; 10.48550/arXiv.2604.12188;
-- 10.1007/978-3-642-16830-7; the exact product ledger is
-- repository-original and has no DOI.
-- Uses: near shell-index multiplicity 9, oriented transition multiplicity 6,
-- five named residual subtypes, octahedral orbit bound 48, eight helicity
-- triples, and two ordered reality mates.
-- Relationship: fixes both linear and post-squaring safe constants for all
-- three owners. A concrete analytic instantiation still has to prove whether
-- each class transports before or after squaring; it may select the smaller
-- linear or the larger squared-safe ledger but may not mix them silently.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Physics.Closure.NSTriadKNFiniteOverlapCanonicalConstants as Canonical

orbitMultiplicity : Nat
orbitMultiplicity = 48

helicityMultiplicity : Nat
helicityMultiplicity = 8

realityMultiplicity : Nat
realityMultiplicity = 2

baseLinearTransport : Nat
baseLinearTransport = orbitMultiplicity * (helicityMultiplicity * realityMultiplicity)

baseSquaredTransport : Nat
baseSquaredTransport = baseLinearTransport * baseLinearTransport

nearLinearConstant : Nat
nearLinearConstant = Canonical.nearPairMultiplicity * baseLinearTransport

transitionLinearConstant : Nat
transitionLinearConstant = Canonical.transitionOrientedMultiplicity * baseLinearTransport

residualLinearConstant : Nat
residualLinearConstant = Canonical.residualSubtypeMultiplicity * baseLinearTransport

nearSquaredSafeConstant : Nat
nearSquaredSafeConstant = Canonical.nearPairMultiplicity * baseSquaredTransport

transitionSquaredSafeConstant : Nat
transitionSquaredSafeConstant =
  Canonical.transitionOrientedMultiplicity * baseSquaredTransport

residualSquaredSafeConstant : Nat
residualSquaredSafeConstant = Canonical.residualSubtypeMultiplicity * baseSquaredTransport

baseLinearTransportIs768 : baseLinearTransport ≡ 768
baseLinearTransportIs768 = refl

baseSquaredTransportIs589824 : baseSquaredTransport ≡ 589824
baseSquaredTransportIs589824 = refl

nearLinearConstantIs6912 : nearLinearConstant ≡ 6912
nearLinearConstantIs6912 = refl

transitionLinearConstantIs4608 : transitionLinearConstant ≡ 4608
transitionLinearConstantIs4608 = refl

residualLinearConstantIs3840 : residualLinearConstant ≡ 3840
residualLinearConstantIs3840 = refl

nearSquaredSafeConstantIs5308416 : nearSquaredSafeConstant ≡ 5308416
nearSquaredSafeConstantIs5308416 = refl

transitionSquaredSafeConstantIs3538944 :
  transitionSquaredSafeConstant ≡ 3538944
transitionSquaredSafeConstantIs3538944 = refl

residualSquaredSafeConstantIs2949120 :
  residualSquaredSafeConstant ≡ 2949120
residualSquaredSafeConstantIs2949120 = refl

data ConditionOwner : Set where
  outputOwner firstAdjointOwner secondAdjointOwner : ConditionOwner

data OverlapClass : Set where
  nearClass transitionClass residualClass : OverlapClass

data TransportStage : Set where
  beforeSquaring afterSquaring : TransportStage

transportedConstant : ConditionOwner → OverlapClass → TransportStage → Nat
transportedConstant owner nearClass beforeSquaring = nearLinearConstant
transportedConstant owner transitionClass beforeSquaring = transitionLinearConstant
transportedConstant owner residualClass beforeSquaring = residualLinearConstant
transportedConstant owner nearClass afterSquaring = nearSquaredSafeConstant
transportedConstant owner transitionClass afterSquaring = transitionSquaredSafeConstant
transportedConstant owner residualClass afterSquaring = residualSquaredSafeConstant

record TransportMajorantLaw {s : Set} : Set₁ where
  field
    _≤_ : s → s → Set
    scaleByNat : Nat → s → s
    transitive : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    orbitExpansionMajorant : ∀ value →
      value ≤ scaleByNat orbitMultiplicity value
    helicityResolutionMajorant : ∀ value →
      value ≤ scaleByNat helicityMultiplicity value
    realityMateMajorant : ∀ value →
      value ≤ scaleByNat realityMultiplicity value
    scaleAssociative : ∀ first second value →
      scaleByNat first (scaleByNat second value)
      ≡ scaleByNat (first * second) value

open TransportMajorantLaw public

allNineLinearConstantsSpecified : Bool
allNineLinearConstantsSpecified = true

allNineLinearConstantsSpecifiedIsTrue :
  allNineLinearConstantsSpecified ≡ true
allNineLinearConstantsSpecifiedIsTrue = refl

allNineSquaredSafeConstantsSpecified : Bool
allNineSquaredSafeConstantsSpecified = true

allNineSquaredSafeConstantsSpecifiedIsTrue :
  allNineSquaredSafeConstantsSpecified ≡ true
allNineSquaredSafeConstantsSpecifiedIsTrue = refl

concreteTransportStageSelectionStillRequired : Bool
concreteTransportStageSelectionStillRequired = true

concreteTransportStageSelectionStillRequiredIsTrue :
  concreteTransportStageSelectionStillRequired ≡ true
concreteTransportStageSelectionStillRequiredIsTrue = refl
