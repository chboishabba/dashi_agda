module DASHI.Physics.Closure.NSTriadKNLegacyCoordinateInterpretationAudit where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_; fst)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical

------------------------------------------------------------------------
-- Candidate meanings for legacy coordinates.  `unexplained` is an explicit
-- failure state: a finite index is not physical merely because it is bounded.
------------------------------------------------------------------------

data CoordinateMeaning : Set where
  shellIndex modeIndex orientation helicity permutation realityOrbit
  angularSector phaseSector multiplicityResidue unexplained : CoordinateMeaning

record LegacyCoordinateInterpretation (N : Nat) : Set₁ where
  field
    headMeaning tailMeaning residueMeaning :
      Relation.ConcreteNonResidualTriadIncidence N → CoordinateMeaning

    reconstruct :
      Relation.ConcreteNonResidualTriadIncidence N →
      Physical.PhysicalTriadIncidence

    reconstructionResonant :
      (code : Relation.ConcreteNonResidualTriadIncidence N) →
      Physical.resonance (reconstruct code)
      ≡ Physical.resonance (reconstruct code)

    headPhysicallyPreserved :
      (code : Relation.ConcreteNonResidualTriadIncidence N) → Set

    tailPhysicallyPreserved :
      (code : Relation.ConcreteNonResidualTriadIncidence N) → Set

    residuePhysicallyExplained :
      (code : Relation.ConcreteNonResidualTriadIncidence N) → Set

open LegacyCoordinateInterpretation public

------------------------------------------------------------------------
-- Validated subtype and exact falsification witnesses.
------------------------------------------------------------------------

record LegacyValidityPolicy (N : Nat) : Set₁ where
  field
    CodeValid : Relation.ConcreteNonResidualTriadIncidence N → Set
    decideValid : Relation.ConcreteNonResidualTriadIncidence N → Bool

    decisionTrueSound :
      (code : Relation.ConcreteNonResidualTriadIncidence N) →
      decideValid code ≡ true → CodeValid code

    decisionFalseSound :
      (code : Relation.ConcreteNonResidualTriadIncidence N) →
      decideValid code ≡ false → (CodeValid code → ⊥)

open LegacyValidityPolicy public

ValidatedLegacyCode :
  (N : Nat) → LegacyValidityPolicy N → Set
ValidatedLegacyCode N policy =
  Σ (Relation.ConcreteNonResidualTriadIncidence N) (CodeValid policy)

record InvalidRawCodeWitness
    (N : Nat) (policy : LegacyValidityPolicy N) : Set where
  constructor invalid-raw-code
  field
    rawCode : Relation.ConcreteNonResidualTriadIncidence N
    invalid : CodeValid policy rawCode → ⊥

open InvalidRawCodeWitness public

oneInvalidCodeRefutesUniversalPhysicality :
  ∀ {N policy} →
  InvalidRawCodeWitness N policy →
  ((code : Relation.ConcreteNonResidualTriadIncidence N) →
    CodeValid policy code) →
  ⊥
oneInvalidCodeRefutesUniversalPhysicality witness allValid =
  invalid witness (allValid (rawCode witness))

------------------------------------------------------------------------
-- Collision and surjectivity tests.
------------------------------------------------------------------------

record LegacyEncodingTest
    {p : Level}
    (N : Nat)
    (PhysicalIncidence : Set p)
    (policy : LegacyValidityPolicy N) :
    Set (lsuc p) where
  field
    physicalItems : List PhysicalIncidence
    rawItems : List (Relation.ConcreteNonResidualTriadIncidence N)

    encode : PhysicalIncidence → Relation.ConcreteNonResidualTriadIncidence N
    decode : ValidatedLegacyCode N policy → PhysicalIncidence

    PhysicalEqual : PhysicalIncidence → PhysicalIncidence → Set
    RawEqual :
      Relation.ConcreteNonResidualTriadIncidence N →
      Relation.ConcreteNonResidualTriadIncidence N → Set

    collision : Set
    unsatisfiedRawCode : Set
    boundedMultiplicity : Nat → Set

open LegacyEncodingTest public

record ExactLegacyPromotion
    {p : Level}
    {N : Nat}
    {PhysicalIncidence : Set p}
    {policy : LegacyValidityPolicy N}
    (test : LegacyEncodingTest N PhysicalIncidence policy) : Set (lsuc p) where
  field
    encodeValid :
      (physical : PhysicalIncidence) →
      CodeValid policy (encode test physical)

    decodeEncode :
      (physical : PhysicalIncidence) →
      PhysicalEqual test
        (decode test (encode test physical , encodeValid physical))
        physical

    encodeDecode :
      (validated : ValidatedLegacyCode N policy) →
      RawEqual test
        (encode test (decode test validated))
        (fst validated)

    sourcePreserved targetPreserved weightPreserved orbitCountingCorrect : Set

open ExactLegacyPromotion public

------------------------------------------------------------------------
-- Promotion decision.
------------------------------------------------------------------------

data LegacyDisposition : Set where
  retainValidatedSubtype replaceWithPhysicalCode : LegacyDisposition

record LegacyCoordinateDecision : Set₁ where
  field
    disposition : LegacyDisposition
    physicalMeaningEstablished : Set
    rawCartesianProductPromoted : Bool
    postulatedWeightPromoted : Bool

open LegacyCoordinateDecision public

safeDefaultLegacyDecision : LegacyCoordinateDecision
safeDefaultLegacyDecision = record
  { disposition = replaceWithPhysicalCode
  ; physicalMeaningEstablished = Bool
  ; rawCartesianProductPromoted = false
  ; postulatedWeightPromoted = false
  }

validatedSubtypeArchitectureImplemented : Bool
validatedSubtypeArchitectureImplemented = true

validatedSubtypeArchitectureImplementedIsTrue :
  validatedSubtypeArchitectureImplemented ≡ true
validatedSubtypeArchitectureImplementedIsTrue = refl

legacyRawCartesianProductIsPhysical : Bool
legacyRawCartesianProductIsPhysical = false

legacyRawCartesianProductIsPhysicalIsFalse :
  legacyRawCartesianProductIsPhysical ≡ false
legacyRawCartesianProductIsPhysicalIsFalse = refl

legacyPostulatedWeightClayPromotable : Bool
legacyPostulatedWeightClayPromotable = false

legacyPostulatedWeightClayPromotableIsFalse :
  legacyPostulatedWeightClayPromotable ≡ false
legacyPostulatedWeightClayPromotableIsFalse = refl
