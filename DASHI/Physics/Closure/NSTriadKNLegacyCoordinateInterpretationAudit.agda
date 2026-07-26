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

record LegacyCoordinateInterpretation
    (N : Nat)
    (policy : LegacyValidityPolicy N) : Set₁ where
  field
    headMeaning tailMeaning residueMeaning :
      Relation.ConcreteNonResidualTriadIncidence N → CoordinateMeaning

    -- Reconstruction is deliberately available only after validity has been
    -- established.  Invalid raw Cartesian tuples remain falsification data.
    reconstruct :
      ValidatedLegacyCode N policy →
      Physical.PhysicalTriadIncidence

    reconstructedInCutoff :
      (code : ValidatedLegacyCode N policy) →
      Physical.PhysicalTriadInCutoff N (reconstruct code)

    headPhysicallyPreserved :
      (code : ValidatedLegacyCode N policy) → Set

    tailPhysicallyPreserved :
      (code : ValidatedLegacyCode N policy) → Set

    residuePhysicallyExplained :
      (code : ValidatedLegacyCode N policy) → Set

    reconstructedClassSound :
      (code : ValidatedLegacyCode N policy) → Set

open LegacyCoordinateInterpretation public

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

    collisionWitnessOrInjective : Set
    invalidRawWitnessOrSurjective : Set
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

record LegacyCoordinateDecision : Set where
  field
    disposition : LegacyDisposition
    physicalMeaningEstablished : Bool
    rawCartesianProductPromoted : Bool
    postulatedWeightPromoted : Bool

open LegacyCoordinateDecision public

safeDefaultLegacyDecision : LegacyCoordinateDecision
safeDefaultLegacyDecision = record
  { disposition = replaceWithPhysicalCode
  ; physicalMeaningEstablished = false
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
