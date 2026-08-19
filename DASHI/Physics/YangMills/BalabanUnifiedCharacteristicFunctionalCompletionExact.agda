module DASHI.Physics.YangMills.BalabanUnifiedCharacteristicFunctionalCompletionExact where

------------------------------------------------------------------------
-- ROUND74: ONE UNIFIED COMPLETED STATE -> ONE CONTINUUM MEASURE
--          VIA A MEASURE-DEFINING CHARACTERISTIC FUNCTIONAL COORDINATE
--
-- STANDARD SOURCE
--
-- R. A. Minlos,
-- "Generalized Random Processes and Their Extension to a Measure",
-- Trudy Moskov. Mat. Obshch. 8 (1959), 497--518.
-- No DOI recorded for the original publication.
--
-- Bochner--Minlos theorem (standard form): on a real nuclear test-function
-- space E, a normalized, positive-definite, nuclear-continuous characteristic
-- functional C is the Fourier transform of a UNIQUE Borel probability measure
-- on E'.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
--
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- TOP-DOWN POINT
--
-- The current unified polymer/Schwinger state has ordinary, composite and
-- connected-correlation projections, but it does NOT yet define a probability
-- measure.  Therefore theorem #4 cannot honestly imply theorem #5 merely from
-- Cauchy completeness.
--
-- The shortest real 4 -> 5 route is to put a characteristic-functional
-- coordinate into the SAME strong state and prove that its limit retains:
--
--   C(0)=1,
--   positive definiteness,
--   continuity in a nuclear test-function topology,
--   Euclidean covariance / reflection positivity in the same limit.
--
-- Bochner--Minlos then constructs the unique continuum measure; the existing
-- ordinary Schwinger projection must be identified with moments/derivatives of
-- THIS SAME characteristic functional.  No independent measure subsequence is
-- allowed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record CharacteristicFunctionalAuthority : Set₁ where
  field
    State TestFunction Characteristic Measure Schwinger : Set

    stateAtScale : Nat → State
    limitState : State

    characteristic : State → Characteristic
    schwinger : State → Schwinger

    StateConverges : (Nat → State) → State → Set
    CharacteristicConverges : (Nat → Characteristic) → Characteristic → Set

    unifiedStateConverges : StateConverges stateAtScale limitState
    characteristicProjectionContinuous :
      StateConverges stateAtScale limitState →
      CharacteristicConverges
        (λ scale → characteristic (stateAtScale scale))
        (characteristic limitState)

    Normalized PositiveDefinite NuclearContinuous : Characteristic → Set
    EuclideanCovariant ReflectionPositive : Characteristic → Set

    -- Closed properties in the convergence topology carried by the strong
    -- state.  These are topological implications, not additional choices of a
    -- limit object.
    normalizedClosed :
      (∀ scale → Normalized (characteristic (stateAtScale scale))) →
      CharacteristicConverges
        (λ scale → characteristic (stateAtScale scale))
        (characteristic limitState) →
      Normalized (characteristic limitState)

    positiveDefiniteClosed :
      (∀ scale → PositiveDefinite (characteristic (stateAtScale scale))) →
      CharacteristicConverges
        (λ scale → characteristic (stateAtScale scale))
        (characteristic limitState) →
      PositiveDefinite (characteristic limitState)

    nuclearContinuousClosed :
      (∀ scale → NuclearContinuous (characteristic (stateAtScale scale))) →
      CharacteristicConverges
        (λ scale → characteristic (stateAtScale scale))
        (characteristic limitState) →
      NuclearContinuous (characteristic limitState)

    euclideanCovariantClosed :
      (∀ scale → EuclideanCovariant (characteristic (stateAtScale scale))) →
      CharacteristicConverges
        (λ scale → characteristic (stateAtScale scale))
        (characteristic limitState) →
      EuclideanCovariant (characteristic limitState)

    reflectionPositiveClosed :
      (∀ scale → ReflectionPositive (characteristic (stateAtScale scale))) →
      CharacteristicConverges
        (λ scale → characteristic (stateAtScale scale))
        (characteristic limitState) →
      ReflectionPositive (characteristic limitState)

    -- Standard Bochner--Minlos constructor on the declared nuclear carrier.
    minlosMeasure : Characteristic → Measure
    IsFourierTransformOf : Characteristic → Measure → Set
    minlos : ∀ C →
      Normalized C → PositiveDefinite C → NuclearContinuous C →
      IsFourierTransformOf C (minlosMeasure C)

    -- Same-family identification: the ordinary Schwinger coordinate must be
    -- the moment/functional-derivative family of the characteristic functional
    -- that constructs the measure.
    SchwingerOfCharacteristic : Characteristic → Schwinger → Set

open CharacteristicFunctionalAuthority public

record FiniteCharacteristicLaws (A : CharacteristicFunctionalAuthority) : Set₁ where
  field
    finiteNormalized : ∀ scale →
      Normalized A (characteristic A (stateAtScale A scale))
    finitePositiveDefinite : ∀ scale →
      PositiveDefinite A (characteristic A (stateAtScale A scale))
    finiteNuclearContinuous : ∀ scale →
      NuclearContinuous A (characteristic A (stateAtScale A scale))
    finiteEuclideanCovariant : ∀ scale →
      EuclideanCovariant A (characteristic A (stateAtScale A scale))
    finiteReflectionPositive : ∀ scale →
      ReflectionPositive A (characteristic A (stateAtScale A scale))

open FiniteCharacteristicLaws public

record UnifiedContinuumMeasureFromCharacteristic
    (A : CharacteristicFunctionalAuthority)
    (finite : FiniteCharacteristicLaws A) : Set₁ where
  field
    limitCharacteristic : Characteristic A
    continuumMeasure : Measure A
    continuumSchwinger : Schwinger A

    limitCharacteristicIsProjection :
      limitCharacteristic ≡ characteristic A (limitState A)
    continuumMeasureIsMinlos :
      continuumMeasure ≡ minlosMeasure A limitCharacteristic
    continuumSchwingerIsProjection :
      continuumSchwinger ≡ schwinger A (limitState A)

    limitNormalized : Normalized A limitCharacteristic
    limitPositiveDefinite : PositiveDefinite A limitCharacteristic
    limitNuclearContinuous : NuclearContinuous A limitCharacteristic
    limitEuclideanCovariant : EuclideanCovariant A limitCharacteristic
    limitReflectionPositive : ReflectionPositive A limitCharacteristic

    measureFourierIdentity :
      IsFourierTransformOf A limitCharacteristic continuumMeasure

    schwingerBelongsToSameCharacteristic :
      SchwingerOfCharacteristic A limitCharacteristic continuumSchwinger

open UnifiedContinuumMeasureFromCharacteristic public

-- Everything except the final same-family Schwinger/moment identity constructs
-- automatically from ONE completed state and closed finite laws.
record SameFamilyMomentIdentification (A : CharacteristicFunctionalAuthority) : Set₁ where
  field
    schwingerAtLimitIsMomentFamily :
      SchwingerOfCharacteristic A
        (characteristic A (limitState A))
        (schwinger A (limitState A))

open SameFamilyMomentIdentification public

assembleUnifiedContinuumMeasure :
  (A : CharacteristicFunctionalAuthority) →
  (finite : FiniteCharacteristicLaws A) →
  SameFamilyMomentIdentification A →
  UnifiedContinuumMeasureFromCharacteristic A finite
assembleUnifiedContinuumMeasure A finite moments =
  let
    convergence = characteristicProjectionContinuous A (unifiedStateConverges A)
    normalized = normalizedClosed A (finiteNormalized finite) convergence
    positive = positiveDefiniteClosed A (finitePositiveDefinite finite) convergence
    continuous = nuclearContinuousClosed A (finiteNuclearContinuous finite) convergence
    euclidean = euclideanCovariantClosed A (finiteEuclideanCovariant finite) convergence
    reflection = reflectionPositiveClosed A (finiteReflectionPositive finite) convergence
  in
  record
    { limitCharacteristic = characteristic A (limitState A)
    ; continuumMeasure = minlosMeasure A (characteristic A (limitState A))
    ; continuumSchwinger = schwinger A (limitState A)
    ; limitCharacteristicIsProjection = refl
    ; continuumMeasureIsMinlos = refl
    ; continuumSchwingerIsProjection = refl
    ; limitNormalized = normalized
    ; limitPositiveDefinite = positive
    ; limitNuclearContinuous = continuous
    ; limitEuclideanCovariant = euclidean
    ; limitReflectionPositive = reflection
    ; measureFourierIdentity = minlos A
        (characteristic A (limitState A)) normalized positive continuous
    ; schwingerBelongsToSameCharacteristic =
        schwingerAtLimitIsMomentFamily moments
    }

bochnerMinlosMeasureConstructionLevel : ProofLevel
bochnerMinlosMeasureConstructionLevel = standardImported

unifiedCharacteristicNoSplicingAssemblyLevel : ProofLevel
unifiedCharacteristicNoSplicingAssemblyLevel = machineChecked

-- EXACT 4 -> 5 HOLES exposed by the backwards compiler:
--
-- (a) strengthen theorem #4's state/norm so the characteristic-functional
--     projection has the same summable RG modulus;
-- (b) prove nuclear continuity is uniform/closed in that topology;
-- (c) identify the existing ordinary Schwinger projection with the moment
--     family of the limiting characteristic functional;
-- (d) feed the resulting reflection-positive Euclidean characteristic family
--     into the existing OS reconstruction theorem.
--
-- Once (a)--(d) are proved, `SameFamilyContinuumOSCompletion` is downstream of
-- the strengthened unified RG theorem and the authoritative analytic count can
-- genuinely drop by one.
physicalUnifiedCharacteristicCoordinateLevel : ProofLevel
physicalUnifiedCharacteristicCoordinateLevel = conditional

physicalNuclearContinuityClosureLevel : ProofLevel
physicalNuclearContinuityClosureLevel = conditional

physicalSchwingerMomentIdentificationLevel : ProofLevel
physicalSchwingerMomentIdentificationLevel = conditional

physicalCharacteristicToOSReconstructionLevel : ProofLevel
physicalCharacteristicToOSReconstructionLevel = conditional
