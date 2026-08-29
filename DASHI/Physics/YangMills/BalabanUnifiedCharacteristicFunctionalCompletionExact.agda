module DASHI.Physics.YangMills.BalabanUnifiedCharacteristicFunctionalCompletionExact where

------------------------------------------------------------------------
-- ROUND75: ONE UNIFIED COMPLETED STATE -> ONE CONTINUUM MEASURE
--          VIA A MEASURE-DEFINING CHARACTERISTIC FUNCTIONAL COORDINATE
--
-- STANDARD SOURCES
--
-- R. A. Minlos,
-- "Generalized Random Processes and Their Extension to a Measure",
-- Trudy Moskov. Mat. Obshch. 8 (1959), 497--518.
-- No DOI recorded for the original publication.
--
-- Julien Fageot, Arash Amini, Michael Unser,
-- "On the Continuity of Characteristic Functionals and Sparse Stochastic
-- Modeling", Journal of Fourier Analysis and Applications 20 (2014),
-- 1179--1211. DOI: 10.1007/s00041-014-9351-4.
-- Their Theorem 1 gives the exact Minlos--Bochner criterion used here:
-- normalized + positive-definite + continuous on a nuclear test space gives a
-- unique probability measure on the topological dual.
--
-- Jose Velhinho,
-- "Topics of Measure Theory on Infinite Dimensional Spaces", 2023,
-- arXiv:2312.04365. DOI: 10.48550/arXiv.2312.04365.
-- This source is used for the Hilbertian/nuclear-topology presentation and the
-- support interpretation on the topological dual.
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
-- connected-correlation projections, but it does NOT define a probability
-- measure merely by being Cauchy. The shortest real 4 -> 5 route is to put a
-- characteristic-functional coordinate into the SAME strong state and prove
-- that its limit retains:
--
--   C(0)=1,
--   positive definiteness,
--   continuity in a nuclear test-function topology,
--   Euclidean covariance,
--   reflection positivity,
--   locality.
--
-- Bochner--Minlos then constructs the unique continuum measure; the existing
-- ordinary Schwinger projection must be identified with moments/derivatives of
-- THIS SAME characteristic functional. No independent measure subsequence is
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
    EuclideanCovariant ReflectionPositive Local : Characteristic → Set

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

    localityClosed :
      (∀ scale → Local (characteristic (stateAtScale scale))) →
      CharacteristicConverges
        (λ scale → characteristic (stateAtScale scale))
        (characteristic limitState) →
      Local (characteristic limitState)

    minlosMeasure : Characteristic → Measure
    IsFourierTransformOf : Characteristic → Measure → Set
    minlos : ∀ C →
      Normalized C → PositiveDefinite C → NuclearContinuous C →
      IsFourierTransformOf C (minlosMeasure C)

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
    finiteLocal : ∀ scale →
      Local A (characteristic A (stateAtScale A scale))

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
    limitLocal : Local A limitCharacteristic

    measureFourierIdentity :
      IsFourierTransformOf A limitCharacteristic continuumMeasure

    schwingerBelongsToSameCharacteristic :
      SchwingerOfCharacteristic A limitCharacteristic continuumSchwinger

open UnifiedContinuumMeasureFromCharacteristic public

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
    local = localityClosed A (finiteLocal finite) convergence
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
    ; limitLocal = local
    ; measureFourierIdentity = minlos A
        (characteristic A (limitState A)) normalized positive continuous
    ; schwingerBelongsToSameCharacteristic =
        schwingerAtLimitIsMomentFamily moments
    }

bochnerMinlosMeasureConstructionLevel : ProofLevel
bochnerMinlosMeasureConstructionLevel = standardImported

unifiedCharacteristicNoSplicingAssemblyLevel : ProofLevel
unifiedCharacteristicNoSplicingAssemblyLevel = machineChecked

-- ROUND75 reduction of the old 4 -> 5 leaf:
--
-- (a) theorem #4 must carry one characteristic-functional coordinate with the
--     SAME summable increment modulus;
-- (b) `BalabanCharacteristicNuclearContinuityTransportExact` proves that one
--     Hilbertian continuity modulus transports to the stronger nuclear topology
--     once the test-space refinement is instantiated;
-- (c) finite-scale normalization, positivity, Euclidean covariance, reflection
--     positivity and locality are closed on the same characteristic limit;
-- (d) the Schwinger coordinate is identified with moments of that same limit;
-- (e) standard OS reconstruction consumes those same-limit OS data.
--
-- There is therefore no trace-class Hilbert-space covariance gate on this
-- nuclear-dual route. Trace class is a different construction route.
physicalUnifiedCharacteristicCoordinateLevel : ProofLevel
physicalUnifiedCharacteristicCoordinateLevel = conditional

physicalCommonHilbertianCharacteristicModulusLevel : ProofLevel
physicalCommonHilbertianCharacteristicModulusLevel = conditional

physicalSchwingerMomentIdentificationLevel : ProofLevel
physicalSchwingerMomentIdentificationLevel = conditional

physicalCharacteristicToOSReconstructionLevel : ProofLevel
physicalCharacteristicToOSReconstructionLevel = conditional
