module DASHI.Physics.CondensedMatter.FlatBandObservableFibreExact where

------------------------------------------------------------------------
-- GENERIC FLAT-BAND / OBSERVABLE-FIBRE CORE
--
-- This module is intentionally mechanism-neutral.
--
-- A flat band is represented here only at the exact observable level:
-- distinct momentum states may have the same selected energy observation.
-- That is enough to prove non-injectivity of the energy observer and to state
-- a precise consumer-descent obstruction.
--
-- No derivative, group velocity, Kondo mechanism, graphene Hamiltonian,
-- Fe5GeTe2 Hamiltonian, or continuum band calculation is fabricated here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym)

Injective : {A B : Set} -> (A -> B) -> Set
Injective f = ∀ {x y} -> f x ≡ f y -> x ≡ y

record BandSystem (Momentum Energy : Set) : Set₁ where
  constructor band-system
  field
    energy : Momentum -> Energy

open BandSystem public

record FlatPairWitness
    {Momentum Energy : Set}
    (band : BandSystem Momentum Energy) : Set where
  constructor flat-pair-witness
  field
    leftMomentum rightMomentum : Momentum
    sameEnergy :
      energy band leftMomentum ≡ energy band rightMomentum
    distinctMomentum :
      leftMomentum ≡ rightMomentum -> ⊥

open FlatPairWitness public

flatPairRefutesInjectiveEnergy :
  {Momentum Energy : Set} ->
  (band : BandSystem Momentum Energy) ->
  FlatPairWitness band ->
  Injective (energy band) ->
  ⊥
flatPairRefutesInjectiveEnergy band witness injective =
  distinctMomentum witness (injective (sameEnergy witness))

EnergyFibre :
  {Momentum Energy : Set} ->
  (band : BandSystem Momentum Energy) ->
  Momentum ->
  Momentum ->
  Set
EnergyFibre band reference momentum =
  energy band momentum ≡ energy band reference

leftLiesInRightEnergyFibre :
  {Momentum Energy : Set} ->
  {band : BandSystem Momentum Energy} ->
  (witness : FlatPairWitness band) ->
  EnergyFibre band (rightMomentum witness) (leftMomentum witness)
leftLiesInRightEnergyFibre witness = sameEnergy witness

rightLiesInLeftEnergyFibre :
  {Momentum Energy : Set} ->
  {band : BandSystem Momentum Energy} ->
  (witness : FlatPairWitness band) ->
  EnergyFibre band (leftMomentum witness) (rightMomentum witness)
rightLiesInLeftEnergyFibre witness = sym (sameEnergy witness)

record FlatBandPhaseSplitWitness
    {Momentum Energy Phase : Set}
    (band : BandSystem Momentum Energy)
    (phaseObserver : Momentum -> Phase) : Set where
  constructor flat-band-phase-split-witness
  field
    flatPair : FlatPairWitness band
    phaseSeparatesPair :
      phaseObserver (leftMomentum flatPair)
      ≡ phaseObserver (rightMomentum flatPair)
      -> ⊥

open FlatBandPhaseSplitWitness public

PhaseDescendsThroughEnergy :
  {Momentum Energy Phase : Set} ->
  (band : BandSystem Momentum Energy) ->
  (phaseObserver : Momentum -> Phase) ->
  Set
PhaseDescendsThroughEnergy band phaseObserver =
  ∀ {left right} ->
    energy band left ≡ energy band right ->
    phaseObserver left ≡ phaseObserver right

flatBandPhaseSplitRefutesEnergyOnlyDescent :
  {Momentum Energy Phase : Set} ->
  (band : BandSystem Momentum Energy) ->
  (phaseObserver : Momentum -> Phase) ->
  FlatBandPhaseSplitWitness band phaseObserver ->
  PhaseDescendsThroughEnergy band phaseObserver ->
  ⊥
flatBandPhaseSplitRefutesEnergyOnlyDescent
  band phaseObserver witness descent =
  phaseSeparatesPair witness
    (descent (sameEnergy (flatPair witness)))

data FlatteningMechanism : Set where
  registrationEngineeredFlattening : FlatteningMechanism
  interactionDrivenFlattening : FlatteningMechanism

registrationAndInteractionFlatteningAreDistinct :
  registrationEngineeredFlattening ≡ interactionDrivenFlattening -> ⊥
registrationAndInteractionFlatteningAreDistinct ()

record FlatBandPromotionBoundary : Set where
  constructor flat-band-promotion-boundary
  field
    exactEqualEnergyFibreFormalised : Bool
    exactNoninjectivityConsequenceFormalised : Bool
    phaseDescentObstructionFormalised : Bool
    equalEnergyImpliesZeroGroupVelocityClaimed : Bool
    finiteEqualityReplacesContinuumDerivativeClaimed : Bool
    commonTheoremShapeIdentifiesPhysicalMechanism : Bool

open FlatBandPromotionBoundary public

canonicalFlatBandPromotionBoundary : FlatBandPromotionBoundary
canonicalFlatBandPromotionBoundary =
  flat-band-promotion-boundary
    true true true
    false false false
