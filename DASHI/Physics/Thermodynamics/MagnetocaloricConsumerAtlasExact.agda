module DASHI.Physics.Thermodynamics.MagnetocaloricConsumerAtlasExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Units.MagnetocaloricSIConsumerExact as SI
import DASHI.Physics.Electromagnetism.MagnetocaloricFieldConsumerExact as EM
import DASHI.Physics.CondensedMatter.MagnetocaloricCrystalQuantumConsumerExact as CM
import DASHI.Physics.Chemistry.MagnetocaloricAtomicChemistryConsumerExact as Chem
import DASHI.Physics.Quantum.MagnetocaloricQuantumStatMechConsumerExact as Quantum
import DASHI.Physics.Thermodynamics.MagnetocaloricContinuumConsumerExact as Fluid

------------------------------------------------------------------------
-- Reachability/status atlas for the magnetocaloric vertical slice.
------------------------------------------------------------------------

data ReuseRole : Set where
  directPhysicalConsumer : ReuseRole
  structuralPrecedentOnly : ReuseRole
  explicitlyNotAConsumer : ReuseRole

record MagnetocaloricConsumerAtlas : Set where
  constructor magnetocaloric-consumer-atlas
  field
    siMetrologyPopulated : Bool
    electromagnetismPopulated : Bool
    condensedMatterPopulated : Bool
    atomicChemistryPopulated : Bool
    quantumStatMechPopulated : Bool
    continuumTransportPopulated : Bool

    navierStokesRole : ReuseRole
    yangMillsRole : ReuseRole

canonicalMagnetocaloricConsumerAtlas : MagnetocaloricConsumerAtlas
canonicalMagnetocaloricConsumerAtlas =
  magnetocaloric-consumer-atlas
    true true true true true true
    structuralPrecedentOnly
    structuralPrecedentOnly

record MagnetocaloricCrossDomainPromotionBoundary : Set where
  constructor magnetocaloric-cross-domain-promotion-boundary
  field
    siTypingIsNotCalibration : Bool
    u1FieldSocketIsNotMaterialLaw : Bool
    crystalSymmetryIsNotCaloricMagnitude : Bool
    atomicStructureIsNotBulkResponse : Bool
    quantumHamiltonianIsNotBulkThermodynamics : Bool
    continuumInterfaceIsNotClayRegularity : Bool
    nonAbelianYMIsNotApplicationMagnetism : Bool

canonicalMagnetocaloricCrossDomainPromotionBoundary :
  MagnetocaloricCrossDomainPromotionBoundary
canonicalMagnetocaloricCrossDomainPromotionBoundary =
  magnetocaloric-cross-domain-promotion-boundary
    true true true true true true true

navierStokesIsStructuralOnly :
  MagnetocaloricConsumerAtlas.navierStokesRole canonicalMagnetocaloricConsumerAtlas
  ≡ structuralPrecedentOnly
navierStokesIsStructuralOnly = refl

yangMillsIsStructuralOnly :
  MagnetocaloricConsumerAtlas.yangMillsRole canonicalMagnetocaloricConsumerAtlas
  ≡ structuralPrecedentOnly
yangMillsIsStructuralOnly = refl
