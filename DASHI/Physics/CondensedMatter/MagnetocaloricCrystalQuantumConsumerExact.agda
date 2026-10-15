module DASHI.Physics.CondensedMatter.MagnetocaloricCrystalQuantumConsumerExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Mathematics.Symmetry.KleinGroupActionInvariantExact as Symmetry
import DASHI.Physics.CondensedMatter.FlatBandObservableFibreExact as Fibre
import DASHI.Physics.Thermodynamics.MagnetocaloricMaterial as MCE

------------------------------------------------------------------------
-- Condensed-matter consumer for the magnetocaloric lane.
--
-- Existing DASHI crystal/altermagnet work keeps site, momentum, spin and
-- measurement channels separate and already factors crystal actions through
-- the reusable GroupAction surface.  This bridge applies the same rule to a
-- magnetocaloric material: crystal phase, magnetic order, electronic state,
-- band energy and thermodynamic response are projections of a shared carrier,
-- not definitionally identical observables.
------------------------------------------------------------------------

record MagnetocaloricCrystalConsumer
  (M : MCE.MagnetocaloricMaterial) : Set₁ where
  open MCE.MagnetocaloricMaterial M
  field
    Momentum ElectronicEnergy ElectronicState : Set
    CrystalPhase MagneticOrder : Set

    band : Fibre.BandSystem Momentum ElectronicEnergy
    momentumOf : MaterialState → Momentum
    electronicState : MaterialState → ElectronicState
    crystalPhase : MaterialState → CrystalPhase
    magneticOrder : MaterialState → MagneticOrder

    crystalAction : Symmetry.GroupAction
    magneticAction : Symmetry.GroupAction
    CrystalActionIdentification : Set
    MagneticActionIdentification : Set
    crystalActionIdentification : CrystalActionIdentification
    magneticActionIdentification : MagneticActionIdentification

    CrystalIdentificationAdmissible : MaterialState → Set
    MagneticIdentificationAdmissible : MaterialState → Set
    ElectronicIdentificationAdmissible : MaterialState → Set

    crystalIdentificationAdmissible :
      (s : MaterialState) → OperatingRegime s → CrystalIdentificationAdmissible s
    magneticIdentificationAdmissible :
      (s : MaterialState) → OperatingRegime s → MagneticIdentificationAdmissible s
    electronicIdentificationAdmissible :
      (s : MaterialState) → OperatingRegime s → ElectronicIdentificationAdmissible s

  bandEnergyOf : MaterialState → ElectronicEnergy
  bandEnergyOf s = Fibre.energy band (momentumOf s)

  SameBandEnergy : MaterialState → MaterialState → Set
  SameBandEnergy x y = bandEnergyOf x ≡ bandEnergyOf y

record CrystalToMagnetocaloricResponseBridge
  {M : MCE.MagnetocaloricMaterial}
  (C : MagnetocaloricCrystalConsumer M)
  (R : MCE.MagnetocaloricResponse M) : Set₁ where
  open MCE.MagnetocaloricMaterial M
  field
    MicroscopicModel : Set
    FreeEnergyModel : Set
    PartitionOrStateWeighting : Set

    microscopicModel : MaterialState → MicroscopicModel
    freeEnergyModel : MaterialState → FreeEnergyModel
    stateWeighting : MaterialState → PartitionOrStateWeighting

    SymmetryCompatible : MaterialState → Set
    ThermodynamicProjectionCompatible : MaterialState → Set
    CalibratedForMaterial : MaterialState → Set

    symmetryCompatible :
      (s : MaterialState) → OperatingRegime s → SymmetryCompatible s
    thermodynamicProjectionCompatible :
      (s : MaterialState) → OperatingRegime s → ThermodynamicProjectionCompatible s
    calibratedForMaterial :
      (s : MaterialState) → OperatingRegime s → CalibratedForMaterial s

record MagnetocaloricCondensedMatterBoundary : Set where
  constructor magnetocaloric-condensed-matter-boundary
  field
    sharedCarrierDoesNotIdentifyObservables : Bool
    crystalActionRequiresPhysicalIdentification : Bool
    magneticActionRequiresPhysicalIdentification : Bool
    crystalSymmetryDoesNotDetermineCaloricMagnitude : Bool
    bandEnergyDoesNotDetermineMagneticOrder : Bool
    magneticOrderDoesNotDetermineEntropyChangeWithoutModel : Bool
    microscopicModelRequiresThermodynamicProjection : Bool
    thermodynamicProjectionRequiresMaterialCalibration : Bool

canonicalMagnetocaloricCondensedMatterBoundary : MagnetocaloricCondensedMatterBoundary
canonicalMagnetocaloricCondensedMatterBoundary =
  magnetocaloric-condensed-matter-boundary
    true true true true true true true true
