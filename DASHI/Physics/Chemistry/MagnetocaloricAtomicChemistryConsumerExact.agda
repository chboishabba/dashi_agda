module DASHI.Physics.Chemistry.MagnetocaloricAtomicChemistryConsumerExact where

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Chemistry.AtomicForceSectorSeparation as Force
import DASHI.Physics.Chemistry.AtomicShellRecurrence as Shell
import DASHI.Physics.Chemistry.AtomicClosedShellSchurBridge as Schur
import DASHI.Physics.Thermodynamics.MagnetocaloricMaterial as MCE

------------------------------------------------------------------------
-- Atomic / chemistry consumer for magnetocaloric materials.
--
-- The existing chemistry lane separates force sectors, atomic shell/valence
-- recurrence, and operator-reduction stability.  This bridge adds the missing
-- material-identity layer: composition, substitution and hydrogenation may
-- change the crystal/magnetic thermodynamics, but no shell or composition fact
-- is itself a measured magnetocaloric response.
------------------------------------------------------------------------

record MagnetocaloricCompositionState : Set₁ where
  field
    Element Species Site : Set
    Composition Substitution Hydrogenation : Set

    elementAt : Site → Element
    speciesAt : Site → Species
    composition : Composition
    substitution : Substitution
    hydrogenation : Hydrogenation

    ChemicallyAdmissible : Set
    chemicallyAdmissible : ChemicallyAdmissible

record AtomicChemistryMagnetocaloricBridge
  (A : Shell.AtomicShellRecurrence)
  (F : Force.AtomicForceSectorSeparation)
  (M : MCE.MagnetocaloricMaterial) : Set₁ where
  open Shell.AtomicShellRecurrence A
  open Force.AtomicForceSectorSeparation F
  open MCE.MagnetocaloricMaterial M
  field
    chemistry : MagnetocaloricCompositionState
    atomicState : AtomicState
    nuclearState : NuclearState
    electronState : ElectronState
    materialState : MaterialState

    forceSectorAdmissible : nuclearAdmissible nuclearState
    electronBound : electromagneticBound (nuclearCharge nuclearState) electronState
    fermionStateAdmissible : fermionAdmissible atomicState

    CompositionIdentifiesMaterial : Set
    AtomicStateCompatible : Set
    ElectronStateCompatible : Set
    ValenceRelevantToMaterial : Set

    compositionIdentifiesMaterial : CompositionIdentifiesMaterial
    atomicStateCompatible : AtomicStateCompatible
    electronStateCompatible : ElectronStateCompatible
    valenceRelevantToMaterial : ValenceRelevantToMaterial

record CompositionToMagnetocaloricCalibration
  {M : MCE.MagnetocaloricMaterial}
  (C : MagnetocaloricCompositionState)
  (R : MCE.MagnetocaloricResponse M) : Set₁ where
  field
    TransitionTemperature : Set
    MagneticPhaseIdentity : Set
    StructuralPhaseIdentity : Set

    transitionTemperature : TransitionTemperature
    magneticPhaseIdentity : MagneticPhaseIdentity
    structuralPhaseIdentity : StructuralPhaseIdentity

    SubstitutionResponseEvidence : Set
    HydrogenationResponseEvidence : Set
    PhaseIdentificationEvidence : Set

    substitutionResponseEvidence : SubstitutionResponseEvidence
    hydrogenationResponseEvidence : HydrogenationResponseEvidence
    phaseIdentificationEvidence : PhaseIdentificationEvidence

record MagnetocaloricAtomicChemistryBoundary : Set where
  constructor magnetocaloric-atomic-chemistry-boundary
  field
    forceSectorSeparationPreserved : Bool
    shellClassDoesNotEqualMaterialResponse : Bool
    valenceStabilityDoesNotProveCurieTemperature : Bool
    compositionDoesNotProveEntropyChange : Bool
    substitutionRequiresResponseCalibration : Bool
    hydrogenationRequiresResponseCalibration : Bool
    schurReductionMaySupplyElectronicStability : Bool
    schurReductionDoesNotSupplyMagnetocaloricResponse : Bool

canonicalMagnetocaloricAtomicChemistryBoundary : MagnetocaloricAtomicChemistryBoundary
canonicalMagnetocaloricAtomicChemistryBoundary =
  magnetocaloric-atomic-chemistry-boundary
    true true true true true true true true
