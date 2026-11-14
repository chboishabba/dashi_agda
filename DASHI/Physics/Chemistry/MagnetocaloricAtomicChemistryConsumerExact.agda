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

------------------------------------------------------------------------
-- Protection chemistry is a second material identity, not a footnote to the
-- magnetic alloy.  Coating, inhibitor and heat-transfer-fluid chemistry are
-- therefore explicit inputs to corrosion and interface-integrity evidence.
------------------------------------------------------------------------

record MagnetocaloricProtectionChemistry : Set₁ where
  field
    Substrate Coating Inhibitor TransferFluid : Set
    CorrosionState InterfaceState : Set

    substrate : Substrate
    coating : Coating
    inhibitor : Inhibitor
    transferFluid : TransferFluid

    initialCorrosionState : CorrosionState
    initialInterfaceState : InterfaceState

    CorrosionCompatibility : Set
    CoatingAdhesionEvidence : Set
    FluidCompatibilityEvidence : Set
    InhibitorEffectEvidence : Set

    corrosionCompatibility : CorrosionCompatibility
    coatingAdhesionEvidence : CoatingAdhesionEvidence
    fluidCompatibilityEvidence : FluidCompatibilityEvidence
    inhibitorEffectEvidence : InhibitorEffectEvidence

record ProtectionChemistryDegradationBridge
  (P : MagnetocaloricProtectionChemistry) : Set₁ where
  open MagnetocaloricProtectionChemistry P
  field
    Time : Set
    corrosionState : Time → CorrosionState
    interfaceState : Time → InterfaceState

    QualifiedInterval : Time → Set
    ChannelBlockingRisk : Time → Set
    MagneticMaterialLossRisk : Time → Set
    ThermalContactRisk : Time → Set

    corrosionQualified :
      (t : Time) → QualifiedInterval t → Set
    channelBlockingControlled :
      (t : Time) → QualifiedInterval t → ChannelBlockingRisk t → Set
    magneticMaterialLossControlled :
      (t : Time) → QualifiedInterval t → MagneticMaterialLossRisk t → Set
    thermalContactControlled :
      (t : Time) → QualifiedInterval t → ThermalContactRisk t → Set

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
    coatingIdentityIsSeparateFromSubstrateIdentity : Bool
    corrosionProtectionRequiresQualifiedEvidence : Bool

canonicalMagnetocaloricAtomicChemistryBoundary : MagnetocaloricAtomicChemistryBoundary
canonicalMagnetocaloricAtomicChemistryBoundary =
  magnetocaloric-atomic-chemistry-boundary
    true true true true true true true true true true
