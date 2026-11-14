module DASHI.Physics.Thermodynamics.ProtectedMagnetocaloricSystem where

open import DASHI.Physics.Thermodynamics.MagnetocaloricMaterial
open import DASHI.Physics.Thermodynamics.CaloricRegenerator
open import DASHI.Physics.Thermodynamics.ActiveMagneticRegenerator

------------------------------------------------------------------------
-- Protected AMR system closure.
--
-- Durability is part of the dynamical validity contract: permeability,
-- magnetic response and channel openness may depend on degradation state.
-- A protection witness is explicitly qualified over an operating interval;
-- it is not an indefinite-lifetime theorem.
------------------------------------------------------------------------

record DegradationModel : Set₁ where
  field
    DegradationState : Set
    Time             : Set
    SafeEnvelope     : DegradationState → Set
    evolves          : Time → DegradationState → DegradationState

    OxidationState   : Set
    CrackState       : Set
    CloggingState    : Set
    CoatingState     : Set

    oxidation        : DegradationState → OxidationState
    cracking         : DegradationState → CrackState
    clogging         : DegradationState → CloggingState
    coating          : DegradationState → CoatingState

record ProtectionStrategy
  (D : DegradationModel) : Set₁ where
  open DegradationModel D
  field
    ProtectionState : Set
    QualifiedTime   : Time → Set
    protects        : ProtectionState → Time → DegradationState → Set

record DegradationFeedback
  {M : MagnetocaloricMaterial}
  {G : RegeneratorGeometry}
  {F : TransferMedium}
  {R : CaloricRegenerator M G F}
  (D : DegradationModel) : Set₁ where
  open DegradationModel D
  open CaloricRegenerator R
  field
    PermeabilityIntegrity : DegradationState → Set
    MagneticIntegrity     : DegradationState → Set
    HydraulicIntegrity    : DegradationState → Set
    ChannelIntegrity      : DegradationState → Set

record QualifiedIntegrity
  {M : MagnetocaloricMaterial}
  {G : RegeneratorGeometry}
  {F : TransferMedium}
  {R : CaloricRegenerator M G F}
  (D : DegradationModel)
  (P : ProtectionStrategy D)
  (B : DegradationFeedback {R = R} D) : Set₁ where
  open DegradationModel D
  open ProtectionStrategy P
  open DegradationFeedback B
  field
    initialState     : DegradationState
    protectionState : ProtectionState
    preservesSafeEnvelope :
      (t : Time) → QualifiedTime t → SafeEnvelope (evolves t initialState)
    preservesPermeability :
      (t : Time) → QualifiedTime t →
      PermeabilityIntegrity (evolves t initialState)
    preservesMagneticResponse :
      (t : Time) → QualifiedTime t →
      MagneticIntegrity (evolves t initialState)
    preservesHydraulics :
      (t : Time) → QualifiedTime t →
      HydraulicIntegrity (evolves t initialState)
    preservesChannels :
      (t : Time) → QualifiedTime t →
      ChannelIntegrity (evolves t initialState)

record CycleEnergyAccounting
  {M : MagnetocaloricMaterial}
  {G : RegeneratorGeometry}
  {F : TransferMedium}
  {R : CaloricRegenerator M G F}
  (C : AMRCycle R) : Set₁ where
  field
    Energy             : Set
    CoolingEnergy      : Set
    RejectedHeat       : Set
    FieldWork          : Set
    PumpWork           : Set
    MotorWork          : Set
    AuxiliaryWork      : Set
    RecoverableWork    : Set
    RecoveredWork      : Set
    NetWork            : Set
    COPCarrier         : Set

    coolingEnergy      : CoolingEnergy
    rejectedHeat       : RejectedHeat
    fieldWork          : FieldWork
    pumpWork           : PumpWork
    motorWork          : MotorWork
    auxiliaryWork      : AuxiliaryWork
    recoverableWork    : RecoverableWork
    recoveredWork      : RecoveredWork
    netWork            : NetWork
    coefficientOfPerformance : COPCarrier

    FirstLawBalance    : Set
    RecoveryBounded    : Set
    COPConsistent      : Set

    firstLawBalance    : FirstLawBalance
    recoveryBounded    : RecoveryBounded
    copConsistent      : COPConsistent

record CycleEntropyAccounting
  {M : MagnetocaloricMaterial}
  {G : RegeneratorGeometry}
  {F : TransferMedium}
  {R : CaloricRegenerator M G F}
  (C : AMRCycle R) : Set₁ where
  field
    EntropyProduction : Set
    Nonnegative       : EntropyProduction → Set
    cycleProduction   : EntropyProduction
    secondLaw         : Nonnegative cycleProduction

record ValidMagnetocaloricCoolingSystem
  {M : MagnetocaloricMaterial}
  {G : RegeneratorGeometry}
  {F : TransferMedium}
  {R : CaloricRegenerator M G F}
  (C : AMRCycle R)
  (D : DegradationModel)
  (P : ProtectionStrategy D)
  (B : DegradationFeedback {R = R} D) : Set₁ where
  field
    materialAdmissible     : Set
    magnetocaloricCompatible : Set
    transportAdmissible    : RegeneratorAdmissibility R
    cycleSynchronised      : AMRSynchronisation C
    periodicState          : AMRPeriodicState C
    producesCooling        : AMRCoolingWitness C
    qualifiedIntegrity     : QualifiedIntegrity D P B
    energyAccounting       : CycleEnergyAccounting C
    entropyAccounting      : CycleEntropyAccounting C

record ProtectedSystemAuthorityBoundary : Set₁ where
  field
    qualifiedDurationIsNotLifetime : Set
    coatingDoesNotByItselfProveSystemIntegrity : Set
    workRecoveryRequiresMechanicalAccounting : Set
    recoveryCannotBeFreeEnergy : Set
    COPRequiresMeasuredOrCalibratedEnergyTerms : Set
    validInterfaceDoesNotProveCommercialSpecification : Set
