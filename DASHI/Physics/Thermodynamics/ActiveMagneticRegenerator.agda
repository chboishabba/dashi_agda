module DASHI.Physics.Thermodynamics.ActiveMagneticRegenerator where

open import DASHI.Physics.Thermodynamics.MagnetocaloricMaterial
open import DASHI.Physics.Thermodynamics.CaloricRegenerator

------------------------------------------------------------------------
-- Active Magnetic Regenerator (AMR) cycle semantics.
--
-- The cycle construction itself does not prove useful refrigeration.
-- Cooling, synchronisation and periodic steady state remain explicit
-- witnesses, so a merely well-typed four-phase machine cannot be promoted
-- to a physically successful device.
------------------------------------------------------------------------

data AMRPhase : Set where
  magnetise   : AMRPhase
  hotBlow     : AMRPhase
  demagnetise : AMRPhase
  coldBlow    : AMRPhase

record AMRCycle
  {M : MagnetocaloricMaterial}
  {G : RegeneratorGeometry}
  {F : TransferMedium}
  (R : CaloricRegenerator M G F) : Set₁ where
  open CaloricRegenerator R
  field
    CycleState      : Set
    PhaseOperator   : AMRPhase → Set
    applyPhase      : (p : AMRPhase) → PhaseOperator p → CycleState → CycleState
    regeneratorView : CycleState → RegeneratorState

    magnetiseOp     : PhaseOperator magnetise
    hotBlowOp       : PhaseOperator hotBlow
    demagnetiseOp   : PhaseOperator demagnetise
    coldBlowOp      : PhaseOperator coldBlow

  oneCycle : CycleState → CycleState
  oneCycle s =
    applyPhase coldBlow coldBlowOp
      (applyPhase demagnetise demagnetiseOp
        (applyPhase hotBlow hotBlowOp
          (applyPhase magnetise magnetiseOp s)))

record AMRSynchronisation
  {M : MagnetocaloricMaterial}
  {G : RegeneratorGeometry}
  {F : TransferMedium}
  {R : CaloricRegenerator M G F}
  (C : AMRCycle R) : Set₁ where
  open AMRCycle C
  field
    FieldScheduleCompatible : CycleState → Set
    FlowScheduleCompatible  : CycleState → Set
    PhaseOrderCompatible    : CycleState → Set

    fieldScheduleCompatible :
      (s : CycleState) → FieldScheduleCompatible s
    flowScheduleCompatible :
      (s : CycleState) → FlowScheduleCompatible s
    phaseOrderCompatible :
      (s : CycleState) → PhaseOrderCompatible s

record AMRPeriodicState
  {M : MagnetocaloricMaterial}
  {G : RegeneratorGeometry}
  {F : TransferMedium}
  {R : CaloricRegenerator M G F}
  (C : AMRCycle R) : Set₁ where
  open AMRCycle C
  field
    EquivalentState : CycleState → CycleState → Set
    periodicState   : CycleState
    periodicWitness : EquivalentState (oneCycle periodicState) periodicState

record AMRCoolingWitness
  {M : MagnetocaloricMaterial}
  {G : RegeneratorGeometry}
  {F : TransferMedium}
  {R : CaloricRegenerator M G F}
  (C : AMRCycle R) : Set₁ where
  open AMRCycle C
  field
    CoolingEnergy     : Set
    TemperatureSpan   : Set
    Positive          : CoolingEnergy → Set
    SustainedSpan     : TemperatureSpan → Set

    extractedCooling  : CycleState → CoolingEnergy
    producedSpan      : CycleState → TemperatureSpan

    coolingPositive :
      (s : CycleState) → Positive (extractedCooling s)
    spanSustained :
      (s : CycleState) → SustainedSpan (producedSpan s)

record AMRAuthorityBoundary : Set₁ where
  field
    fourPhaseCycleDoesNotProveCooling : Set
    synchronisationRequiresTimingEvidence : Set
    periodicityRequiresConvergenceOrWitness : Set
    positiveCoolingRequiresBoundaryMeasurementOrModel : Set
    temperatureSpanRequiresHeatLeakAccounting : Set
