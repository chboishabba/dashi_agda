module DASHI.Physics.Propulsion.JetEngineFlowArchitectureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- JET-ENGINE FLOW ARCHITECTURE
--
-- This owner formalises the same-object station chain and the engineering
-- dependency structure of a gas-turbine jet engine.  It intentionally does
-- not promote an ideal thermodynamic cycle into a claim about any particular
-- certified engine, aircraft, fuel burn, or mission.
------------------------------------------------------------------------

data EngineStation : Set where
  ambient : EngineStation
  inlet : EngineStation
  compressorExit : EngineStation
  combustorExit : EngineStation
  turbineExit : EngineStation
  nozzleExit : EngineStation

data EngineComponent : Set where
  inletComponent : EngineComponent
  compressor : EngineComponent
  combustor : EngineComponent
  turbine : EngineComponent
  shaft : EngineComponent
  nozzle : EngineComponent

data EngineObservable : Set where
  massFlow : EngineObservable
  pressure : EngineObservable
  temperature : EngineObservable
  velocity : EngineObservable
  shaftPower : EngineObservable
  fuelFlow : EngineObservable
  vibration : EngineObservable
  rotationalSpeed : EngineObservable

record EngineState : Set where
  constructor engine-state
  field
    station : EngineStation
    massFlowCode : Nat
    pressureCode : Nat
    temperatureCode : Nat
    velocityCode : Nat

open EngineState public

record FlowTransition : Set where
  constructor flow-transition
  field
    component : EngineComponent
    from : EngineStation
    to : EngineStation
    retainedMassFlowIdentity : Bool
    sourceModel : String

open FlowTransition public

inletTransition : FlowTransition
inletTransition =
  flow-transition inletComponent ambient inlet true
    "same working-fluid carrier across the inlet boundary"

compressionTransition : FlowTransition
compressionTransition =
  flow-transition compressor inlet compressorExit true
    "compressor raises stagnation-state pressure using shaft work"

combustionTransition : FlowTransition
combustionTransition =
  flow-transition combustor compressorExit combustorExit false
    "combustor adds fuel mass and chemical heat release to the gas path"

turbineTransition : FlowTransition
turbineTransition =
  flow-transition turbine combustorExit turbineExit true
    "turbine extracts gas-path work to drive the compressor through the shaft"

nozzleTransition : FlowTransition
nozzleTransition =
  flow-transition nozzle turbineExit nozzleExit true
    "nozzle converts available stagnation enthalpy/pressure into exhaust momentum"

------------------------------------------------------------------------
-- Same-object execution: the stations belong to one engine pass.  The Nat
-- coordinates are deliberately dimensionless placeholders.  A later numeric
-- producer may bind them to SI-valued thermodynamic measurements without
-- changing the architecture.
------------------------------------------------------------------------

record JetEngineExecution : Set where
  constructor jet-engine-execution
  field
    ambientState : EngineState
    inletState : EngineState
    compressorState : EngineState
    combustorState : EngineState
    turbineState : EngineState
    nozzleState : EngineState
    inletEdge : FlowTransition
    compressorEdge : FlowTransition
    combustorEdge : FlowTransition
    turbineEdge : FlowTransition
    nozzleEdge : FlowTransition

open JetEngineExecution public

------------------------------------------------------------------------
-- Conservation / performance receipt surfaces.
------------------------------------------------------------------------

record MassBalanceReceipt : Set where
  constructor mass-balance-receipt
  field
    airMassFlowCode : Nat
    fuelMassFlowCode : Nat
    exhaustMassFlowCode : Nat
    balanceChecked : Bool

record ShaftWorkReceipt : Set where
  constructor shaft-work-receipt
  field
    compressorWorkCode : Nat
    turbineWorkCode : Nat
    accessoryWorkCode : Nat
    shaftBalanceChecked : Bool

record MomentumThrustReceipt : Set where
  constructor momentum-thrust-receipt
  field
    inletMomentumCode : Nat
    exhaustMomentumCode : Nat
    pressureThrustCode : Nat
    thrustBalanceChecked : Bool

record EnginePerformanceReceipt : Set where
  constructor engine-performance-receipt
  field
    massBalance : MassBalanceReceipt
    shaftBalance : ShaftWorkReceipt
    thrustBalance : MomentumThrustReceipt
    sameExecution : Bool

------------------------------------------------------------------------
-- BIDI / WrongType firewalls.
------------------------------------------------------------------------

data HeatInputImpliesThrustPermission : Set where

data CompressorPressureRatioImpliesEngineEfficiencyPermission : Set where

data IdealCycleImpliesCertifiedEnginePerformancePermission : Set where

data RatedPerformanceImpliesMissionFuelBurnPermission : Set where

data ComponentEfficiencyImpliesAbsoluteFuelDeclinePermission : Set where

heatInputDoesNotByItselfProveThrust : HeatInputImpliesThrustPermission → ⊥
heatInputDoesNotByItselfProveThrust ()

pressureRatioDoesNotByItselfProveEngineEfficiency :
  CompressorPressureRatioImpliesEngineEfficiencyPermission → ⊥
pressureRatioDoesNotByItselfProveEngineEfficiency ()

idealCycleDoesNotAutoPromoteToCertifiedPerformance :
  IdealCycleImpliesCertifiedEnginePerformancePermission → ⊥
idealCycleDoesNotAutoPromoteToCertifiedPerformance ()

ratedPerformanceDoesNotAutoPromoteToMissionFuelBurn :
  RatedPerformanceImpliesMissionFuelBurnPermission → ⊥
ratedPerformanceDoesNotAutoPromoteToMissionFuelBurn ()

componentEfficiencyDoesNotProveAbsoluteFuelDecline :
  ComponentEfficiencyImpliesAbsoluteFuelDeclinePermission → ⊥
componentEfficiencyDoesNotProveAbsoluteFuelDecline ()

------------------------------------------------------------------------
-- Reverse-search obligations.  A claimed engine-level result routes back to
-- the exact physical producer that must be acquired or measured.
------------------------------------------------------------------------

data JetEngineReverseTarget : Set where
  acquireStationThermodynamics : JetEngineReverseTarget
  acquireMassFlow : JetEngineReverseTarget
  acquireFuelFlow : JetEngineReverseTarget
  acquireShaftPower : JetEngineReverseTarget
  acquireNozzleExitState : JetEngineReverseTarget
  acquireInstalledPerformance : JetEngineReverseTarget
  acquireMissionProfile : JetEngineReverseTarget
  acquireCertificationEnvelope : JetEngineReverseTarget

record JetEngineReverseObligation : Set where
  constructor jet-engine-reverse-obligation
  field
    target : JetEngineReverseTarget
    preferredEvidence : String
    promotes : String
    cannotPromote : String

open JetEngineReverseObligation public
