module DASHI.Physics.Photovoltaic.ConditionalStageDispatchExact where

-- 2026-11-16: temperature-conditional stage dispatch max-cut.
-- The ALL-STAGE-SIMULTANEOUS model is not an optimality theorem.
-- Finite arithmetic and SOURCE-conditional feasibility only.
-- Agda kernel acceptance NOT yet run.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

-- Minimal selected-work comparison, independent of which hardware is named.
minWork : Nat -> Nat -> Nat
minWork zero y = zero
minWork (suc x) zero = zero
minWork (suc x) (suc y) = suc (minWork x y)

minWorkAtMostFirst :
  (a b : Nat) -> Bound._≤_ (minWork a b) a
minWorkAtMostFirst zero b = Bound.z≤n
minWorkAtMostFirst (suc a) zero = Bound.z≤n
minWorkAtMostFirst (suc a) (suc b) =
  Bound.s≤s (minWorkAtMostFirst a b)

minWorkAtMostSecond :
  (a b : Nat) -> Bound._≤_ (minWork a b) b
minWorkAtMostSecond zero b = Bound.z≤n
minWorkAtMostSecond (suc a) zero = Bound.z≤n
minWorkAtMostSecond (suc a) (suc b) =
  Bound.s≤s (minWorkAtMostSecond a b)

-- A temperature-and-capacity receipt must be supplied by the physical
-- stage. Comparing auxiliary work is only meaningful at equal thermal duty
-- and equal PV state; this is a CONDITIONAL same-service comparator.
record EqualServiceChoice : Set where
  constructor equalServiceChoice
  field
    requestedHeatExtraction : Nat
    pvOperatingTemperature : Nat
    stageOneAuxiliaryWork stageTwoAuxiliaryWork : Nat

    StageOneSameServiceFeasible : Set
    StageTwoSameServiceFeasible : Set
    stageOnePaid : StageOneSameServiceFeasible
    stageTwoPaid : StageTwoSameServiceFeasible

open EqualServiceChoice public

selectedMinimumAuxiliary : EqualServiceChoice -> Nat
selectedMinimumAuxiliary r =
  minWork (stageOneAuxiliaryWork r) (stageTwoAuxiliaryWork r)

selectionNoWorseThanFirst :
  (r : EqualServiceChoice) ->
  Bound._≤_ (selectedMinimumAuxiliary r) (stageOneAuxiliaryWork r)
selectionNoWorseThanFirst r =
  minWorkAtMostFirst (stageOneAuxiliaryWork r) (stageTwoAuxiliaryWork r)

selectionNoWorseThanSecond :
  (r : EqualServiceChoice) ->
  Bound._≤_ (selectedMinimumAuxiliary r) (stageTwoAuxiliaryWork r)
selectionNoWorseThanSecond r =
  minWorkAtMostSecond (stageOneAuxiliaryWork r) (stageTwoAuxiliaryWork r)

-- Temperature approach and finite heat-transfer capacity may eliminate an
-- apparent no-compressor route. This explicitly blocks zero-lift infinite flow.
record PassiveSinkAdmission : Set where
  constructor passiveSinkAdmission
  field
    sinkTemperature : Nat
    approachTemperature : Nat
    condenserTemperature : Nat
    condensingTemperatureAboveSink :
      sinkTemperature + approachTemperature ≡ condenserTemperature

    conductanceQuanta : Nat
    rejectedHeatQuanta : Nat
    finiteTransferPaid :
      Bound._≤_ rejectedHeatQuanta (conductanceQuanta * approachTemperature)

open PassiveSinkAdmission public

-- Selected PV cooling work is a PARTITION: only useful-upgraded heat passes
-- the high-lift stage; the ground and passive paths bypass the compressor.
record PVStageDispatch : Set where
  constructor pvStageDispatch
  field
    sourceQualifiedHeatDuty : Nat
    groundDirectHeat : Nat
    ambientPassiveHeat : Nat
    lowLiftEvaporatorHeat : Nat
    highLiftEvaporatorHeat : Nat
    thermalLoadPartition :
      sourceQualifiedHeatDuty
      ≡ groundDirectHeat +
        (ambientPassiveHeat +
        (lowLiftEvaporatorHeat + highLiftEvaporatorHeat))

    groundPumpWork lowLiftCompressorWork highLiftCompressorWork controlWork : Nat
    fullAuxiliaryWork : Nat
    auxiliaryWorkAccounted :
      fullAuxiliaryWork
      ≡ groundPumpWork +
        (lowLiftCompressorWork +
        (highLiftCompressorWork + controlWork))

    lowLiftCondenserHeat highLiftCondenserHeat : Nat
    lowLiftCycleBalance :
      lowLiftCondenserHeat ≡ lowLiftEvaporatorHeat + lowLiftCompressorWork
    highLiftCycleBalance :
      highLiftCondenserHeat ≡ highLiftEvaporatorHeat + highLiftCompressorWork

open PVStageDispatch public

-- Synthetic fixture only; the physical optimum and heat exchanger
-- admission witnesses still require independent measured parameters.
toyParallelStageHeatPartition : PVStageDispatch
toyParallelStageHeatPartition =
  pvStageDispatch
    700 400 200 100 0 refl
    6 10 0 2 18 refl
    110 0 refl refl
