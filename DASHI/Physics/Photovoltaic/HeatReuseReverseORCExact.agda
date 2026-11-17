module DASHI.Physics.Photovoltaic.HeatReuseReverseORCExact where

-- 2026-11-16. Heat-service displacement and reversible HP/ORC cross-pollination.
-- Source-written conditional thermodynamic interface; no physical calibration
-- and no local Agda kernel acceptance has been performed.
--
-- Historical experimental prior art (not attributable to DASHI):
-- Ravindran et al. (2024), DOI 10.1016/j.applthermaleng.2024.124237
-- Dumont et al. (2015), DOI 10.1016/j.ijrefrig.2015.03.008
-- Treat scroll-expander operation as a different machine mode from compressor
-- operation; never treat reversing an electric motor as proof of a heat engine.

open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

data ThermalMode : Set where
  pvCooling groundHeatReuse heatPumpService organicRankineGenerator
    thermalStorage heatRejected : ThermalMode

-- The incoming solar heat is partitioned across physically different
-- heat-treatment pathways. A hot stream produced by a heat pump is not
-- counted again as a newly acquired solar input.
record ThermalCascade : Set where
  constructor thermalCascade
  field
    pvAvailableHeat : Nat
    directHeatDelivered : Nat
    heatPumpColdIntake : Nat
    sourceHotORCIntake : Nat
    groundRejected : Nat
    thermalStored : Nat

    primaryPartition :
      pvAvailableHeat
      ≡ directHeatDelivered
        + (heatPumpColdIntake
        + (sourceHotORCIntake + (groundRejected + thermalStored)))

    hpElectricalWork : Nat
    hpHotHeat : Nat
    hpFirstLaw : heatPumpColdIntake + hpElectricalWork ≡ hpHotHeat

    upgradedDelivered : Nat
    upgradedORCIntake : Nat
    hpHotPartition : hpHotHeat ≡ upgradedDelivered + upgradedORCIntake

    orcHotInput orcElectricalOutput orcColdReject : Nat
    orcFeed : orcHotInput ≡ sourceHotORCIntake + upgradedORCIntake
    orcFirstLaw : orcHotInput ≡ orcElectricalOutput + orcColdReject

open ThermalCascade public

orcWorkDoesNotExceedHotHeat : (c : ThermalCascade) ->
  Bound._≤_ (orcElectricalOutput c) (orcHotInput c)
orcWorkDoesNotExceedHotHeat c =
  Bound.transportUpper (Bound.sym (orcFirstLaw c))
    (Bound.≤-append (orcElectricalOutput c) (orcColdReject c))

-- Second-law qualification is distinct from a first-law energy identity.
-- Caller must supply an independently justified temperature/exergy bound.
record ORCSourceTemperatureGate (c : ThermalCascade) : Set where
  field
    coldAbsoluteK : Nat
    temperatureLiftK : Nat
    hotAbsoluteK : Nat
    hotTemperatureIsColdPlusLift :
      coldAbsoluteK + temperatureLiftK ≡ hotAbsoluteK

    -- Cross-multiplied Carnot inequality, avoiding inexact rational truncation.
    secondLawReceipt :
      Bound._≤_
        (orcElectricalOutput c * hotAbsoluteK)
        (orcHotInput c * temperatureLiftK)

-- A heating displacement must be compared at the SAME delivered heat demand,
-- output temperatures and measurement window. Counterfactual electricity is
-- an independent measurement, not created by an ORC conservation proof.
record SameServiceHeatingCounterfactual : Set where
  constructor sameServiceHeatingCounterfactual
  field
    serviceHeatDemand : Nat
    recoveredHeatDelivered : Nat
    originalHeaterDelivered : Nat
    residualHeaterDelivered : Nat
    serviceMatchBefore : originalHeaterDelivered ≡ serviceHeatDemand
    serviceMatchAfter :
      recoveredHeatDelivered + residualHeaterDelivered ≡ serviceHeatDemand

    originalHeatingElectricity : Nat
    newHeatingElectricity : Nat
    serviceUpgradeElectricity : Nat
    pumpingElectricity : Nat

    -- Separate upward/downward deltas prevent assuming savings are positive.
    increaseInElectricity : Nat
    avoidedElectricity : Nat
    signedSavingsReceipt :
      originalHeatingElectricity + increaseInElectricity
      ≡ newHeatingElectricity
        + (serviceUpgradeElectricity + (pumpingElectricity + avoidedElectricity))

-- One synthetic example: 700 heat quanta, 400 directly delivered,
-- 200 sent to heat pump with 40 external work, 100 rejected.
-- 240 upgraded heat delivered. No electric ORC output is claimed.
syntheticHeatReuseNotGeneration : ThermalCascade
syntheticHeatReuseNotGeneration =
  thermalCascade 700 400 200 0 100 0 refl
    40 240 refl 240 0 refl
    0 0 0 refl refl

-- Independent thermal source that is hot enough can be admitted to ORC.
-- This synthetic energy split does not prove it is at a usable temperature.
syntheticHotORC : ThermalCascade
syntheticHotORC =
  thermalCascade 700 0 0 700 0 0 refl
    0 0 refl 0 0 refl
    700 21 679 refl refl

-- In the previous fixture, before/after heating demand is 640 units.
-- The baseline uses 640 electricity-equivalent units, the recovered
-- 640 units of heat leave no electrical heating requirement, but cost 40
-- in service-upgrade work. The resulting 600-unit avoidance is conditional
-- on the assumed baseline being resistive electric heat.
syntheticResistiveDisplacement : SameServiceHeatingCounterfactual
syntheticResistiveDisplacement =
  sameServiceHeatingCounterfactual
    640 640 640 0 refl refl
    640 0 40 0
    0 600 refl

-- This module does not assign value to heat without a same-temperature,
-- same-service demand/counterfactual receipt. The source can route heat
-- to the user, store it, or drive an independently hot ORC branch.
