module DASHI.Control.ZhangDaibingControlDataReplayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Control.ZhangDaibingUAVControlBidiExact as Base

------------------------------------------------------------------------
-- ZHANG DAIBING / UAV CARRIER-LANDING SOURCE-DATA REPLAY SURFACE
-- DOI 10.13700/j.bh.1001-5965.2016.0679.
--
-- The public article page exposes the exact control architecture and
-- optimisation/validation topology, but not all numerical controller gains or
-- simulation time series in the indexed surface.
------------------------------------------------------------------------

record ZhangDaibingControlDataReplay : Set where
  constructor zhang-daibing-control-data-replay
  field
    sourceReference : String
    task : String
    disturbances : String
    proposedControlStructure : String
    optimisationMethod : String
    optimisationPriority : String
    objective : String
    disturbanceSpectraUsed : Bool
    comparedAgainstRegularStructure : Bool
    calculationAndSimulationValidationReported : Bool
    exactControllerGainsPaid : Bool
    exactVehicleModelPaid : Bool
    exactTouchdownDispersionSeriesPaid : Bool

open ZhangDaibingControlDataReplay public

zhangDaibingControlDataReplay : ZhangDaibingControlDataReplay
zhangDaibingControlDataReplay = zhang-daibing-control-data-replay
  "DOI 10.13700/j.bh.1001-5965.2016.0679"
  "high-precision longitudinal flight control for UAV carrier landing"
  "carrier air-wake disturbance plus deck-motion disturbance"
  "direct force control (DFC) with multiple control surfaces"
  "particle swarm optimisation (PSO) of control-law parameters"
  "stability margin satisfied before touchdown-dispersion minimisation"
  "minimise touchdown-point dispersion under the combined landing environment"
  true
  true
  true
  false
  false
  false

existingControlPipeline : Base.UAVControlPipeline
existingControlPipeline = Base.canonicalZhangDaibingControlPipeline

sourceDataReplayPaysControlArchitecture : Bool
sourceDataReplayPaysControlArchitecture = true

sourceDataReplayPaysPSOObjectiveTopology : Bool
sourceDataReplayPaysPSOObjectiveTopology = true

sourceDataReplayPaysExactControllerNumerics : Bool
sourceDataReplayPaysExactControllerNumerics = false

publishedControlArchitecturePaysSpecificDeployment : Bool
publishedControlArchitecturePaysSpecificDeployment = false
