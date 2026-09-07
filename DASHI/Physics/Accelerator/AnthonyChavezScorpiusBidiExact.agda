module DASHI.Physics.Accelerator.AnthonyChavezScorpiusBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.FiniteObservationClosureBidiExact as Closure

-- LEGACY FILENAME / ATTRIBUTION CORRECTION.
--
-- The relevant LANL technical publications and Scorpius/DARHT engineering
-- record identify MARK ANTHONY CHAVEZ. This module name predates the identity
-- audit and MUST NOT be used to attribute this technical work to the separate
-- missing 78-year-old Anthony Chavez without an independent same-person receipt.
-- Programme-level machine physics comes from LANL/LLNL public Scorpius
-- descriptions; no sole-inventor claim is made.

data ScorpiusStage : Set where pulsedPower electronBeam xRayProduction radiographicFrame materialStateInference : ScorpiusStage

record ScorpiusArchitecture : Set where
  constructor scorpius-architecture
  field
    linearInductionAccelerator : Set
    multipleTimedPulses : Set
    multipleXRadiographs : Set
    modularPulsedPowerUnits : Set
    sourceReference : String

open ScorpiusArchitecture public

record ScorpiusBoundary : Set where
  constructor scorpius-boundary
  field
    xRayImageIsDirectMaterialEquationOfState : Bool
    xRayImageIsDirectMaterialEquationOfStateIsFalse : xRayImageIsDirectMaterialEquationOfState ≡ false
    pulseTimingAloneDeterminesImageQuality : Bool
    pulseTimingAloneDeterminesImageQualityIsFalse : pulseTimingAloneDeterminesImageQuality ≡ false
    engineerDesignContributionImpliesSoleAcceleratorAuthorship : Bool
    engineerDesignContributionImpliesSoleAcceleratorAuthorshipIsFalse : engineerDesignContributionImpliesSoleAcceleratorAuthorship ≡ false
    multipleFramesSupportTimeResolvedMaterialInference : Bool
    multipleFramesSupportTimeResolvedMaterialInferenceIsTrue : multipleFramesSupportTimeResolvedMaterialInference ≡ true

canonicalScorpiusBoundary : ScorpiusBoundary
canonicalScorpiusBoundary = scorpius-boundary false refl false refl false refl true refl

scorpiusReverse : Closure.ReverseClosureObligation
scorpiusReverse = Closure.reverse-closure-obligation
  "Scorpius multi-pulse flash-radiography"
  "time-indexed X-ray transmission images"
  "beam/source calibration plus radiographic forward model"
  "time-resolved material-state inference"
  "unique constitutive physics from images alone"
