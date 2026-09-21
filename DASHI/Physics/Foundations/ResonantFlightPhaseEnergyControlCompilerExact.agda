module DASHI.Physics.Foundations.ResonantFlightPhaseEnergyControlCompilerExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.ResonantFlightNaturalModeControlCompilerExact as Mode
import DASHI.Physics.Foundations.ResonantFlightPhaseEnergyRoutingExact as Energy

------------------------------------------------------------------------
-- Joint compiler: the same phase coordinate indexes both geometry and
-- energy-routing policy.
------------------------------------------------------------------------

record PhaseEnergyControlledMode : Set₁ where
  constructor phase-energy-controlled-mode
  field
    PilotInput Phase State : Set
    geometry : PilotInput → Phase → State
    energyRole : PilotInput → Phase → Energy.PowerRole
    neutral : PilotInput

open PhaseEnergyControlledMode public

record NaturalPhaseEnergyMode : Set₁ where
  constructor natural-phase-energy-mode
  field
    Phase State : Set
    naturalGeometry : Phase → State
    naturalEnergyRole : Phase → Energy.PowerRole

open NaturalPhaseEnergyMode public

record PhaseEnergyModeCompiler
  (N : NaturalPhaseEnergyMode) : Set₁ where
  constructor phase-energy-mode-compiler
  field
    PilotInput : Set
    compileGeometry :
      PilotInput →
      NaturalPhaseEnergyMode.Phase N →
      NaturalPhaseEnergyMode.State N
    compileEnergyRole :
      PilotInput →
      NaturalPhaseEnergyMode.Phase N →
      Energy.PowerRole
    neutral : PilotInput
    neutral-geometry :
      (φ : NaturalPhaseEnergyMode.Phase N) →
      compileGeometry neutral φ ≡
      NaturalPhaseEnergyMode.naturalGeometry N φ
    neutral-energy :
      (φ : NaturalPhaseEnergyMode.Phase N) →
      compileEnergyRole neutral φ ≡
      NaturalPhaseEnergyMode.naturalEnergyRole N φ

open PhaseEnergyModeCompiler public

neutralPreservesEnergyPolicy :
  {N : NaturalPhaseEnergyMode} →
  (C : PhaseEnergyModeCompiler N) →
  (φ : NaturalPhaseEnergyMode.Phase N) →
  compileEnergyRole C (PhaseEnergyModeCompiler.neutral C) φ ≡
  NaturalPhaseEnergyMode.naturalEnergyRole N φ
neutralPreservesEnergyPolicy C =
  PhaseEnergyModeCompiler.neutral-energy C
