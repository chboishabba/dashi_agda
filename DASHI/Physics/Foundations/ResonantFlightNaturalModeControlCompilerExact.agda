module DASHI.Physics.Foundations.ResonantFlightNaturalModeControlCompilerExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.ResonantFlightPhaseControlExact as Phase
import DASHI.Physics.Foundations.ResonantFlightHarmonicCyclicBasisExact as Harm
import DASHI.Physics.Foundations.ResonantFlightTunableResonanceExact as Resonance

------------------------------------------------------------------------
-- Compiler target: neutral control is the natural flight mode; non-neutral
-- control changes harmonic coefficients and/or resonance tuning.
------------------------------------------------------------------------

record NaturalFlightMode : Set₁ where
  constructor natural-flight-mode
  field
    Phase State : Set
    natural : Phase → State

open NaturalFlightMode public

record ModeCoefficientDeformation
  (PilotInput : Set)
  (M : NaturalFlightMode) : Set₁ where
  constructor mode-coefficient-deformation
  field
    controlled : PilotInput → Phase M → State M
    neutral : PilotInput
    neutral-preserves-natural :
      (φ : Phase M) →
      controlled neutral φ ≡ natural M φ

open ModeCoefficientDeformation public

record ModalControlCompiler : Set₁ where
  constructor modal-control-compiler
  field
    PilotInput Phase State : Set
    natural : Phase → State
    compile : PilotInput → Phase → State
    neutral : PilotInput
    neutral-compiler :
      (φ : Phase) →
      compile neutral φ ≡ natural φ

open ModalControlCompiler public

compileNeutralIsNatural :
  (C : ModalControlCompiler) →
  (φ : ModalControlCompiler.Phase C) →
  ModalControlCompiler.compile C (ModalControlCompiler.neutral C) φ ≡
  ModalControlCompiler.natural C φ
compileNeutralIsNatural C =
  ModalControlCompiler.neutral-compiler C

------------------------------------------------------------------------
-- Control decomposition: phase-shape deformation and resonance retuning
-- remain explicit, so future numerical/CFD layers can optimize them
-- separately.
------------------------------------------------------------------------

record ModalControlSurface : Set₁ where
  constructor modal-control-surface
  field
    PilotInput ShapeControl ResonanceControl : Set
    shape : PilotInput → ShapeControl
    resonance : PilotInput → ResonanceControl

open ModalControlSurface public
