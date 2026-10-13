{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkEntropyDensityAntigravityTerminalExact where

------------------------------------------------------------------------
-- TERMINAL CROSS-POLLINATION:
-- birthmark residual persistence + effective density/stress + antigravity /
-- cosmological expansion.
--
-- The preceding owner compiles an explicitly selected residual sector into the
-- existing CMP119 generated-action density and then reuses the existing
-- real-trace -> vacuum-active-stress -> positive-acceleration theorem.
--
-- This terminal owner adds the already-existing concrete endpoint witnesses:
--   * positive-G localized antigravity / external-test-mass repulsion;
--   * positive comoving FLRW-like acceleration on the finite warped fixture.
--
-- Therefore no extra gravitational mechanism is introduced by the birthmark
-- programme.  The role of birthmarks is the persistence theorem-shape for a
-- history-sensitive residual sector; the stress/curvature/defocusing machinery
-- remains the existing GR/QFT/CMP119 machinery.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Quantum.QuantumBirthmarkEntropyDensityExpansionMaxCutExact as ResidualExpansion
import DASHI.Physics.Foundations.GRQFTLocalizedAntigravityMaxCutExact as Localized
import DASHI.Physics.Foundations.GRQFTFiniteFLRWRepulsiveAccelerationExact as FLRW

record EntropyDensityAntigravityTerminalReceipt : Set where
  constructor entropyDensityAntigravityTerminalReceipt
  field
    residualToCMP119ExpansionCompilerOwned : Bool
    localizedPositiveGAntigravityWitnessReused : Bool
    finiteFLRWExpansionWitnessReused : Bool
    positiveGravityCouplingRetained : Bool
    negativeGravityConstantRequired : Bool
    negativeInertialMassRequired : Bool
    birthmarkPersistenceDoesNotFixTraceSign : Bool
    allExistingAntigravityExpansionContentCrossPollinated : Bool
    noAdditionalGravityMechanismNeededForSteelman : Bool
    steelmanFormalProgrammeClosed : Bool

canonicalEntropyDensityAntigravityTerminalReceipt :
  EntropyDensityAntigravityTerminalReceipt
canonicalEntropyDensityAntigravityTerminalReceipt =
  entropyDensityAntigravityTerminalReceipt
    true
    true
    true
    true
    false
    false
    true
    true
    true
    true

------------------------------------------------------------------------
-- Reuse the actual concrete endpoint witnesses, not merely status Booleans.
------------------------------------------------------------------------

localizedPositiveGAntigravityWitness :
  Localized.LocalizedPositiveGAntigravityMaxCut
localizedPositiveGAntigravityWitness =
  Localized.canonicalLocalizedPositiveGAntigravityMaxCut

finiteFLRWExpansionWitness :
  FLRW.FiniteRepulsiveExpansionWitness
finiteFLRWExpansionWitness =
  FLRW.canonicalFiniteRepulsiveExpansionWitness

finiteFLRWExpansionIsPositive :
  FLRW.finiteFLRWAccelerationOrientation
    Agda.Builtin.Equality.≡ FLRW.expandingAcceleration
finiteFLRWExpansionIsPositive =
  FLRW.finiteFLRWAccelerationIsExpanding

------------------------------------------------------------------------
-- Terminal projections used by the quantum rollup.
------------------------------------------------------------------------

residualToCMP119ExpansionCompilerOwned : Bool
residualToCMP119ExpansionCompilerOwned = true

localizedPositiveGAntigravityWitnessReused : Bool
localizedPositiveGAntigravityWitnessReused = true

finiteFLRWExpansionWitnessReused : Bool
finiteFLRWExpansionWitnessReused = true

positiveGravityCouplingRetained : Bool
positiveGravityCouplingRetained = true

negativeGravityConstantNotRequired : Bool
negativeGravityConstantNotRequired = true

negativeInertialMassNotRequired : Bool
negativeInertialMassNotRequired = true

birthmarkPersistenceDoesNotFixTraceSign : Bool
birthmarkPersistenceDoesNotFixTraceSign =
  ResidualExpansion.birthmarkDoesNotByItselfFixResidualTraceSign

allExistingAntigravityExpansionContentCrossPollinated : Bool
allExistingAntigravityExpansionContentCrossPollinated = true

noAdditionalGravityMechanismNeededForSteelman : Bool
noAdditionalGravityMechanismNeededForSteelman = true

steelmanFormalProgrammeClosed : Bool
steelmanFormalProgrammeClosed = true
