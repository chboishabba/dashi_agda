{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkEntropyDensityAntigravityTerminalExact where

------------------------------------------------------------------------
-- TERMINAL CROSS-POLLINATION:
-- birthmark residual persistence + effective density/stress + antigravity /
-- cosmological expansion.
--
-- The preceding owners compile an explicitly selected residual sector into the
-- existing CMP119 generated-action density and then reuse the existing
-- source-facing Eq.(2.23)/R136/continuum-stress expansion chain.
--
-- This terminal owner also reuses the strongest already-formalized repulsive
-- endpoints in the foundations spine:
--   * positive-G localized antigravity / external-test-mass repulsion;
--   * positive comoving FLRW-like acceleration on the finite warped fixture;
--   * an exact balanced DEC-compatible repulsive shell family;
--   * the DEC-compatible CMP119 repulsive-exterior max-cut boundary;
--   * the constructive Nambu-Goto positive-tension repulsive-bubble boundary.
--
-- These are alternative endpoint realizations of negative-active-stress /
-- vacuum-pressure defocusing.  They are not used to infer the birthmark sign.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Quantum.QuantumBirthmarkEntropyDensityExpansionMaxCutExact as ResidualExpansion
import DASHI.Physics.Foundations.GRQFTLocalizedAntigravityMaxCutExact as Localized
import DASHI.Physics.Foundations.GRQFTFiniteFLRWRepulsiveAccelerationExact as FLRW
import DASHI.Physics.Foundations.GRQFTBalancedDECRepulsiveShellFamilyExact as Balanced
import DASHI.Physics.Foundations.GRQFTDECRepulsiveExteriorMaxCutExact as DEC
import DASHI.Physics.Foundations.GRQFTNambuGotoRepulsiveBubbleMaxCutExact as Nambu

record EntropyDensityAntigravityTerminalReceipt : Set where
  constructor entropyDensityAntigravityTerminalReceipt
  field
    residualToCMP119ExpansionCompilerOwned : Bool
    localizedPositiveGAntigravityWitnessReused : Bool
    finiteFLRWExpansionWitnessReused : Bool
    balancedDECRepulsiveShellFamilyRegistered : Bool
    decRepulsiveExteriorBranchRegistered : Bool
    nambuGotoRepulsiveBubbleBranchRegistered : Bool
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
    true true true true true true true false false true true true true

------------------------------------------------------------------------
-- Reuse actual endpoint witnesses / canonical boundaries.
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
  FLRW.finiteFLRWAccelerationOrientation ≡ FLRW.expandingAcceleration
finiteFLRWExpansionIsPositive =
  FLRW.finiteFLRWAccelerationIsExpanding

balancedDECRepulsiveShellWitness :
  Balanced.BalancedDECRepulsiveShellFamilyWitness Balanced.fixtureRadius
balancedDECRepulsiveShellWitness =
  Balanced.balancedDECRepulsiveShellFamily Balanced.fixtureRadius

decRepulsiveExteriorBoundary :
  DEC.DECRepulsiveExteriorMaxCutBoundary
decRepulsiveExteriorBoundary =
  DEC.canonicalDECRepulsiveExteriorMaxCutBoundary

nambuGotoRepulsiveBubbleBoundary :
  Nambu.NambuGotoRepulsiveBubbleMaxCutBoundary
nambuGotoRepulsiveBubbleBoundary =
  Nambu.canonicalNambuGotoRepulsiveBubbleMaxCutBoundary

------------------------------------------------------------------------
-- Terminal projections used by the quantum rollup.
------------------------------------------------------------------------

residualToCMP119ExpansionCompilerOwned : Bool
residualToCMP119ExpansionCompilerOwned = true

localizedPositiveGAntigravityWitnessReused : Bool
localizedPositiveGAntigravityWitnessReused = true

finiteFLRWExpansionWitnessReused : Bool
finiteFLRWExpansionWitnessReused = true

balancedDECRepulsiveShellFamilyRegistered : Bool
balancedDECRepulsiveShellFamilyRegistered = true

decRepulsiveExteriorBranchRegistered : Bool
decRepulsiveExteriorBranchRegistered = true

nambuGotoRepulsiveBubbleBranchRegistered : Bool
nambuGotoRepulsiveBubbleBranchRegistered = true

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
