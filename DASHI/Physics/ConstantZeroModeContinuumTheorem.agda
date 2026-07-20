{-# OPTIONS --safe #-}
module DASHI.Physics.ConstantZeroModeContinuumTheorem where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.DiscreteContinuumKernelTargets

------------------------------------------------------------------------
-- Selected discrete-to-continuum theorem: stationary spatially constant mode.
--
-- This is the exact zero-momentum, zero-Laplacian sector of the first-order wave
-- system.  Every spatial and temporal resolution represents the same unique
-- constant state.  The discrete kernel, embedding, and continuum zero-mode
-- evolution therefore agree definitionally at every resolution.
--
-- The theorem is intentionally narrow.  It does not establish convergence for
-- nonconstant fields, nonzero momentum, dispersion, or a continuum Laplacian.

data ConstantZeroMode : Set where
  constantZeroMode : ConstantZeroMode

zeroModeKernel : ConstantZeroMode → ConstantZeroMode
zeroModeKernel constantZeroMode = constantZeroMode

zeroModeEmbed : ConstantZeroMode → ConstantZeroMode
zeroModeEmbed constantZeroMode = constantZeroMode

zeroModeGenerator : ConstantZeroMode → ConstantZeroMode
zeroModeGenerator constantZeroMode = constantZeroMode

constantZeroModeFamily : DiscretisationFamily
constantZeroModeFamily =
  record
    { DiscreteState = λ _ _ → ConstantZeroMode
    ; ContinuumState = ConstantZeroMode
    ; spatialStep = λ h → h
    ; temporalStep = λ dt → dt
    ; discreteKernel = λ _ _ → zeroModeKernel
    ; embed = zeroModeEmbed
    ; continuumGenerator = zeroModeGenerator
    }

ZeroModeBoundaryConditions : Set
ZeroModeBoundaryConditions = ConstantZeroMode

ZeroModeUnitsMap : Set
ZeroModeUnitsMap = ConstantZeroMode

ZeroModeLocalConsistency : Set
ZeroModeLocalConsistency =
  ∀ {h dt} (x : DiscreteState constantZeroModeFamily h dt) →
  embed constantZeroModeFamily
    (discreteKernel constantZeroModeFamily h dt x)
  ≡
  continuumGenerator constantZeroModeFamily
    (embed constantZeroModeFamily x)

ZeroModeStability : Set
ZeroModeStability =
  ∀ {h dt} (x : DiscreteState constantZeroModeFamily h dt) →
  discreteKernel constantZeroModeFamily h dt x ≡ x

ZeroModeCompleteness : Set
ZeroModeCompleteness = ConstantZeroMode

ZeroModeGeneratorIdentification : Set
ZeroModeGeneratorIdentification =
  continuumGenerator constantZeroModeFamily constantZeroMode ≡ constantZeroMode

ZeroModeConvergence : Set
ZeroModeConvergence =
  ∀ {h dt} (x : DiscreteState constantZeroModeFamily h dt) →
  embed constantZeroModeFamily
    (discreteKernel constantZeroModeFamily h dt x)
  ≡ embed constantZeroModeFamily x

zeroModeLocalConsistency : ZeroModeLocalConsistency
zeroModeLocalConsistency constantZeroMode = refl

zeroModeStability : ZeroModeStability
zeroModeStability constantZeroMode = refl

zeroModeConvergence : ZeroModeConvergence
zeroModeConvergence constantZeroMode = refl

constantZeroModeContinuumTheorem :
  DiscreteContinuumTheorem constantZeroModeFamily
constantZeroModeContinuumTheorem =
  record
    { boundaryConditions = ZeroModeBoundaryConditions
    ; physicalUnitsMap = ZeroModeUnitsMap
    ; localConsistency = ZeroModeLocalConsistency
    ; stabilityEstimate = ZeroModeStability
    ; compactnessOrCompleteness = ZeroModeCompleteness
    ; generatorIdentification = ZeroModeGeneratorIdentification
    ; convergence = ZeroModeConvergence
    }

constantZeroModeTheoremWitnesses :
  ZeroModeBoundaryConditions ×
  ZeroModeUnitsMap ×
  ZeroModeLocalConsistency ×
  ZeroModeStability ×
  ZeroModeCompleteness ×
  ZeroModeGeneratorIdentification ×
  ZeroModeConvergence
constantZeroModeTheoremWitnesses =
  constantZeroMode ,
  constantZeroMode ,
  zeroModeLocalConsistency ,
  zeroModeStability ,
  constantZeroMode ,
  refl ,
  zeroModeConvergence
