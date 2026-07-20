module DASHI.Core.FiniteQuadraticMultiscale where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

open import DASHI.Unified.GRQuantumProofTerms

------------------------------------------------------------------------
-- A small exact proof pattern for multiscale energy uniqueness.

data FiniteMultiscaleState : Set where
  zeroState : FiniteMultiscaleState
  coarseUnit : FiniteMultiscaleState
  detailUnit : FiniteMultiscaleState
  combinedUnit : FiniteMultiscaleState

record EnergyTable : Set where
  constructor energy-table
  field
    zeroEnergy : Nat
    coarseEnergy : Nat
    detailEnergy : Nat
    combinedEnergy : Nat
open EnergyTable public

canonicalQuadraticEnergy : EnergyTable
canonicalQuadraticEnergy = energy-table 0 1 1 2

record SatisfiesFiniteMultiscaleLaws (energy : EnergyTable) : Set where
  constructor finite-multiscale-laws
  field
    zeroNormalisation : zeroEnergy energy ≡ 0
    coarseUnitNormalisation : coarseEnergy energy ≡ 1
    detailUnitNormalisation : detailEnergy energy ≡ 1
    orthogonalNoLeakage :
      combinedEnergy energy ≡ coarseEnergy energy + detailEnergy energy
open SatisfiesFiniteMultiscaleLaws public

canonicalEnergySatisfiesLaws :
  SatisfiesFiniteMultiscaleLaws canonicalQuadraticEnergy
canonicalEnergySatisfiesLaws =
  finite-multiscale-laws refl refl refl refl

finiteQuadraticEnergyUnique :
  (energy : EnergyTable) →
  SatisfiesFiniteMultiscaleLaws energy →
  energy ≡ canonicalQuadraticEnergy
finiteQuadraticEnergyUnique
  (energy-table zeroValue coarseValue detailValue combinedValue)
  (finite-multiscale-laws zero-is-zero coarse-is-one detail-is-one no-leakage)
  rewrite zero-is-zero
        | coarse-is-one
        | detail-is-one
        | no-leakage = refl

finiteQuadraticUniquenessProof : QuadraticUniquenessProof
finiteQuadraticUniquenessProof =
  record
    { EnergyFunctional = EnergyTable
    ; SatisfiesMultiscaleLaws = SatisfiesFiniteMultiscaleLaws
    ; canonicalQuadraticDefect = canonicalQuadraticEnergy
    ; canonicalSatisfiesLaws = canonicalEnergySatisfiesLaws
    ; uniqueness = finiteQuadraticEnergyUnique
    }

------------------------------------------------------------------------
-- Explicit split and Pythagorean receipt.

coarsePart : FiniteMultiscaleState → FiniteMultiscaleState
coarsePart zeroState = zeroState
coarsePart coarseUnit = coarseUnit
coarsePart detailUnit = zeroState
coarsePart combinedUnit = coarseUnit

detailPart : FiniteMultiscaleState → FiniteMultiscaleState
detailPart zeroState = zeroState
detailPart coarseUnit = zeroState
detailPart detailUnit = detailUnit
detailPart combinedUnit = detailUnit

energyOf : EnergyTable → FiniteMultiscaleState → Nat
energyOf energy zeroState = zeroEnergy energy
energyOf energy coarseUnit = coarseEnergy energy
energyOf energy detailUnit = detailEnergy energy
energyOf energy combinedUnit = combinedEnergy energy

combinedPythagorean :
  energyOf canonicalQuadraticEnergy combinedUnit
  ≡ energyOf canonicalQuadraticEnergy (coarsePart combinedUnit)
    + energyOf canonicalQuadraticEnergy (detailPart combinedUnit)
combinedPythagorean = refl

quadraticFiniteScope : String
quadraticFiniteScope =
  "Exact uniqueness on the four-state orthogonal carrier.  Extension to arbitrary linear/Hilbert carriers requires the repository's general parallelogram-law or Jordan-von Neumann authority."
