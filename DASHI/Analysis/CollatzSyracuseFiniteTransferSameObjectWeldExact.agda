module DASHI.Analysis.CollatzSyracuseFiniteTransferSameObjectWeldExact where

------------------------------------------------------------------------
-- FINITE TRANSFER / INTEGER SYRACUSE SAME-OBJECT AUDIT
--
-- Literal Syracuse inverse branches at modulus 2^m are
--
--   y ↦ 2y
--   y ↦ 3⁻¹(2y - 1),
--
-- while the pinned spectral source CollatzRelMatrix uses, for every state,
--
--   z ↦ 3z
--   z ↦ 3z - 1.
--
-- These are different finite dynamics.  Shared binary branching, common
-- modulus, or downstream spectral consumers do not create an intertwiner.
-- A separate supported-observable theorem could still be supplied in future,
-- but none is promoted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder

record SyracuseFiniteTransferWeld : Set₁ where
  field
    cylinderSource : Cylinder.ParityCylinderSource

    FiniteState : Set
    FiniteObservable : Set
    FineObservable : Set

    observeFiniteState : Syracuse.PositiveNat → FiniteState
    fineStep : Syracuse.PositiveNat → Syracuse.PositiveNat
    finiteLawStep : FiniteState → FiniteState

    fineStepIsLiteralSyracuse :
      (x : Syracuse.PositiveNat) →
      fineStep x ≡ Syracuse.shortcutSyracuse x

    supportedFine : FineObservable → Set
    supportedFinite : FiniteObservable → Set
    realizeObservable : FineObservable → FiniteObservable

    oneStepIntertwining :
      (f : FineObservable) →
      supportedFine f →
      supportedFinite (realizeObservable f) → Set

    iteratedIntertwining :
      (steps : Nat) →
      (f : FineObservable) →
      supportedFine f → Set

    finiteSourceAttribution : String

open SyracuseFiniteTransferWeld public

------------------------------------------------------------------------
-- Wrong-type firewall for the particular spectral relation already audited.
------------------------------------------------------------------------

data SpectralGeneratorsEqualSyracuseInverseBranches : Set where
data SharedBinaryBranchingCreatesIntertwiner : Set where

spectralGeneratorsDoNotEqualSyracuseInverseBranches :
  SpectralGeneratorsEqualSyracuseInverseBranches → ⊥
spectralGeneratorsDoNotEqualSyracuseInverseBranches ()

sharedBinaryBranchingDoesNotCreateIntertwiner :
  SharedBinaryBranchingCreatesIntertwiner → ⊥
sharedBinaryBranchingDoesNotCreateIntertwiner ()

record FiniteTransferBoundary : Set where
  constructor finiteTransferBoundary
  field
    fineKernelEqualsFiniteKernel : Bool
    explicitIntertwinerRequired : Bool
    observableLawOrientationMustMatch : Bool
    pathMemoryRetained : Bool
    literalSyracuseInverseBranchesAreTwoAndOddInv3 : Bool
    spectralSourceUsesThreeZAndThreeZMinusOne : Bool
    currentSpectralRelationSameObjectWeldPaid : Bool
    currentSpectralRelationCriticalForSyracuseConcentration : Bool
    sourceNote : String

open FiniteTransferBoundary public

canonicalFiniteTransferBoundary : FiniteTransferBoundary
canonicalFiniteTransferBoundary =
  finiteTransferBoundary
    false true true true
    true true
    false false
    "Pinned CollatzRelMatrix defines y=3x or y=3x-1 for every finite state. Literal shortcut-Syracuse reverse cylinders are x=2y or x=3^-1(2y-1). The existing spectral relation therefore remains a separate finite object unless a new explicit observable intertwiner is proved."

spectralWeldNotPaid :
  currentSpectralRelationSameObjectWeldPaid canonicalFiniteTransferBoundary
  ≡ false
spectralWeldNotPaid = refl

spectralRouteNotCritical :
  currentSpectralRelationCriticalForSyracuseConcentration canonicalFiniteTransferBoundary
  ≡ false
spectralRouteNotCritical = refl
