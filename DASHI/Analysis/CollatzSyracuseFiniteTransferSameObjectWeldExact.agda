module DASHI.Analysis.CollatzSyracuseFiniteTransferSameObjectWeldExact where

------------------------------------------------------------------------
-- FINITE TRANSFER / INTEGER SYRACUSE SAME-OBJECT WELD
--
-- The finite 3z/(3z-1) chain is not declared equal to the shortcut Syracuse
-- map.  A consumer must supply an explicit supported-observable intertwiner.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

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

record FiniteTransferBoundary : Set where
  constructor finiteTransferBoundary
  field
    fineKernelEqualsFiniteKernel : Nat
    explicitIntertwinerRequired : Nat
    observableLawOrientationMustMatch : Nat
    pathMemoryRetained : Nat

canonicalFiniteTransferBoundary : FiniteTransferBoundary
canonicalFiniteTransferBoundary = finiteTransferBoundary 0 1 1 1
