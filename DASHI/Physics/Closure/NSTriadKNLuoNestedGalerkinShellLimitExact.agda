module DASHI.Physics.Closure.NSTriadKNLuoNestedGalerkinShellLimitExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Authors: Rupert L. Frank; Fedor Sukochev; Dmitriy Zanin.
-- Title: "Endpoint Schatten Class Properties of Commutators".
-- DOI: 10.1016/j.aim.2024.109738.
--
-- DASHI CONTEXT
--
-- Extends NSTriadKNLuoGalerkinUniformLimitContinuationExact from one cutoff to
-- the actual two-cutoff order required by the critical route.  A finite
-- approximation A(N,Q) is uniformly bounded.  For each Galerkin cutoff N, a
-- selected shell sequence approaches the Galerkin critical quantity.  A
-- selected Galerkin sequence then approaches the physical critical quantity.
--
-- Separate positive shell and Galerkin margins are retained.  Choosing the
-- Galerkin stage first and the shell stage for that selected Galerkin cutoff
-- proves the exact terminal threshold.  No compactness, convergence, lower
-- semicontinuity or nonlinear weak limit is manufactured: all such analytic
-- inputs remain fields of the record.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
import Data.Nat.Properties as NatProperties
open import Data.Rational.Base using (ℚ; _/_; _+_; _≤_; _<_)
import Data.Rational.Properties as RationalProperties

import DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact as Vanish

record NestedGalerkinShellLimitData : Set where
  constructor nestedGalerkinShellLimitData
  field
    finiteApproximation : Nat → Nat → ℚ
    galerkinCritical physicalCritical uniformFiniteBound : ℚ

    galerkinCriticalAt : Nat → ℚ

    uniformFiniteEstimate :
      (galerkinCutoff shellCutoff : Nat) →
      finiteApproximation galerkinCutoff shellCutoff ≤ uniformFiniteBound

    selectedShellCutoff : Nat → Nat → Nat
    shellApproximationError : Nat → Nat → ℚ

    shellErrorTendsToZero :
      (galerkinCutoff : Nat) →
      Vanish.TendsToZero (shellApproximationError galerkinCutoff)

    galerkinBelowSelectedShellPlusError :
      (galerkinCutoff stage : Nat) →
      galerkinCriticalAt galerkinCutoff
      ≤ finiteApproximation
          galerkinCutoff
          (selectedShellCutoff galerkinCutoff stage)
        + shellApproximationError galerkinCutoff stage

    selectedGalerkinCutoff : Nat → Nat
    galerkinApproximationError : Nat → ℚ

    galerkinErrorTendsToZero :
      Vanish.TendsToZero galerkinApproximationError

    physicalBelowSelectedGalerkinPlusError :
      (stage : Nat) →
      physicalCritical
      ≤ galerkinCriticalAt (selectedGalerkinCutoff stage)
        + galerkinApproximationError stage

    shellMargin galerkinMargin continuationThreshold : ℚ

    shellMarginPositive : Int.+ 0 / 1 < shellMargin
    galerkinMarginPositive : Int.+ 0 / 1 < galerkinMargin

    finiteBoundPlusMarginsBelowThreshold :
      uniformFiniteBound + shellMargin + galerkinMargin
      ≤ continuationThreshold

open NestedGalerkinShellLimitData public

nestedGalerkinShellLimitBelowThreshold :
  (dataSet : NestedGalerkinShellLimitData) →
  physicalCritical dataSet ≤ continuationThreshold dataSet
nestedGalerkinShellLimitBelowThreshold dataSet =
  let
    galerkinTail =
      Vanish.eventuallySmall
        (galerkinErrorTendsToZero dataSet)
        (galerkinMargin dataSet)
        (galerkinMarginPositive dataSet)

    galerkinStage = Vanish.cutoff galerkinTail
    chosenGalerkin = selectedGalerkinCutoff dataSet galerkinStage

    galerkinErrorBound :
      galerkinApproximationError dataSet galerkinStage
      ≤ galerkinMargin dataSet
    galerkinErrorBound =
      Vanish.tailBound
        galerkinTail
        galerkinStage
        NatProperties.≤-refl

    shellTail =
      Vanish.eventuallySmall
        (shellErrorTendsToZero dataSet chosenGalerkin)
        (shellMargin dataSet)
        (shellMarginPositive dataSet)

    shellStage = Vanish.cutoff shellTail
    chosenShell =
      selectedShellCutoff dataSet chosenGalerkin shellStage

    shellErrorBound :
      shellApproximationError dataSet chosenGalerkin shellStage
      ≤ shellMargin dataSet
    shellErrorBound =
      Vanish.tailBound
        shellTail
        shellStage
        NatProperties.≤-refl

    finiteBound :
      finiteApproximation dataSet chosenGalerkin chosenShell
      ≤ uniformFiniteBound dataSet
    finiteBound =
      uniformFiniteEstimate dataSet chosenGalerkin chosenShell

    shellApproximationBound :
      galerkinCriticalAt dataSet chosenGalerkin
      ≤ uniformFiniteBound dataSet + shellMargin dataSet
    shellApproximationBound =
      RationalProperties.≤-trans
        (galerkinBelowSelectedShellPlusError
          dataSet chosenGalerkin shellStage)
        (RationalProperties.+-mono-≤ finiteBound shellErrorBound)

    physicalWithMargins :
      physicalCritical dataSet
      ≤
      (uniformFiniteBound dataSet + shellMargin dataSet)
      + galerkinMargin dataSet
    physicalWithMargins =
      RationalProperties.≤-trans
        (physicalBelowSelectedGalerkinPlusError dataSet galerkinStage)
        (RationalProperties.+-mono-≤
          shellApproximationBound
          galerkinErrorBound)
  in
  RationalProperties.≤-trans
    physicalWithMargins
    (finiteBoundPlusMarginsBelowThreshold dataSet)

record NestedLimitAuthorityBoundary : Set where
  constructor nestedLimitAuthorityBoundary
  field
    shellThenGalerkinSelectionProved : Set
    separatePositiveMarginsRetained : Set
    exactThresholdTransportProved : Set
    shellConvergenceProducedAnalytically : Set
    galerkinConvergenceProducedAnalytically : Set
    criticalNormLowerSemicontinuityProved : Set

canonicalNestedLimitAuthorityBoundary : NestedLimitAuthorityBoundary
canonicalNestedLimitAuthorityBoundary =
  nestedLimitAuthorityBoundary ⊤ ⊤ ⊤ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
