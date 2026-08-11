module DASHI.Physics.Closure.NSTriadKNPhysicalTimeDependentShellBalanceRound30Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Bind the Round-29 static five-source authority to one time-dependent
-- physical trajectory.  At each time the chain-rule derivative, viscosity and
-- two boundary terms are added to the same global bilinear pairing.  The five
-- source signs and multiplicities are inherited from the exhaustive global
-- pairing and cannot be resupplied by the dynamic theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_)

import DASHI.Physics.Closure.NSTriadKNGlobalBilinearShellPairingRound29Exact as Shell

record PhysicalTimeDependentShellBalance
    {timeLevel : Level}
    (Time : Set timeLevel) : Set (lsuc timeLevel) where
  field
    balanceAt : Time → Shell.DynamicPhysicalShellBalance

    Trajectory : Set timeLevel
    trajectory : Trajectory

    balanceComesFromTrajectory :
      Time → Shell.DynamicPhysicalShellBalance → Set timeLevel
    sameTrajectoryBalance : ∀ time →
      balanceComesFromTrajectory time (balanceAt time)

open PhysicalTimeDependentShellBalance public

physicalFiveSourceShellBalanceAt :
  ∀ {timeLevel}
    {Time : Set timeLevel}
    (dataSet : PhysicalTimeDependentShellBalance Time)
    time →
  Shell.energyDerivative (balanceAt dataSet time)
    + Shell.diffusion (balanceAt dataSet time)
  ≡
    Shell.hhValue (Shell.staticPairing (balanceAt dataSet time))
    + Shell.lhValue (Shell.staticPairing (balanceAt dataSet time))
    + Shell.hlValue (Shell.staticPairing (balanceAt dataSet time))
    + Shell.ccValue (Shell.staticPairing (balanceAt dataSet time))
    + Shell.comValue (Shell.staticPairing (balanceAt dataSet time))
    + Shell.lowerBoundary (balanceAt dataSet time)
    + Shell.upperBoundary (balanceAt dataSet time)
physicalFiveSourceShellBalanceAt dataSet time =
  Shell.physicalShellBalanceExpandsOnce (balanceAt dataSet time)

record LiteralTrajectoryShellAuthority
    {timeLevel}
    {Time : Set timeLevel}
    (dataSet : PhysicalTimeDependentShellBalance Time) : Set (lsuc timeLevel) where
  field
    energyDerivativeIsChainRule : Time → Set timeLevel
    diffusionIsLiteralViscosity : Time → Set timeLevel
    lowerBoundaryIsLiteralFlux : Time → Set timeLevel
    upperBoundaryIsLiteralFlux : Time → Set timeLevel

open LiteralTrajectoryShellAuthority public

physicalTimeDependentShellReducerClosed : Bool
physicalTimeDependentShellReducerClosed = true

literalTrajectoryShellAuthoritySupplied : Bool
literalTrajectoryShellAuthoritySupplied = false

physicalTimeDependentShellReducerClosedIsTrue :
  physicalTimeDependentShellReducerClosed ≡ true
physicalTimeDependentShellReducerClosedIsTrue = refl

literalTrajectoryShellAuthoritySuppliedIsFalse :
  literalTrajectoryShellAuthoritySupplied ≡ false
literalTrajectoryShellAuthoritySuppliedIsFalse = refl
