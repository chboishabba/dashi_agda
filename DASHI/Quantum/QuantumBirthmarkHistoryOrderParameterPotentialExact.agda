{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHistoryOrderParameterPotentialExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _*_; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Quantum.QuantumBirthmarkHistoryHorizonScalingExact as Horizon
import DASHI.Physics.Foundations.GRQFTNambuGotoTwoVacuumPotentialExact as Potential

------------------------------------------------------------------------
-- HISTORY ORDER PARAMETER -> SCALED TWO-VACUUM POTENTIAL
--
-- This is an explicit phenomenological realization of the history-sector idea.
-- A dimensionless history order parameter phi uses the already-constructed
-- two-vacuum potential.  The whole potential is then multiplied by a selected
-- horizon/history scale s(H) = alpha H^2.
--
-- The result is exact:
--   V_H(0) = alpha H^2 * 21/64
--   V_H(1) = alpha H^2 * 19/48
-- and both vacuum levels therefore track H^2 together.
--
-- This does not derive phi or alpha from microscopic birthmark statistics.
------------------------------------------------------------------------

historyPotentialScale : ℚ → ℚ → ℚ
historyPotentialScale alpha hubble = Horizon.historyDensity alpha hubble

historyVacuumPotential : ℚ → ℚ → ℚ → ℚ
historyVacuumPotential alpha hubble phi =
  Potential.scaledNambuPotential (historyPotentialScale alpha hubble) phi

historyInteriorVacuum :
  (alpha hubble : ℚ) →
  historyVacuumPotential alpha hubble Potential.interiorField
    ≡ historyPotentialScale alpha hubble * (Int.+ 21 / 64)
historyInteriorVacuum alpha hubble =
  Potential.scaledInteriorEnergy (historyPotentialScale alpha hubble)

historyExteriorVacuum :
  (alpha hubble : ℚ) →
  historyVacuumPotential alpha hubble Potential.exteriorField
    ≡ historyPotentialScale alpha hubble * (Int.+ 19 / 48)
historyExteriorVacuum alpha hubble =
  Potential.scaledExteriorEnergy (historyPotentialScale alpha hubble)

------------------------------------------------------------------------
-- The vacuum ratio is scale independent in cross-multiplied form.
------------------------------------------------------------------------

historyVacuumRatioInvariant :
  (alpha hubble : ℚ) →
  (Int.+ 19 / 48)
    * historyVacuumPotential alpha hubble Potential.interiorField
  ≡
  (Int.+ 21 / 64)
    * historyVacuumPotential alpha hubble Potential.exteriorField
historyVacuumRatioInvariant alpha hubble = solve (alpha ∷ hubble ∷ [])

------------------------------------------------------------------------
-- Exact three-state finite wall carrier.
--
-- The existing potential owns stationary interior/exterior vacua and one
-- unstable barrier.  We expose those as a minimal finite-thickness candidate
-- carrier.  This is not yet a continuum Euler-Lagrange kink solution.
------------------------------------------------------------------------

data HistoryWallSite : Set where
  interiorSite : HistoryWallSite
  barrierSite : HistoryWallSite
  exteriorSite : HistoryWallSite

historyFieldAt : HistoryWallSite → ℚ
historyFieldAt interiorSite = Potential.interiorField
historyFieldAt barrierSite = Potential.barrierField
historyFieldAt exteriorSite = Potential.exteriorField

historyWallPotentialAt :
  ℚ → ℚ → HistoryWallSite → ℚ
historyWallPotentialAt alpha hubble site =
  historyVacuumPotential alpha hubble (historyFieldAt site)

record HistoryOrderParameterPotentialBoundary : Set where
  constructor history-order-parameter-potential-boundary
  field
    twoStableVacuaReused : Bool
    separatingBarrierReused : Bool
    wholePotentialHubbleSquaredScaled : Bool
    vacuumRatioScaleInvariant : Bool
    finiteThreeSiteWallCarrierConstructed : Bool
    microscopicBirthmarkOrderParameterDerived : Bool
    cmp119PotentialCouplingDerived : Bool
    continuumFiniteThicknessKinkDerived : Bool

canonicalHistoryOrderParameterPotentialBoundary :
  HistoryOrderParameterPotentialBoundary
canonicalHistoryOrderParameterPotentialBoundary =
  history-order-parameter-potential-boundary
    true true true true true false false false

historyPotentialModelOwned : Bool
historyPotentialModelOwned = true

finiteWallCarrierOwned : Bool
finiteWallCarrierOwned = true

microscopicOrderParameterStillRequired : Bool
microscopicOrderParameterStillRequired = true

continuumWallDynamicsStillRequired : Bool
continuumWallDynamicsStillRequired = true
