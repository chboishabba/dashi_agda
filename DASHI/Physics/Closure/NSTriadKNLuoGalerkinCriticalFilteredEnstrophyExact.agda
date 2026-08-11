module DASHI.Physics.Closure.NSTriadKNLuoGalerkinCriticalFilteredEnstrophyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
-- Status: arXiv preprint, submitted 25 June 2026.
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
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- This module implements the exact finite Galerkin/quadrature pairing behind
-- F2.  Every scalar vorticity coordinate satisfies the literal filtered
-- equation
--
--   omega_t - nu Delta omega = HH + LH + HL + CC + Com.
--
-- Multiplication by 2 omega gives the exact enstrophy identity with the
-- dissipative sign retained:
--
--   2 omega omega_t - 2 nu omega Delta omega
--     = 2 omega (HH + LH + HL + CC + Com).
--
-- Recursive summation proves the finite coordinate identity.  A shell record
-- then supplies the independently checked periodic integration-by-parts
-- equality identifying the negative Laplacian pairing with a nonnegative
-- gradient norm, and the whole identity is multiplied by a literal critical
-- weight.
--
-- This is not an arbitrary endpoint ledger: the five sources occur inside the
-- differential equation before pairing.  The remaining open interface is the
-- actual Fourier/Galerkin construction of those coordinates and Bony index
-- ranges from the periodic Navier-Stokes solution.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; sym; trans)

record GalerkinVorticityCoordinate (viscosity : ℚ) : Set where
  constructor galerkinVorticityCoordinate
  field
    vorticity timeDerivative laplacian : ℚ
    highHigh lowHigh highLow comparable commutator : ℚ

    filteredVorticityEquation :
      timeDerivative - viscosity * laplacian
      ≡ highHigh + lowHigh + highLow + comparable + commutator

open GalerkinVorticityCoordinate public

coordinateEnstrophyRate :
  ∀ {viscosity} → GalerkinVorticityCoordinate viscosity → ℚ
coordinateEnstrophyRate coordinate =
  2 * vorticity coordinate * timeDerivative coordinate

coordinateViscousPairing :
  ∀ {viscosity} → GalerkinVorticityCoordinate viscosity → ℚ
coordinateViscousPairing {viscosity} coordinate =
  - (2 * viscosity * vorticity coordinate * laplacian coordinate)

coordinateSourcePairing :
  ∀ {viscosity} →
  (GalerkinVorticityCoordinate viscosity → ℚ) →
  GalerkinVorticityCoordinate viscosity → ℚ
coordinateSourcePairing select coordinate =
  2 * vorticity coordinate * select coordinate

coordinateHighHigh :
  ∀ {viscosity} → GalerkinVorticityCoordinate viscosity → ℚ
coordinateHighHigh coordinate = coordinateSourcePairing highHigh coordinate

coordinateLowHigh :
  ∀ {viscosity} → GalerkinVorticityCoordinate viscosity → ℚ
coordinateLowHigh coordinate = coordinateSourcePairing lowHigh coordinate

coordinateHighLow :
  ∀ {viscosity} → GalerkinVorticityCoordinate viscosity → ℚ
coordinateHighLow coordinate = coordinateSourcePairing highLow coordinate

coordinateComparable :
  ∀ {viscosity} → GalerkinVorticityCoordinate viscosity → ℚ
coordinateComparable coordinate = coordinateSourcePairing comparable coordinate

coordinateCommutator :
  ∀ {viscosity} → GalerkinVorticityCoordinate viscosity → ℚ
coordinateCommutator coordinate = coordinateSourcePairing commutator coordinate

coordinateFilteredEnstrophyIdentity :
  ∀ {viscosity}
    (coordinate : GalerkinVorticityCoordinate viscosity) →
  coordinateEnstrophyRate coordinate
    + coordinateViscousPairing coordinate
  ≡
  coordinateHighHigh coordinate
    + coordinateLowHigh coordinate
    + coordinateHighLow coordinate
    + coordinateComparable coordinate
    + coordinateCommutator coordinate
coordinateFilteredEnstrophyIdentity {viscosity} coordinate =
  let
    leftFactorization :
      coordinateEnstrophyRate coordinate
        + coordinateViscousPairing coordinate
      ≡
      2 * vorticity coordinate
        * (timeDerivative coordinate - viscosity * laplacian coordinate)
    leftFactorization =
      solve
        ( vorticity coordinate
        ∷ timeDerivative coordinate
        ∷ viscosity
        ∷ laplacian coordinate
        ∷ [])

    equationPaired =
      cong
        (λ value → 2 * vorticity coordinate * value)
        (filteredVorticityEquation coordinate)

    rightExpansion :
      2 * vorticity coordinate
        * (highHigh coordinate + lowHigh coordinate
          + highLow coordinate + comparable coordinate
          + commutator coordinate)
      ≡
      coordinateHighHigh coordinate
        + coordinateLowHigh coordinate
        + coordinateHighLow coordinate
        + coordinateComparable coordinate
        + coordinateCommutator coordinate
    rightExpansion =
      solve
        ( vorticity coordinate
        ∷ highHigh coordinate
        ∷ lowHigh coordinate
        ∷ highLow coordinate
        ∷ comparable coordinate
        ∷ commutator coordinate
        ∷ [])
  in
  trans leftFactorization (trans equationPaired rightExpansion)

sumCoordinate :
  ∀ {viscosity} →
  (GalerkinVorticityCoordinate viscosity → ℚ) →
  List (GalerkinVorticityCoordinate viscosity) → ℚ
sumCoordinate select [] = 0ℚ
sumCoordinate select (coordinate ∷ coordinates) =
  select coordinate + sumCoordinate select coordinates

sumEnstrophyRate :
  ∀ {viscosity} → List (GalerkinVorticityCoordinate viscosity) → ℚ
sumEnstrophyRate = sumCoordinate coordinateEnstrophyRate

sumViscousPairing :
  ∀ {viscosity} → List (GalerkinVorticityCoordinate viscosity) → ℚ
sumViscousPairing = sumCoordinate coordinateViscousPairing

sumHighHigh :
  ∀ {viscosity} → List (GalerkinVorticityCoordinate viscosity) → ℚ
sumHighHigh = sumCoordinate coordinateHighHigh

sumLowHigh :
  ∀ {viscosity} → List (GalerkinVorticityCoordinate viscosity) → ℚ
sumLowHigh = sumCoordinate coordinateLowHigh

sumHighLow :
  ∀ {viscosity} → List (GalerkinVorticityCoordinate viscosity) → ℚ
sumHighLow = sumCoordinate coordinateHighLow

sumComparable :
  ∀ {viscosity} → List (GalerkinVorticityCoordinate viscosity) → ℚ
sumComparable = sumCoordinate coordinateComparable

sumCommutator :
  ∀ {viscosity} → List (GalerkinVorticityCoordinate viscosity) → ℚ
sumCommutator = sumCoordinate coordinateCommutator

finiteGalerkinFilteredEnstrophyIdentity :
  ∀ {viscosity}
    (coordinates : List (GalerkinVorticityCoordinate viscosity)) →
  sumEnstrophyRate coordinates + sumViscousPairing coordinates
  ≡
  sumHighHigh coordinates
    + sumLowHigh coordinates
    + sumHighLow coordinates
    + sumComparable coordinates
    + sumCommutator coordinates
finiteGalerkinFilteredEnstrophyIdentity [] = solve []
finiteGalerkinFilteredEnstrophyIdentity (coordinate ∷ coordinates)
  rewrite coordinateFilteredEnstrophyIdentity coordinate
        | finiteGalerkinFilteredEnstrophyIdentity coordinates =
  solve
    ( coordinateHighHigh coordinate
    ∷ coordinateLowHigh coordinate
    ∷ coordinateHighLow coordinate
    ∷ coordinateComparable coordinate
    ∷ coordinateCommutator coordinate
    ∷ sumHighHigh coordinates
    ∷ sumLowHigh coordinates
    ∷ sumHighLow coordinates
    ∷ sumComparable coordinates
    ∷ sumCommutator coordinates
    ∷ [])

record GalerkinFilteredShell : Set where
  constructor galerkinFilteredShell
  field
    viscosity criticalWeight gradientNormSquared : ℚ
    coordinates : List (GalerkinVorticityCoordinate viscosity)

    periodicIntegrationByParts :
      sumViscousPairing coordinates
      ≡ 2 * viscosity * gradientNormSquared

open GalerkinFilteredShell public

weightedShellRate : GalerkinFilteredShell → ℚ
weightedShellRate shell =
  criticalWeight shell * sumEnstrophyRate (coordinates shell)

weightedShellDiffusion : GalerkinFilteredShell → ℚ
weightedShellDiffusion shell =
  criticalWeight shell
  * (2 * viscosity shell * gradientNormSquared shell)

weightedShellSource :
  (∀ {viscosity} → GalerkinVorticityCoordinate viscosity → ℚ) →
  GalerkinFilteredShell → ℚ
weightedShellSource select shell =
  criticalWeight shell * sumCoordinate select (coordinates shell)

weightedGalerkinFilteredEnstrophyIdentity :
  ∀ shell →
  weightedShellRate shell + weightedShellDiffusion shell
  ≡
  weightedShellSource coordinateHighHigh shell
    + weightedShellSource coordinateLowHigh shell
    + weightedShellSource coordinateHighLow shell
    + weightedShellSource coordinateComparable shell
    + weightedShellSource coordinateCommutator shell
weightedGalerkinFilteredEnstrophyIdentity shell =
  let
    rate = sumEnstrophyRate (coordinates shell)
    viscous = sumViscousPairing (coordinates shell)
    gradient = 2 * viscosity shell * gradientNormSquared shell
    weight = criticalWeight shell

    leftFactorization :
      weightedShellRate shell + weightedShellDiffusion shell
      ≡ weight * (rate + gradient)
    leftFactorization = solve (weight ∷ rate ∷ gradient ∷ [])

    integrationByPartsSubstitution :
      weight * (rate + gradient)
      ≡ weight * (rate + viscous)
    integrationByPartsSubstitution =
      cong
        (λ value → weight * (rate + value))
        (sym (periodicIntegrationByParts shell))

    equationSubstitution :
      weight * (rate + viscous)
      ≡
      weight
        * (sumHighHigh (coordinates shell)
          + sumLowHigh (coordinates shell)
          + sumHighLow (coordinates shell)
          + sumComparable (coordinates shell)
          + sumCommutator (coordinates shell))
    equationSubstitution =
      cong
        (λ value → weight * value)
        (finiteGalerkinFilteredEnstrophyIdentity (coordinates shell))

    rightExpansion :
      weight
        * (sumHighHigh (coordinates shell)
          + sumLowHigh (coordinates shell)
          + sumHighLow (coordinates shell)
          + sumComparable (coordinates shell)
          + sumCommutator (coordinates shell))
      ≡
      weightedShellSource coordinateHighHigh shell
        + weightedShellSource coordinateLowHigh shell
        + weightedShellSource coordinateHighLow shell
        + weightedShellSource coordinateComparable shell
        + weightedShellSource coordinateCommutator shell
    rightExpansion =
      solve
        ( weight
        ∷ sumHighHigh (coordinates shell)
        ∷ sumLowHigh (coordinates shell)
        ∷ sumHighLow (coordinates shell)
        ∷ sumComparable (coordinates shell)
        ∷ sumCommutator (coordinates shell)
        ∷ [])
  in
  trans leftFactorization
    (trans integrationByPartsSubstitution
      (trans equationSubstitution rightExpansion))

record GalerkinEnstrophyAuthorityBoundary : Set where
  constructor galerkinEnstrophyAuthorityBoundary
  field
    coordinatePDEPairingProved : Set
    finiteCoordinateSummationProved : Set
    weightedShellIdentityProved : Set
    actualGalerkinCoordinatesConstructed : Set
    paraproductIndexRangesExhaustive : Set
    cutoffUniformConstantsProduced : Set

canonicalGalerkinEnstrophyAuthorityBoundary :
  GalerkinEnstrophyAuthorityBoundary
canonicalGalerkinEnstrophyAuthorityBoundary =
  galerkinEnstrophyAuthorityBoundary ⊤ ⊤ ⊤ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
