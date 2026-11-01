module DASHI.Physics.Closure.NSTriadKNLuoDissipationWavenumberAmplitudeRepairExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "A Unified Approach to Regularity Problems for the 3D Navier-Stokes
-- and Euler Equations: The Use of Kolmogorov's Dissipation Range".
-- DOI: 10.1007/s00021-014-0167-4.
-- arXiv DOI: 10.48550/arXiv.1102.1944.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- The raw Bernstein amplitude budget is supercritical by one frequency power.
-- This module records the precise repair supplied by a dissipation-wavenumber
-- condition.  If a high shell obeys
--
--   amplitude <= c * nu * lambda^2,
--
-- then multiplication by its nonnegative enstrophy E gives
--
--   amplitude * E
--     <= c * (nu * lambda^2 * E).
--
-- The right side is exactly c times shell diffusion.  Thus F7 should not seek
-- a universal Bernstein estimate; it should prove that bad high shells lie in
-- a dynamically viscous regime, while the finitely many low shells are paid by
-- an explicit reservoir.  The theorem here closes the coefficient transport,
-- not the Navier-Stokes production of the high-shell condition.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record DissipationWavenumberAmplitudeCell : Set where
  constructor dissipationWavenumberAmplitudeCell
  field
    amplitude coefficient viscosity eigenvalue enstrophy : ℚ

    amplitudeNonnegative : 0ℚ ≤ amplitude
    coefficientNonnegative : 0ℚ ≤ coefficient
    viscosityNonnegative : 0ℚ ≤ viscosity
    eigenvalueNonnegative : 0ℚ ≤ eigenvalue
    enstrophyNonnegative : 0ℚ ≤ enstrophy

    viscousHighModeCondition :
      amplitude ≤ coefficient * viscosity * eigenvalue

open DissipationWavenumberAmplitudeCell public

shellDiffusion : DissipationWavenumberAmplitudeCell → ℚ
shellDiffusion cell =
  viscosity cell * eigenvalue cell * enstrophy cell

amplitudeStretching : DissipationWavenumberAmplitudeCell → ℚ
amplitudeStretching cell = amplitude cell * enstrophy cell

coefficientTimesShellDiffusion :
  DissipationWavenumberAmplitudeCell → ℚ
coefficientTimesShellDiffusion cell =
  coefficient cell * shellDiffusion cell

viscousHighModeAmplitudeAbsorption :
  ∀ cell →
  amplitudeStretching cell ≤ coefficientTimesShellDiffusion cell
viscousHighModeAmplitudeAbsorption cell =
  let
    upper = coefficient cell * viscosity cell * eigenvalue cell

    upperNonnegative : 0ℚ ≤ upper
    upperNonnegative =
      let
        instance
          coefficientNN = nonNegative (coefficientNonnegative cell)
          viscosityNN = nonNegative (viscosityNonnegative cell)
          firstProductNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (coefficient cell) (viscosity cell)
          eigenNN = nonNegative (eigenvalueNonnegative cell)
          secondProductNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (coefficient cell * viscosity cell)
              (eigenvalue cell)
      in
      ℚₚ.nonNegative⁻¹ upper

    multiplied :
      amplitude cell * enstrophy cell
      ≤ upper * enstrophy cell
    multiplied =
      L2.nonnegativeProductMonotone
        (amplitudeNonnegative cell)
        (enstrophyNonnegative cell)
        upperNonnegative
        (enstrophyNonnegative cell)
        (viscousHighModeCondition cell)
        ℚₚ.≤-refl

    rightMeaning :
      upper * enstrophy cell
      ≡ coefficientTimesShellDiffusion cell
    rightMeaning =
      solve
        ( coefficient cell
        ∷ viscosity cell
        ∷ eigenvalue cell
        ∷ enstrophy cell
        ∷ [])
  in
  subst
    (λ right → amplitudeStretching cell ≤ right)
    rightMeaning
    multiplied

record DissipationAmplitudeAuthorityBoundary : Set where
  constructor dissipationAmplitudeAuthorityBoundary
  field
    highModeAmplitudeTransportProved : Set
    rawBernsteinObstructionRepairedConditionally : Set
    navierStokesDissipationWavenumberBoundProduced : Set
    lowModeReservoirCriticallyIntegrated : Set
    universalSmallCoefficientProduced : Set

canonicalDissipationAmplitudeAuthorityBoundary :
  DissipationAmplitudeAuthorityBoundary
canonicalDissipationAmplitudeAuthorityBoundary =
  dissipationAmplitudeAuthorityBoundary ⊤ ⊤ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
