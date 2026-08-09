module DASHI.Physics.Closure.NSTriadKNHHBadTimeScaleGainRound31Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "A Unified Approach to Regularity Problems for the 3D
-- Navier-Stokes and Euler Equations: The Use of Kolmogorov's
-- Dissipation Range".
-- DOI: 10.1007/s00021-014-0167-4.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- The raw Bernstein bad-amplitude cost has scale lambda^3 E whereas shell
-- diffusion has scale nu lambda^2 E.  This file proves the exact missing
-- mechanism:
--
--   (bad occupation time) * lambda <= eta * nu
--
-- implies
--
--   integral_bad lambda^3 E <= eta * nu lambda^2 E.
--
-- Thus time localization must contribute one inverse shell scale.  The
-- theorem is finite and exact, is uniform in the shell label, and sums over
-- arbitrary finite bad-shell families.  It does not assume a BKM norm,
-- Serrin norm, target critical supremum, or a pre-existing regular solution.
-- Producing the physical occupation estimate remains the PDE frontier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNScaleNormalisedAmplitudeAuditRound29Exact as Scale

record HHBadTimeScaleCell : Set where
  constructor hh-bad-time-scale-cell
  field
    activeTime shellScale shellEnergy viscosity eta : ℚ

    activeTimeNonnegative : 0ℚ ≤ activeTime
    shellScaleNonnegative : 0ℚ ≤ shellScale
    shellEnergyNonnegative : 0ℚ ≤ shellEnergy
    viscosityNonnegative : 0ℚ ≤ viscosity
    etaNonnegative : 0ℚ ≤ eta

    -- This is the exact one-inverse-scale occupation condition.
    timeScaleGain :
      activeTime * shellScale ≤ eta * viscosity

open HHBadTimeScaleCell public

criticalShellFactor : HHBadTimeScaleCell → ℚ
criticalShellFactor cell =
  shellScale cell * shellScale cell * shellEnergy cell

rawBernsteinBadCost : HHBadTimeScaleCell → ℚ
rawBernsteinBadCost cell =
  activeTime cell
  * shellScale cell * shellScale cell * shellScale cell
  * shellEnergy cell

shellDiffusionCost : HHBadTimeScaleCell → ℚ
shellDiffusionCost cell =
  viscosity cell
  * shellScale cell * shellScale cell
  * shellEnergy cell

etaShellDiffusionCost : HHBadTimeScaleCell → ℚ
etaShellDiffusionCost cell =
  eta cell * shellDiffusionCost cell

criticalShellFactorNonnegative :
  ∀ cell → 0ℚ ≤ criticalShellFactor cell
criticalShellFactorNonnegative cell =
  let
    instance
      shellScaleNN = nonNegative (shellScaleNonnegative cell)
      shellScaleSquareNN =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (shellScale cell) (shellScale cell)
      shellEnergyNN = nonNegative (shellEnergyNonnegative cell)
      criticalFactorNN =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (shellScale cell * shellScale cell)
          (shellEnergy cell)
  in
  ℚP.nonNegative⁻¹ (criticalShellFactor cell)

timeScaleGainAbsorbsRawBernstein :
  ∀ cell →
  rawBernsteinBadCost cell ≤ etaShellDiffusionCost cell
timeScaleGainAbsorbsRawBernstein cell =
  let
    factor = criticalShellFactor cell

    multiplied :
      (activeTime cell * shellScale cell) * factor
      ≤ (eta cell * viscosity cell) * factor
    multiplied =
      let
        instance
          factorNN = nonNegative (criticalShellFactorNonnegative cell)
      in
      ℚP.*-monoʳ-≤-nonNeg factor (timeScaleGain cell)

    leftMeaning :
      (activeTime cell * shellScale cell) * factor
      ≡ rawBernsteinBadCost cell
    leftMeaning =
      solve
        ( activeTime cell
        ∷ shellScale cell
        ∷ shellEnergy cell
        ∷ [])

    rightMeaning :
      (eta cell * viscosity cell) * factor
      ≡ etaShellDiffusionCost cell
    rightMeaning =
      solve
        ( eta cell
        ∷ viscosity cell
        ∷ shellScale cell
        ∷ shellEnergy cell
        ∷ [])
  in
  subst
    (λ left → left ≤ etaShellDiffusionCost cell)
    leftMeaning
    (subst
      (λ right →
        (activeTime cell * shellScale cell) * factor ≤ right)
      rightMeaning
      multiplied)

sumRawBernsteinBadCost : List HHBadTimeScaleCell → ℚ
sumRawBernsteinBadCost [] = 0ℚ
sumRawBernsteinBadCost (cell ∷ rest) =
  rawBernsteinBadCost cell + sumRawBernsteinBadCost rest

sumEtaShellDiffusionCost : List HHBadTimeScaleCell → ℚ
sumEtaShellDiffusionCost [] = 0ℚ
sumEtaShellDiffusionCost (cell ∷ rest) =
  etaShellDiffusionCost cell + sumEtaShellDiffusionCost rest

finiteTimeLocalizedHHBadAbsorption :
  ∀ cells →
  sumRawBernsteinBadCost cells ≤ sumEtaShellDiffusionCost cells
finiteTimeLocalizedHHBadAbsorption [] = ℚP.≤-refl
finiteTimeLocalizedHHBadAbsorption (cell ∷ rest) =
  ℚP.+-mono-≤
    (timeScaleGainAbsorbsRawBernstein cell)
    (finiteTimeLocalizedHHBadAbsorption rest)

------------------------------------------------------------------------
-- Exact equality at the critical occupation time.
--
-- If tau = eta * nu * lambda^-1, then the bad Bernstein cost is not merely
-- bounded by, but exactly equals, eta times shell diffusion.
------------------------------------------------------------------------

criticalOccupationTime :
  Scale.InverseShellScale → ℚ → ℚ → ℚ
criticalOccupationTime scale eta viscosity =
  eta * viscosity * Scale.inverseScale scale

criticalOccupationRawCost :
  Scale.InverseShellScale → ℚ → ℚ → ℚ → ℚ
criticalOccupationRawCost scale eta viscosity energy =
  criticalOccupationTime scale eta viscosity
  * Scale.shellScale scale * Scale.shellScale scale
  * Scale.shellScale scale * energy

criticalOccupationDiffusion :
  Scale.InverseShellScale → ℚ → ℚ → ℚ → ℚ
criticalOccupationDiffusion scale eta viscosity energy =
  eta
  * (viscosity
      * Scale.shellScale scale * Scale.shellScale scale
      * energy)

criticalOccupationRepairsExactlyOneScale :
  ∀ scale eta viscosity energy →
  criticalOccupationRawCost scale eta viscosity energy
  ≡ criticalOccupationDiffusion scale eta viscosity energy
criticalOccupationRepairsExactlyOneScale scale eta viscosity energy =
  trans
    (solve
      ( eta
      ∷ viscosity
      ∷ Scale.inverseScale scale
      ∷ Scale.shellScale scale
      ∷ energy
      ∷ []))
    (trans
      (cong
        (λ product →
          product
          * (eta * viscosity
             * Scale.shellScale scale * Scale.shellScale scale
             * energy))
        (Scale.inverseLaw scale))
      (solve
        ( eta
        ∷ viscosity
        ∷ Scale.shellScale scale
        ∷ energy
        ∷ [])))

------------------------------------------------------------------------
-- Separate amplitude-route formulation.
--
-- This is the other exact way to repair the same one-power loss: prove the
-- physical pointwise bad amplitude already lies below eta nu lambda^2.
------------------------------------------------------------------------

record HHBadAmplitudeCell : Set where
  constructor hh-bad-amplitude-cell
  field
    amplitude shellScale shellEnergy viscosity eta : ℚ

    amplitudeNonnegative : 0ℚ ≤ amplitude
    shellScaleNonnegative : 0ℚ ≤ shellScale
    shellEnergyNonnegative : 0ℚ ≤ shellEnergy
    viscosityNonnegative : 0ℚ ≤ viscosity
    etaNonnegative : 0ℚ ≤ eta

    viscousAmplitudeGain :
      amplitude
      ≤ eta * viscosity * shellScale * shellScale

open HHBadAmplitudeCell public

amplitudeBadCost : HHBadAmplitudeCell → ℚ
amplitudeBadCost cell =
  amplitude cell * shellEnergy cell

amplitudeEtaDiffusion : HHBadAmplitudeCell → ℚ
amplitudeEtaDiffusion cell =
  eta cell
  * (viscosity cell
      * shellScale cell * shellScale cell
      * shellEnergy cell)

viscousAmplitudeGainAbsorbsHHBad :
  ∀ cell → amplitudeBadCost cell ≤ amplitudeEtaDiffusion cell
viscousAmplitudeGainAbsorbsHHBad cell =
  let
    upper =
      eta cell * viscosity cell
      * shellScale cell * shellScale cell

    upperNonnegative : 0ℚ ≤ upper
    upperNonnegative =
      let
        instance
          etaNN = nonNegative (etaNonnegative cell)
          viscosityNN = nonNegative (viscosityNonnegative cell)
          etaViscosityNN =
            ℚP.nonNeg*nonNeg⇒nonNeg (eta cell) (viscosity cell)
          scaleNN = nonNegative (shellScaleNonnegative cell)
          firstScaleNN =
            ℚP.nonNeg*nonNeg⇒nonNeg
              (eta cell * viscosity cell) (shellScale cell)
          secondScaleNN =
            ℚP.nonNeg*nonNeg⇒nonNeg
              (eta cell * viscosity cell * shellScale cell)
              (shellScale cell)
      in
      ℚP.nonNegative⁻¹ upper

    multiplied :
      amplitude cell * shellEnergy cell
      ≤ upper * shellEnergy cell
    multiplied =
      L2.nonnegativeProductMonotone
        (amplitudeNonnegative cell)
        (shellEnergyNonnegative cell)
        upperNonnegative
        (shellEnergyNonnegative cell)
        (viscousAmplitudeGain cell)
        ℚP.≤-refl

    rightMeaning :
      upper * shellEnergy cell
      ≡ amplitudeEtaDiffusion cell
    rightMeaning =
      solve
        ( eta cell
        ∷ viscosity cell
        ∷ shellScale cell
        ∷ shellEnergy cell
        ∷ [])
  in
  subst
    (λ right → amplitudeBadCost cell ≤ right)
    rightMeaning
    multiplied

hhBadTimeScaleGainAlgebraClosed : Bool
hhBadTimeScaleGainAlgebraClosed = true

hhBadFiniteOccupationAbsorptionClosed : Bool
hhBadFiniteOccupationAbsorptionClosed = true

hhBadExactCriticalOccupationIdentityClosed : Bool
hhBadExactCriticalOccupationIdentityClosed = true

physicalHHBadOccupationEstimateConstructed : Bool
physicalHHBadOccupationEstimateConstructed = false

physicalHHBadAmplitudeGainConstructed : Bool
physicalHHBadAmplitudeGainConstructed = false

hhBadTimeScaleGainAlgebraClosedIsTrue :
  hhBadTimeScaleGainAlgebraClosed ≡ true
hhBadTimeScaleGainAlgebraClosedIsTrue = refl

hhBadFiniteOccupationAbsorptionClosedIsTrue :
  hhBadFiniteOccupationAbsorptionClosed ≡ true
hhBadFiniteOccupationAbsorptionClosedIsTrue = refl

hhBadExactCriticalOccupationIdentityClosedIsTrue :
  hhBadExactCriticalOccupationIdentityClosed ≡ true
hhBadExactCriticalOccupationIdentityClosedIsTrue = refl
