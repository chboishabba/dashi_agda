module DASHI.Physics.Closure.NSTriadKNSupercriticalResidenceDissipationChargeRound97Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Zhen Lei; Xiao Ren.
-- Title: "Quantitative partial regularity of the Navier-Stokes equations
-- and applications".
-- arXiv:2210.01783 (2022).
-- DOI: not asserted from the supplied arXiv manuscript.
-- Uses: the disjoint-interval / finite-dissipation charging principle behind
-- quantitative epochs of regularity, not any conditional regularity result.
--
-- Author: John G. Heywood.
-- Title: "Epochs of Regularity for Weak Solutions of the Navier-Stokes
-- Equations in Unbounded Domains".
-- Tohoku Mathematical Journal 40 (1988), 293--313.
-- DOI: 10.2748/tmj/1178228031.
-- Uses: calibration that disjoint bad epochs can be charged to finite
-- Dirichlet expenditure.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes
-- Equations in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- ROUND97 / UNCONDITIONAL SUPERCRITICAL-RESIDENCE PRICE
--
-- Work in the squared/radical-free shell variables.  Assume the concrete
-- Bernstein relation
--
--   A^2 <= C_B * lambda * E,
--
-- and D = lambda^2 * E.  On a supercritical cell A_* < A, with all physical
-- quantities nonnegative, monotonicity of squaring and multiplication gives
--
--   lambda * A_*^2 <= C_B * D.
--
-- Thus every unit of time spent above the critical amplitude threshold at
-- shell lambda consumes a definite frequency-weighted amount of dissipation.
-- A finite disjoint family of time cells therefore satisfies
--
--   sum dt * lambda * A_*^2 <= C_B * sum dt * D.
--
-- This is the exact finite occupation mechanism suggested by Lei--Ren and
-- Heywood, now stated in the shell currency used by the DASHI program.
-- It intentionally does NOT claim the stronger open estimate
--   integral D (A-A_*)_+ <= escape.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; _<_ ; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational

square : ℚ → ℚ
square x = x * x

record SupercriticalShellCell (bernsteinConstant threshold : ℚ) : Set where
  constructor supercritical-shell-cell
  field
    shellScale shellEnergy amplitude dissipation timeWeight : ℚ

    bernsteinConstantNonnegative : 0ℚ ≤ bernsteinConstant
    thresholdNonnegative : 0ℚ ≤ threshold
    shellScaleNonnegative : 0ℚ ≤ shellScale
    shellEnergyNonnegative : 0ℚ ≤ shellEnergy
    amplitudeNonnegative : 0ℚ ≤ amplitude
    timeWeightNonnegative : 0ℚ ≤ timeWeight

    supercritical : threshold < amplitude

    amplitudeSquaredBernstein :
      square amplitude ≤ bernsteinConstant * (shellScale * shellEnergy)

    dissipationMeaning :
      dissipation ≡ shellScale * shellScale * shellEnergy

open SupercriticalShellCell public

thresholdSquareBelowAmplitudeSquare :
  ∀ {C threshold} (cell : SupercriticalShellCell C threshold) →
  square threshold ≤ square (amplitude cell)
thresholdSquareBelowAmplitudeSquare {threshold = threshold} cell =
  Rational.nonnegativeProductMonotone
    (thresholdNonnegative cell)
    (thresholdNonnegative cell)
    (amplitudeNonnegative cell)
    (amplitudeNonnegative cell)
    (ℚP.<⇒≤ (supercritical cell))
    (ℚP.<⇒≤ (supercritical cell))

supercriticalCellHasDissipationPrice :
  ∀ {C threshold} (cell : SupercriticalShellCell C threshold) →
  shellScale cell * square threshold ≤ C * dissipation cell
supercriticalCellHasDissipationPrice {C} {threshold} cell =
  let
    lambda = shellScale cell
    E = shellEnergy cell
    A = amplitude cell

    thresholdToA : square threshold ≤ square A
    thresholdToA = thresholdSquareBelowAmplitudeSquare cell

    lambdaThresholdToLambdaA :
      lambda * square threshold ≤ lambda * square A
    lambdaThresholdToLambdaA =
      let instance lambdaNN = nonNegative (shellScaleNonnegative cell)
      in ℚP.*-monoˡ-≤-nonNeg lambda thresholdToA

    lambdaAToBernstein :
      lambda * square A
      ≤ lambda * (C * (lambda * E))
    lambdaAToBernstein =
      let instance lambdaNN = nonNegative (shellScaleNonnegative cell)
      in ℚP.*-monoˡ-≤-nonNeg lambda (amplitudeSquaredBernstein cell)

    rearrange :
      lambda * (C * (lambda * E))
      ≡ C * (lambda * lambda * E)
    rearrange = solve (lambda ∷ C ∷ E ∷ [])

    toRawD :
      lambda * square threshold ≤ C * (lambda * lambda * E)
    toRawD =
      ℚP.≤-trans lambdaThresholdToLambdaA
        (subst
          (λ upper → lambda * square A ≤ upper)
          rearrange lambdaAToBernstein)
  in
  subst
    (λ D → lambda * square threshold ≤ C * D)
    (dissipationMeaning cell)
    toRawD

weightedResidencePrice :
  ∀ {C threshold} (cell : SupercriticalShellCell C threshold) →
  timeWeight cell * (shellScale cell * square threshold)
  ≤ C * (timeWeight cell * dissipation cell)
weightedResidencePrice {C} cell =
  let
    dt = timeWeight cell
    base = supercriticalCellHasDissipationPrice cell
    scaled :
      dt * (shellScale cell * square _) ≤ dt * (C * dissipation cell)
    scaled =
      let instance dtNN = nonNegative (timeWeightNonnegative cell)
      in ℚP.*-monoˡ-≤-nonNeg dt base
    rearrange :
      dt * (C * dissipation cell) ≡ C * (dt * dissipation cell)
    rearrange = solve (dt ∷ C ∷ dissipation cell ∷ [])
  in
  subst
    (λ upper →
      dt * (shellScale cell * square _) ≤ upper)
    rearrange scaled

sumResidenceCost :
  ∀ {C threshold} → List (SupercriticalShellCell C threshold) → ℚ
sumResidenceCost [] = 0ℚ
sumResidenceCost {threshold = threshold} (cell ∷ rest) =
  timeWeight cell * (shellScale cell * square threshold)
    + sumResidenceCost rest

sumWeightedDissipation :
  ∀ {C threshold} → List (SupercriticalShellCell C threshold) → ℚ
sumWeightedDissipation [] = 0ℚ
sumWeightedDissipation (cell ∷ rest) =
  timeWeight cell * dissipation cell + sumWeightedDissipation rest

finiteSupercriticalResidenceChargedToDissipation :
  ∀ {C threshold} →
  (cells : List (SupercriticalShellCell C threshold)) →
  sumResidenceCost cells ≤ C * sumWeightedDissipation cells
finiteSupercriticalResidenceChargedToDissipation [] = ℚP.≤-refl
finiteSupercriticalResidenceChargedToDissipation {C} {threshold}
    (cell ∷ rest) =
  let
    head = weightedResidencePrice cell
    tail = finiteSupercriticalResidenceChargedToDissipation rest
    added = ℚP.+-mono-≤ head tail

    rightMeaning :
      C * (timeWeight cell * dissipation cell)
        + C * sumWeightedDissipation rest
      ≡ C * sumWeightedDissipation (cell ∷ rest)
    rightMeaning = solve
      (C ∷ timeWeight cell ∷ dissipation cell
       ∷ sumWeightedDissipation rest ∷ [])
  in
  subst
    (λ upper → sumResidenceCost (cell ∷ rest) ≤ upper)
    rightMeaning added

round97SupercriticalResidenceHasDissipationPrice : Bool
round97SupercriticalResidenceHasDissipationPrice = true

round97WeightedExcessOccupationStillStronger : Bool
round97WeightedExcessOccupationStillStronger = true

round97SupercriticalResidenceHasDissipationPriceIsTrue :
  round97SupercriticalResidenceHasDissipationPrice ≡ true
round97SupercriticalResidenceHasDissipationPriceIsTrue = refl
