module DASHI.Physics.Closure.NSTriadKNCheskidovShvydkoyFiniteShellAbsorptionRound91Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes
-- Equations in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
-- arXiv: 0708.3067.
--
-- The source derives, after frequency localization, a high-shell inequality
-- whose nonlinear side is bounded by a dissipation-weighted critical block
-- amplitude lambda_q^{-1} ||u_q||_infinity.  If that amplitude is uniformly
-- below a constant multiple of viscosity, the nonlinear term is absorbed by
-- the viscous sum.  The paper proves a conditional regularity criterion; it
-- does not prove that the critical amplitude is small for arbitrary Leray
-- solutions.
--
-- ROUND91 / FINITE PERIODIC ABSORPTION CORE
--
-- This module extracts exactly the finite algebra needed on the DASHI cutoff
-- carrier.  Each high shell supplies
--
--   D_q >= 0,     A_q <= A_*,
--
-- where D_q is the shell dissipation mass and A_q is the dimensionless
-- critical amplitude.  Then
--
--   sum D_q A_q <= A_* sum D_q.
--
-- Consequently, if a frequency-local nonlinear estimate gives
--
--   N_hi <= C sum D_q A_q
--
-- and C A_* + delta <= nu, then
--
--   N_hi + delta sum D_q <= nu sum D_q.
--
-- This is the exact strict surplus statement required by a shellwise
-- absorption route.  It makes the remaining Clay-level producer explicit:
-- obtain A_* < nu/C on the SAME physical high-shell family, rather than
-- attempting to infer absorption from an unsigned H^{-1} square estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record CriticalShellCell (threshold : ℚ) : Set where
  constructor critical-shell-cell
  field
    dissipation amplitude : ℚ
    dissipationNonnegative : 0ℚ ≤ dissipation
    amplitudeNonnegative : 0ℚ ≤ amplitude
    amplitudeBelowThreshold : amplitude ≤ threshold

open CriticalShellCell public

dissipationSum : ∀ {threshold} → List (CriticalShellCell threshold) → ℚ
dissipationSum [] = 0ℚ
dissipationSum (cell ∷ cells) =
  dissipation cell + dissipationSum cells

weightedAmplitudeSum : ∀ {threshold} → List (CriticalShellCell threshold) → ℚ
weightedAmplitudeSum [] = 0ℚ
weightedAmplitudeSum (cell ∷ cells) =
  dissipation cell * amplitude cell + weightedAmplitudeSum cells

dissipationSumNonnegative :
  ∀ {threshold} (cells : List (CriticalShellCell threshold)) →
  0ℚ ≤ dissipationSum cells
dissipationSumNonnegative [] = ℚP.≤-refl
dissipationSumNonnegative (cell ∷ cells) =
  ℚP.+-mono-≤
    (dissipationNonnegative cell)
    (dissipationSumNonnegative cells)

weightedAmplitudeBelowThresholdDissipation :
  ∀ {threshold}
    (thresholdNonnegative : 0ℚ ≤ threshold)
    (cells : List (CriticalShellCell threshold)) →
  weightedAmplitudeSum cells ≤ threshold * dissipationSum cells
weightedAmplitudeBelowThresholdDissipation thresholdNN [] = ℚP.≤-refl
weightedAmplitudeBelowThresholdDissipation {threshold} thresholdNN (cell ∷ cells) =
  let
    head :
      dissipation cell * amplitude cell
      ≤ dissipation cell * threshold
    head =
      let instance dNN = nonNegative (dissipationNonnegative cell)
      in ℚP.*-monoˡ-≤-nonNeg
        (dissipation cell) (amplitudeBelowThreshold cell)

    tail = weightedAmplitudeBelowThresholdDissipation thresholdNN cells

    summed :
      dissipation cell * amplitude cell + weightedAmplitudeSum cells
      ≤ dissipation cell * threshold + threshold * dissipationSum cells
    summed = ℚP.+-mono-≤ head tail

    targetMeaning :
      dissipation cell * threshold + threshold * dissipationSum cells
      ≡ threshold * (dissipation cell + dissipationSum cells)
    targetMeaning = solve
      (dissipation cell ∷ threshold ∷ dissipationSum cells ∷ [])
  in
  subst
    (λ upper →
      dissipation cell * amplitude cell + weightedAmplitudeSum cells ≤ upper)
    targetMeaning
    summed

record FiniteHighShellAbsorptionData : Set₁ where
  constructor finite-high-shell-absorption-data
  field
    threshold nonlinearConstant viscosity strictMargin : ℚ
    thresholdNonnegative : 0ℚ ≤ threshold
    nonlinearConstantNonnegative : 0ℚ ≤ nonlinearConstant
    strictMarginNonnegative : 0ℚ ≤ strictMargin

    cells : List (CriticalShellCell threshold)
    nonlinearBudget : ℚ

    frequencyLocalNonlinearBound :
      nonlinearBudget
      ≤ nonlinearConstant * weightedAmplitudeSum cells

    viscosityHeadroom :
      nonlinearConstant * threshold + strictMargin ≤ viscosity

open FiniteHighShellAbsorptionData public

finiteHighShellStrictAbsorption :
  (dataSet : FiniteHighShellAbsorptionData) →
  nonlinearBudget dataSet
    + strictMargin dataSet * dissipationSum (cells dataSet)
  ≤ viscosity dataSet * dissipationSum (cells dataSet)
finiteHighShellStrictAbsorption dataSet =
  let
    C = nonlinearConstant dataSet
    A = threshold dataSet
    delta = strictMargin dataSet
    nu = viscosity dataSet
    D = dissipationSum (cells dataSet)
    W = weightedAmplitudeSum (cells dataSet)

    W≤AD : W ≤ A * D
    W≤AD =
      weightedAmplitudeBelowThresholdDissipation
        (thresholdNonnegative dataSet) (cells dataSet)

    CW≤CAD : C * W ≤ C * (A * D)
    CW≤CAD =
      let instance cNN = nonNegative (nonlinearConstantNonnegative dataSet)
      in ℚP.*-monoˡ-≤-nonNeg C W≤AD

    nonlinearToCAD : nonlinearBudget dataSet ≤ (C * A) * D
    nonlinearToCAD =
      ℚP.≤-trans
        (frequencyLocalNonlinearBound dataSet)
        (subst
          (λ upper → C * W ≤ upper)
          (solve (C ∷ A ∷ D ∷ []))
          CW≤CAD)

    addMargin :
      nonlinearBudget dataSet + delta * D
      ≤ (C * A) * D + delta * D
    addMargin = ℚP.+-mono-≤ nonlinearToCAD ℚP.≤-refl

    factorMargin :
      (C * A) * D + delta * D ≡ (C * A + delta) * D
    factorMargin = solve (C ∷ A ∷ delta ∷ D ∷ [])

    scaleHeadroom :
      (C * A + delta) * D ≤ nu * D
    scaleHeadroom =
      let instance dNN = nonNegative (dissipationSumNonnegative (cells dataSet))
      in ℚP.*-monoʳ-≤-nonNeg D (viscosityHeadroom dataSet)
  in
  ℚP.≤-trans
    addMargin
    (subst
      (λ lower → lower ≤ nu * D)
      (symEq factorMargin)
      scaleHeadroom)
  where
  symEq : ∀ {a b : ℚ} → a ≡ b → b ≡ a
  symEq refl = refl

round91FiniteCriticalBlockAbsorptionAlgebraClosed : Bool
round91FiniteCriticalBlockAbsorptionAlgebraClosed = true

round91FrequencyLocalNonlinearEstimateStillPhysical : Bool
round91FrequencyLocalNonlinearEstimateStillPhysical = true

round91CriticalAmplitudeHeadroomStillPhysical : Bool
round91CriticalAmplitudeHeadroomStillPhysical = true

round91FiniteCriticalBlockAbsorptionAlgebraClosedIsTrue :
  round91FiniteCriticalBlockAbsorptionAlgebraClosed ≡ true
round91FiniteCriticalBlockAbsorptionAlgebraClosedIsTrue = refl
