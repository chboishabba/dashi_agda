module DASHI.Physics.Closure.NSTriadKNHHCriticalAmplitudeAbsorptionRound91Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes
-- Equations in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- Authors: Qionglei Chen; Changxing Miao; Zhifei Zhang.
-- Title: "On the uniqueness of weak solutions for the 3D Navier-Stokes
-- equations".
-- Annales de l'Institut Henri Poincare C 26 (2009), 2165--2180.
-- DOI: 10.1016/j.anihpc.2009.01.008.
--
-- ROUND91 / CONSUMER-LEVEL CORRECTION
--
-- Round89 moved the viscous p.q factor inside the derivative tensor, exposing
-- the legitimate finite estimate
--
--   || Delta_K P div(grad u_hi tensor grad u_hi) ||_{H^-1}^2
--      <= lambda_K^3 D_hi^2.
--
-- That estimate is quadratic in the nonlinear vector (quartic in velocity).
-- It is NOT by itself a signed absorption theorem for the compact-transfer
-- relative-growth consumer.  At the energy level, the nonlinear contribution
-- is cubic in velocity while viscous dissipation is quadratic.  Under amplitude
-- scaling a this elementary obstruction is exact:
--
--   N(a) = a^3 = a * a^2 = a D(a).
--
-- Hence a uniform implication N <= c D requires an independent bound on the
-- critical amplitude a.  This is precisely the role played by the critical
-- block smallness hypothesis in the Cheskidov--Shvydkoy frequency-local
-- absorption argument.  The source does NOT prove that smallness for arbitrary
-- Leray solutions; it proves regularity once it holds.
--
-- The positive theorem below packages the exact algebra needed by DASHI:
--
--   nonlinear <= amplitude * D
--   amplitude + margin <= viscousFloor
--        ==> nonlinear + margin * D <= viscousFloor * D.
--
-- Thus the live Clay producer is no longer allowed to promote a raw H^-1 HH
-- square bound directly into coercivity.  It must additionally produce the
-- same-object critical-amplitude inequality which creates the strict surplus.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)

square : ℚ → ℚ
square a = a * a

cubic : ℚ → ℚ
cubic a = a * a * a

cubicFactorsThroughQuadraticDissipation :
  (a : ℚ) → cubic a ≡ a * square a
cubicFactorsThroughQuadraticDissipation a = solve (a ∷ [])

-- Exact calibration: doubling amplitude multiplies the cubic consumer by 8
-- but the quadratic dissipation by only 4.  This is the homogeneity reason a
-- scale-free unsigned HH estimate cannot manufacture viscous absorption.
two : ℚ
two = 1ℚ + 1ℚ

four eight : ℚ
four = two * two
eight = four * two

quadraticAtTwo : square two ≡ four
quadraticAtTwo = solve []

cubicAtTwo : cubic two ≡ eight
cubicAtTwo = solve []

eightEqualsTwoTimesFour : eight ≡ two * four
eightEqualsTwoTimesFour = solve []

record CriticalAmplitudeAbsorptionData : Set where
  constructor critical-amplitude-absorption-data
  field
    nonlinear criticalAmplitude dissipation viscousFloor margin : ℚ

    dissipationNonnegative : 0ℚ ≤ dissipation

    nonlinearFactorBound :
      nonlinear ≤ criticalAmplitude * dissipation

    strictAmplitudeHeadroom :
      criticalAmplitude + margin ≤ viscousFloor

open CriticalAmplitudeAbsorptionData public

criticalAmplitudeAbsorbsNonlinearWithMargin :
  (dataSet : CriticalAmplitudeAbsorptionData) →
  nonlinear dataSet + margin dataSet * dissipation dataSet
  ≤ viscousFloor dataSet * dissipation dataSet
criticalAmplitudeAbsorbsNonlinearWithMargin dataSet =
  let
    D = dissipation dataSet
    A = criticalAmplitude dataSet
    m = margin dataSet
    nu = viscousFloor dataSet

    addMargin :
      nonlinear dataSet + m * D
      ≤ (A * D) + m * D
    addMargin =
      ℚP.+-mono-≤
        (nonlinearFactorBound dataSet)
        ℚP.≤-refl

    factor : (A * D) + m * D ≡ (A + m) * D
    factor = solve (A ∷ m ∷ D ∷ [])

    scaleHeadroom : (A + m) * D ≤ nu * D
    scaleHeadroom =
      let instance dNN = nonNegative (dissipationNonnegative dataSet)
      in ℚP.*-monoʳ-≤-nonNeg D (strictAmplitudeHeadroom dataSet)
  in
  ℚP.≤-trans
    addMargin
    (substUpper factor scaleHeadroom)
  where
  substUpper :
    ∀ {a b c : ℚ} → a ≡ b → b ≤ c → a ≤ c
  substUpper refl proof = proof

record CriticalAmplitudeAbsorptionWithResidual : Set where
  constructor critical-amplitude-absorption-with-residual
  field
    core : CriticalAmplitudeAbsorptionData
    residual residualBudget : ℚ
    residualBound : residual ≤ residualBudget
    budgetFitsMargin :
      residualBudget ≤ margin core * dissipation core

open CriticalAmplitudeAbsorptionWithResidual public

criticalAmplitudeAbsorbsNonlinearAndResidual :
  (dataSet : CriticalAmplitudeAbsorptionWithResidual) →
  nonlinear (core dataSet) + residual dataSet
  ≤ viscousFloor (core dataSet) * dissipation (core dataSet)
criticalAmplitudeAbsorbsNonlinearAndResidual dataSet =
  let
    C = core dataSet
    residualToMargin :
      nonlinear C + residual dataSet
      ≤ nonlinear C + margin C * dissipation C
    residualToMargin =
      ℚP.+-mono-≤
        ℚP.≤-refl
        (ℚP.≤-trans (residualBound dataSet) (budgetFitsMargin dataSet))
  in
  ℚP.≤-trans residualToMargin
    (criticalAmplitudeAbsorbsNonlinearWithMargin C)

round91RawHHHMinusOneSquareBoundAloneImpliesViscousAbsorption : Bool
round91RawHHHMinusOneSquareBoundAloneImpliesViscousAbsorption = false

round91CriticalAmplitudeHeadroomIsRequiredByThisAbsorptionRoute : Bool
round91CriticalAmplitudeHeadroomIsRequiredByThisAbsorptionRoute = true

round91CriticalAmplitudePlusResidualAbsorptionAlgebraClosed : Bool
round91CriticalAmplitudePlusResidualAbsorptionAlgebraClosed = true

round91RawHHHMinusOneSquareBoundAloneImpliesViscousAbsorptionIsFalse :
  round91RawHHHMinusOneSquareBoundAloneImpliesViscousAbsorption ≡ false
round91RawHHHMinusOneSquareBoundAloneImpliesViscousAbsorptionIsFalse = refl

round91CriticalAmplitudeHeadroomIsRequiredByThisAbsorptionRouteIsTrue :
  round91CriticalAmplitudeHeadroomIsRequiredByThisAbsorptionRoute ≡ true
round91CriticalAmplitudeHeadroomIsRequiredByThisAbsorptionRouteIsTrue = refl

round91CriticalAmplitudePlusResidualAbsorptionAlgebraClosedIsTrue :
  round91CriticalAmplitudePlusResidualAbsorptionAlgebraClosed ≡ true
round91CriticalAmplitudePlusResidualAbsorptionAlgebraClosedIsTrue = refl
