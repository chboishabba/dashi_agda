module DASHI.Physics.Closure.NSTriadKNLuoFiniteCriticalShellFunctionalExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Implement the finite shell-resolved critical functional underlying
--
--   A_q^2 = integral sum_p eta(q,p) lambda_p^3 ||u_p||_2^2.
--
-- On an exact p-shell, ||grad u_p||_2^2 is represented by
-- lambda_p^2 ||u_p||_2^2.  Therefore the two descriptions
--
--   eta lambda_p ||grad u_p||_2^2
--
-- and
--
--   eta lambda_p^3 ||u_p||_2^2
--
-- agree pointwise and after every finite shell sum.  This is the precise
-- finite bridge from terminal dissipation to the critical half-derivative
-- functional.  No decay or continuum estimate is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteCenteredCommutatorBudgetExact as Sum

record CriticalShellCell : Set where
  constructor critical-shell-cell
  field
    interactionWeight shellScale velocitySquaredMass : ℚ

open CriticalShellCell public

gradientSquaredMass : CriticalShellCell → ℚ
gradientSquaredMass cell =
  shellScale cell * shellScale cell * velocitySquaredMass cell

criticalDensityFromGradient : CriticalShellCell → ℚ
criticalDensityFromGradient cell =
  interactionWeight cell * shellScale cell * gradientSquaredMass cell

criticalDensityFromVelocity : CriticalShellCell → ℚ
criticalDensityFromVelocity cell =
  interactionWeight cell
  * shellScale cell * shellScale cell * shellScale cell
  * velocitySquaredMass cell

criticalDensityRepresentationsAgree :
  (cell : CriticalShellCell) →
  criticalDensityFromGradient cell ≡ criticalDensityFromVelocity cell
criticalDensityRepresentationsAgree cell =
  solve
    ( interactionWeight cell
    ∷ shellScale cell
    ∷ velocitySquaredMass cell
    ∷ [])

criticalFunctionalFromGradient : List CriticalShellCell → ℚ
criticalFunctionalFromGradient cells =
  Sum.sumBy cells criticalDensityFromGradient

criticalFunctionalFromVelocity : List CriticalShellCell → ℚ
criticalFunctionalFromVelocity cells =
  Sum.sumBy cells criticalDensityFromVelocity

criticalFunctionalRepresentationsAgree :
  (cells : List CriticalShellCell) →
  criticalFunctionalFromGradient cells
  ≡ criticalFunctionalFromVelocity cells
criticalFunctionalRepresentationsAgree [] = refl
criticalFunctionalRepresentationsAgree (cell ∷ cells)
  rewrite criticalDensityRepresentationsAgree cell
        | criticalFunctionalRepresentationsAgree cells = refl
