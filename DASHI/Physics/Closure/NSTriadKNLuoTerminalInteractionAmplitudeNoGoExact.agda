module DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionAmplitudeNoGoExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Repository-original scaling audit; no DOI is assigned.
--
-- Related background:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Audit the proposed terminal estimate
--
--   nonlinearTransfer <= C * dissipationTail * shellEnergy.
--
-- A Navier--Stokes energy transfer is trilinear in amplitude.  Dissipation
-- and shell energy are each quadratic, so their product is quartic.  Without
-- an additional normalization, lower bound, or differently homogeneous
-- factor, a universal cubic <= C quartic estimate cannot survive small
-- amplitude.
--
-- The exact rational witness below defeats the requested coefficient C=2:
--
--   amplitude = 1/8,
--   cubic transfer = 1/512,
--   2 * quadratic tail * quadratic energy = 1/2048.
--
-- This is a homogeneity no-go, not a construction of a Navier--Stokes
-- solution.  It prevents the formal development from silently promoting the
-- quartic target as a universal analytic theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_; _<_)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

two oneEighth : ℚ
two = Int.+ 2 / 1
oneEighth = Int.+ 1 / 8

cubicTransfer : ℚ → ℚ
cubicTransfer amplitude = amplitude * amplitude * amplitude

dissipationTail : ℚ → ℚ
dissipationTail amplitude = amplitude * amplitude

shellEnergy : ℚ → ℚ
shellEnergy amplitude = amplitude * amplitude

quarticCandidate : ℚ → ℚ → ℚ
quarticCandidate coefficient amplitude =
  coefficient * dissipationTail amplitude * shellEnergy amplitude

quarticCandidateFactorisation :
  (coefficient amplitude : ℚ) →
  quarticCandidate coefficient amplitude
  ≡ (coefficient * amplitude) * cubicTransfer amplitude
quarticCandidateFactorisation coefficient amplitude =
  solve (coefficient ∷ amplitude ∷ [])

witnessCubicValue :
  cubicTransfer oneEighth ≡ Int.+ 1 / 512
witnessCubicValue = solve []

witnessQuarticValue :
  quarticCandidate two oneEighth ≡ Int.+ 1 / 2048
witnessQuarticValue = solve []

coefficientTwoQuarticTargetFails :
  quarticCandidate two oneEighth < cubicTransfer oneEighth
coefficientTwoQuarticTargetFails =
  toWitness
    {a? = quarticCandidate two oneEighth
       <? cubicTransfer oneEighth}
    _

-- A degree-three replacement has the correct scalar homogeneity.  This is
-- only a bookkeeping identity: the analytic estimate producing a square-root
-- dissipation factor remains a genuine continuum obligation.
tailAmplitude : ℚ → ℚ
tailAmplitude amplitude = amplitude

homogeneousCandidate : ℚ → ℚ
homogeneousCandidate amplitude =
  tailAmplitude amplitude * shellEnergy amplitude

homogeneousCandidateHasCubicDegree :
  (amplitude : ℚ) →
  homogeneousCandidate amplitude ≡ cubicTransfer amplitude
homogeneousCandidateHasCubicDegree amplitude =
  solve (amplitude ∷ [])
