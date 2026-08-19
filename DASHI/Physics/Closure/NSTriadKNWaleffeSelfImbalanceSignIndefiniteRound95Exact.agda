module DASHI.Physics.Closure.NSTriadKNWaleffeSelfImbalanceSignIndefiniteRound95Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- ROUND95 / SELF-TRIAD SIGN FALSIFIER
--
-- The normalized-phase self energy contribution contains
--
--   I = lambda_k E_k (E_p-E_q)
--     + lambda_p E_p (E_q-E_k)
--     + lambda_q E_q (E_k-E_p).
--
-- This file gives an exact rational witness showing that even with one fixed
-- strictly ordered signed-eigenvalue triple, I can have either sign depending
-- only on the modal energy distribution.  Therefore helicity class plus
-- eigenvalue ordering cannot by itself turn the self-triad normalized drift
-- into a universal favorable-sign theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

neg : ℚ → ℚ
neg x = - x

imbalance : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
imbalance lambdaK lambdaP lambdaQ energyK energyP energyQ =
    lambdaK * energyK * (energyP + neg energyQ)
  + lambdaP * energyP * (energyQ + neg energyK)
  + lambdaQ * energyQ * (energyK + neg energyP)

-- Fixed eigenvalues: lambdaP=1 < lambdaQ=2 < lambdaK=3.
-- Energy distribution (E_k,E_p,E_q)=(1,2,3) gives -5.
negativeWitness :
  imbalance 3 1 2 1 2 3 ≡ - 5
negativeWitness = solve []

-- The SAME eigenvalue triple with (E_k,E_p,E_q)=(3,2,1) gives +7.
positiveWitness :
  imbalance 3 1 2 3 2 1 ≡ 7
positiveWitness = solve []

-- Equipartition remains the neutral calibration.
equipartitionWitness :
  imbalance 3 1 2 2 2 2 ≡ 0
 equipartitionWitness = solve []

round95SelfImbalanceSignDeterminedByHelicityOrdering : Bool
round95SelfImbalanceSignDeterminedByHelicityOrdering = false

round95SelfImbalanceHasBothSignsAtFixedEigenvalues : Bool
round95SelfImbalanceHasBothSignsAtFixedEigenvalues = true

round95SelfImbalanceSignDeterminedByHelicityOrderingIsFalse :
  round95SelfImbalanceSignDeterminedByHelicityOrdering ≡ false
round95SelfImbalanceSignDeterminedByHelicityOrderingIsFalse = refl

round95SelfImbalanceHasBothSignsAtFixedEigenvaluesIsTrue :
  round95SelfImbalanceHasBothSignsAtFixedEigenvalues ≡ true
round95SelfImbalanceHasBothSignsAtFixedEigenvaluesIsTrue = refl
