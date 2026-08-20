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
-- I=lambda_k E_k(E_p-E_q)+lambda_p E_p(E_q-E_k)+lambda_q E_q(E_k-E_p).
-- One fixed ordered eigenvalue triple admits both signs as the energy
-- distribution changes, so helicity/eigenvalue ordering alone cannot supply a
-- universal favorable-sign theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Data.Rational.Base using (ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

neg : ℚ → ℚ
neg x = - x

imbalance : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
imbalance lambdaK lambdaP lambdaQ energyK energyP energyQ =
    lambdaK * energyK * (energyP + neg energyQ)
  + lambdaP * energyP * (energyQ + neg energyK)
  + lambdaQ * energyQ * (energyK + neg energyP)

negativeWitness : imbalance 3 1 2 1 2 3 ≡ - 5
negativeWitness = solve []

positiveWitness : imbalance 3 1 2 3 2 1 ≡ 7
positiveWitness = solve []

equipartitionWitness : imbalance 3 1 2 2 2 2 ≡ 0
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
