module DASHI.Physics.Closure.NSTriadKNBoundarySelfTriadNormalizedDriftWitnessRound100Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: J. M. Manley; H. E. Rowe.
-- Title: "Some General Properties of Nonlinear Elements-Part I. General
-- Energy Relations".
-- Proceedings of the IRE 44(7) (1956), 904--913.
-- DOI: 10.1109/JRPROC.1956.275145.
--
-- ROUND100 / CHEAP FALSIFIER FOR THE "EXTERNAL NETWORK ONLY" SHORTCUT
--
-- Exact three-leg energy cancellation says an isolated triad cannot change
-- the SUM of the energies of its three legs.  It does NOT say that the
-- transfer through a packet boundary, or a normalized triad observable, is
-- stationary under the isolated-triad dynamics.
--
-- This file gives an exact rational witness inside the already-proved Round95
-- Waleffe/Manley--Rowe algebra.  Even after setting the self amplitude forcing
-- itself to zero, unequal modal energies leave the denominator-normalization
-- term nonzero.  Hence the final packet-boundary variation theorem must retain
-- a self-triad boundary sector as well as the external-network sector.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _<_; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)
open ℚP using (_<?_)

import DASHI.Physics.Closure.NSTriadKNNormalizedWaleffePhaseDerivativeRound95Exact as Phase

one two three : ℚ
one = 1ℚ
two = Int.+ 2 / 1
three = Int.+ 3 / 1

selfTK selfTP selfTQ : ℚ
selfTK = (three + (- two)) * one
selfTP = (one + (- three)) * one
selfTQ = (two + (- one)) * one

witnessTangentData : Phase.NormalizedPhaseTangentData
witnessTangentData = Phase.normalized-phase-tangent-data
  one                    -- amplitude
  0ℚ                     -- amplitude tangent
  one two three          -- E_k,E_p,E_q
  selfTK selfTP selfTQ   -- energy tangents
  0ℚ 0ℚ 0ℚ              -- rho_k,rho_p,rho_q
  0ℚ 0ℚ                  -- self/external amplitude forcing
  selfTK selfTP selfTQ   -- self transfers
  0ℚ 0ℚ 0ℚ              -- external transfers
  (solve [])
  (solve [])
  (solve [])
  (solve [])

witnessSelfTransferData : Phase.WaleffeSelfTransferData
witnessSelfTransferData = Phase.waleffe-self-transfer-data
  witnessTangentData
  one two three
  (solve [])
  (solve [])
  (solve [])

minusTwo : ℚ
minusTwo = - two

witnessEnergyImbalanceIsMinusTwo :
  Phase.energyImbalancePolynomial witnessSelfTransferData ≡ minusTwo
witnessEnergyImbalanceIsMinusTwo = solve []

witnessSelfNormalizedDriftIsMinusTwo :
  Phase.selfNormalizedDrift witnessTangentData ≡ minusTwo
witnessSelfNormalizedDriftIsMinusTwo =
  let
    exact = Phase.waleffeSelfNormalizedDriftExact witnessSelfTransferData
  in
  solve []

minusTwoNegative : minusTwo < 0ℚ
minusTwoNegative = toWitness {a? = minusTwo <? 0ℚ} _

witnessSelfNormalizedDriftStrictlyNegative :
  Phase.selfNormalizedDrift witnessTangentData < 0ℚ
witnessSelfNormalizedDriftStrictlyNegative
  rewrite witnessSelfNormalizedDriftIsMinusTwo = minusTwoNegative

round100ThreeLegEnergyCancellationDoesNotEraseBoundarySelfDrift : Bool
round100ThreeLegEnergyCancellationDoesNotEraseBoundarySelfDrift = true

round100BoundarySelfTriadSectorMustRemainInFinalEstimate : Bool
round100BoundarySelfTriadSectorMustRemainInFinalEstimate = true

round100ThreeLegEnergyCancellationDoesNotEraseBoundarySelfDriftIsTrue :
  round100ThreeLegEnergyCancellationDoesNotEraseBoundarySelfDrift ≡ true
round100ThreeLegEnergyCancellationDoesNotEraseBoundarySelfDriftIsTrue = refl
