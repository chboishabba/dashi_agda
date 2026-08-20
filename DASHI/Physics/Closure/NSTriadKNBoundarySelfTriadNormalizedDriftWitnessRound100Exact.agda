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
-- This file gives exact rational witnesses inside the already-proved Round95
-- Waleffe/Manley--Rowe algebra.  Even after setting self amplitude forcing and
-- every external forcing to zero, unequal modal energies leave the normalized
-- self drift nonzero.  Two choices of the lambda ordering give opposite signs.
-- Hence the final packet-boundary theorem must retain the self-triad boundary
-- sector, and no universal pointwise sign can be assigned to it from the
-- three-leg energy identities alone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)
open ℚP using (_<?_)

import DASHI.Physics.Closure.NSTriadKNNormalizedWaleffePhaseDerivativeRound95Exact as Phase

one two three : ℚ
one = 1ℚ
two = Int.+ 2 / 1
three = Int.+ 3 / 1

mkSelfTangent : ℚ → ℚ → ℚ → Phase.NormalizedPhaseTangentData
mkSelfTangent lambdaK lambdaP lambdaQ =
  let
    tk = (lambdaQ + (- lambdaP)) * one
    tp = (lambdaK + (- lambdaQ)) * one
    tq = (lambdaP + (- lambdaK)) * one
  in
  Phase.normalized-phase-tangent-data
    one 0ℚ
    one two three
    tk tp tq
    0ℚ 0ℚ 0ℚ
    0ℚ 0ℚ
    tk tp tq
    0ℚ 0ℚ 0ℚ
    (solve (lambdaK ∷ lambdaP ∷ lambdaQ ∷ []))
    (solve (lambdaK ∷ lambdaP ∷ lambdaQ ∷ []))
    (solve (lambdaK ∷ lambdaP ∷ lambdaQ ∷ []))
    (solve (lambdaK ∷ lambdaP ∷ lambdaQ ∷ []))

mkSelfTransferData :
  (lambdaK lambdaP lambdaQ : ℚ) → Phase.WaleffeSelfTransferData
mkSelfTransferData lambdaK lambdaP lambdaQ =
  Phase.waleffe-self-transfer-data
    (mkSelfTangent lambdaK lambdaP lambdaQ)
    lambdaK lambdaP lambdaQ
    (solve []) (solve []) (solve [])

negativeData : Phase.NormalizedPhaseTangentData
negativeData = mkSelfTangent one two three

positiveData : Phase.NormalizedPhaseTangentData
positiveData = mkSelfTangent three two one

minusTwo : ℚ
minusTwo = - two

negativeSelfNormalizedDriftIsMinusTwo :
  Phase.selfNormalizedDrift negativeData ≡ minusTwo
negativeSelfNormalizedDriftIsMinusTwo = solve []

positiveSelfNormalizedDriftIsTwo :
  Phase.selfNormalizedDrift positiveData ≡ two
positiveSelfNormalizedDriftIsTwo = solve []

minusTwoNegative : minusTwo < 0ℚ
minusTwoNegative = toWitness {a? = minusTwo <? 0ℚ} _

zeroBelowTwo : 0ℚ < two
zeroBelowTwo = toWitness {a? = 0ℚ <? two} _

negativeSelfNormalizedDriftStrictlyNegative :
  Phase.selfNormalizedDrift negativeData < 0ℚ
negativeSelfNormalizedDriftStrictlyNegative
  rewrite negativeSelfNormalizedDriftIsMinusTwo = minusTwoNegative

positiveSelfNormalizedDriftStrictlyPositive :
  0ℚ < Phase.selfNormalizedDrift positiveData
positiveSelfNormalizedDriftStrictlyPositive
  rewrite positiveSelfNormalizedDriftIsTwo = zeroBelowTwo

round100ThreeLegEnergyCancellationDoesNotEraseBoundarySelfDrift : Bool
round100ThreeLegEnergyCancellationDoesNotEraseBoundarySelfDrift = true

round100BoundarySelfDriftHasBothSignsInExactTransferAlgebra : Bool
round100BoundarySelfDriftHasBothSignsInExactTransferAlgebra = true

round100UniversalPointwiseSelfSectorSignAvailable : Bool
round100UniversalPointwiseSelfSectorSignAvailable = false

round100ThreeLegEnergyCancellationDoesNotEraseBoundarySelfDriftIsTrue :
  round100ThreeLegEnergyCancellationDoesNotEraseBoundarySelfDrift ≡ true
round100ThreeLegEnergyCancellationDoesNotEraseBoundarySelfDriftIsTrue = refl

round100UniversalPointwiseSelfSectorSignAvailableIsFalse :
  round100UniversalPointwiseSelfSectorSignAvailable ≡ false
round100UniversalPointwiseSelfSectorSignAvailableIsFalse = refl
