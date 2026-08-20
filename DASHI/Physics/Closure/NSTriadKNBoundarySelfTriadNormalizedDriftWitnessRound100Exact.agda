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
-- self drift nonzero.  The two spectral triples
--
--     (1,2,5/2) and (5/2,2,1)
--
-- both satisfy the strict triangle inequalities, while producing opposite
-- signs for the normalized self drift.  Thus the sign obstruction is not an
-- artefact of the earlier degenerate (1,2,3) calibration.
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

one two three fiveHalves : ℚ
one = 1ℚ
two = Int.+ 2 / 1
three = Int.+ 3 / 1
fiveHalves = Int.+ 5 / 2

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

negativeData positiveData : Phase.NormalizedPhaseTangentData
negativeData = mkSelfTangent one two fiveHalves
positiveData = mkSelfTangent fiveHalves two one

minusHalf fiveHalvesPositive : ℚ
minusHalf = - (Int.+ 1 / 2)
fiveHalvesPositive = fiveHalves

negativeSelfNormalizedDriftIsMinusHalf :
  Phase.selfNormalizedDrift negativeData ≡ minusHalf
negativeSelfNormalizedDriftIsMinusHalf = solve []

positiveSelfNormalizedDriftIsFiveHalves :
  Phase.selfNormalizedDrift positiveData ≡ fiveHalvesPositive
positiveSelfNormalizedDriftIsFiveHalves = solve []

minusHalfNegative : minusHalf < 0ℚ
minusHalfNegative = toWitness {a? = minusHalf <? 0ℚ} _

zeroBelowFiveHalves : 0ℚ < fiveHalvesPositive
zeroBelowFiveHalves = toWitness {a? = 0ℚ <? fiveHalvesPositive} _

negativeSelfNormalizedDriftStrictlyNegative :
  Phase.selfNormalizedDrift negativeData < 0ℚ
negativeSelfNormalizedDriftStrictlyNegative
  rewrite negativeSelfNormalizedDriftIsMinusHalf = minusHalfNegative

positiveSelfNormalizedDriftStrictlyPositive :
  0ℚ < Phase.selfNormalizedDrift positiveData
positiveSelfNormalizedDriftStrictlyPositive
  rewrite positiveSelfNormalizedDriftIsFiveHalves = zeroBelowFiveHalves

triangle125 : one < two + fiveHalves
triangle125 = toWitness {a? = one <? (two + fiveHalves)} _
triangle215 : two < one + fiveHalves
triangle215 = toWitness {a? = two <? (one + fiveHalves)} _
triangle521 : fiveHalves < one + two
triangle521 = toWitness {a? = fiveHalves <? (one + two)} _

round100SelfDriftOppositeSignsSurviveStrictTriangleGeometry : Bool
round100SelfDriftOppositeSignsSurviveStrictTriangleGeometry = true

round100ThreeLegEnergyCancellationDoesNotEraseBoundarySelfDrift : Bool
round100ThreeLegEnergyCancellationDoesNotEraseBoundarySelfDrift = true

round100UniversalPointwiseSelfSectorSignAvailable : Bool
round100UniversalPointwiseSelfSectorSignAvailable = false

round100SelfDriftOppositeSignsSurviveStrictTriangleGeometryIsTrue :
  round100SelfDriftOppositeSignsSurviveStrictTriangleGeometry ≡ true
round100SelfDriftOppositeSignsSurviveStrictTriangleGeometryIsTrue = refl

round100UniversalPointwiseSelfSectorSignAvailableIsFalse :
  round100UniversalPointwiseSelfSectorSignAvailable ≡ false
round100UniversalPointwiseSelfSectorSignAvailableIsFalse = refl
