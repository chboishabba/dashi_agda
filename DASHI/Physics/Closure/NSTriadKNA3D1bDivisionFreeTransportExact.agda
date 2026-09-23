module DASHI.Physics.Closure.NSTriadKNA3D1bDivisionFreeTransportExact where

------------------------------------------------------------------------
-- A3 / d1b0 EXACT DIVISION-FREE TRANSPORT
--
-- The fixed-output d1b0 identity and the division-free covariance-centering
-- identity do not identify the commutator work with the A3 pair-difference
-- scalar at unit coefficient.
--
-- Let
--
--   M = sum_i A_i
--   D = variable viscous-decay fold
--   T = damped tangent fold
--   C = commutator fold
--   r_i = physical/two-leg cell rate
--   w_i = W(M,A_i)
--   P = sum_{i<j} (r_i-r_j)(w_i-w_j).
--
-- Existing owners prove
--
--   W(M,C) = W(M,T) - W(M,D)
--
-- and
--
--   n W(M,D) + (sum_i r_i) W(M,M) = -P.
--
-- Therefore, without division by n,
--
--   n W(M,C) + (-P)
--     = n W(M,T) + (sum_i r_i) W(M,M).
--
-- This is the exact normalization/sign firewall required before attempting an
-- endpoint-aware A3 -> R406 splice.  No inequality or new NS estimate occurs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (length)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair

F : C3.RealField _
F = Rational.rationalRealField

divisionFreeD1bA3Normalization :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (rho : Z3.FourierMode → ℚ) →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    rate = Pair.cellRate rho
    work = Pair.cellWork mixed value
    tangent =
      R224.foldVector
        (D1a.dampedMixedTangentCell rho S velocity forcing) items
    commutator =
      R224.foldVector
        (R230.forcingCommutatorCell
          S velocity forcing) items
    n = Pair.natAsRational (length items)
  in
  n * Work.coherentWork mixed commutator
    + (0ℚ - Pair.pairDifferenceWorkSum rate work items)
  ≡
  n * Work.coherentWork mixed tangent
    + Pair.rateSum rate items * Work.coherentWork mixed mixed
divisionFreeD1bA3Normalization
    rho S velocity forcing cutoff output =
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    rate = Pair.cellRate rho
    work = Pair.cellWork mixed value
    decay =
      R224.foldVector (D1a.variableDecayCell rho S velocity) items
    tangent =
      R224.foldVector
        (D1a.dampedMixedTangentCell rho S velocity forcing) items
    commutator =
      R224.foldVector
        (R230.forcingCommutatorCell
          S velocity forcing) items
    n = Pair.natAsRational (length items)
    rateTotal = Pair.rateSum rate items
    self = Work.coherentWork mixed mixed
    decayWork = Work.coherentWork mixed decay
    tangentWork = Work.coherentWork mixed tangent
    commutatorWork = Work.coherentWork mixed commutator
    pairDiff = Pair.pairDifferenceWorkSum rate work items

    commutatorMeaning :
      commutatorWork ≡ tangentWork - decayWork
    commutatorMeaning =
      Work.fixedOutputCommutatorWorkIsTangentMinusDecay
        rho S velocity forcing cutoff output

    covarianceMeaning :
      n * decayWork + rateTotal * self ≡ 0ℚ - pairDiff
    covarianceMeaning =
      Pair.fixedOutputCovariancePairDifference
        rho S velocity cutoff output

  in
  trans
    (cong
      (λ selected →
        n * selected + (0ℚ - pairDiff))
      commutatorMeaning)
    (trans
      (cong
        (λ selected →
          n * (tangentWork - decayWork) + selected)
        (sym covarianceMeaning))
      (solve
        (n ∷ tangentWork ∷ decayWork ∷ rateTotal ∷ self ∷ [])))

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

divisionFreeD1bA3NormalizationClosed : Bool
divisionFreeD1bA3NormalizationClosed = true

divisionByFibreCardinalityIntroduced : Bool
divisionByFibreCardinalityIntroduced = false

meanRateSelfWorkTermPresent : Bool
meanRateSelfWorkTermPresent = true

naiveUnitCoefficientCommutatorEqualsA3 : Bool
naiveUnitCoefficientCommutatorEqualsA3 = false

newNonlinearEstimateIntroduced : Bool
newNonlinearEstimateIntroduced = false

divisionFreeD1bA3NormalizationClosedIsTrue :
  divisionFreeD1bA3NormalizationClosed ≡ true
divisionFreeD1bA3NormalizationClosedIsTrue = refl

divisionByFibreCardinalityIntroducedIsFalse :
  divisionByFibreCardinalityIntroduced ≡ false
divisionByFibreCardinalityIntroducedIsFalse = refl

meanRateSelfWorkTermPresentIsTrue :
  meanRateSelfWorkTermPresent ≡ true
meanRateSelfWorkTermPresentIsTrue = refl

naiveUnitCoefficientCommutatorEqualsA3IsFalse :
  naiveUnitCoefficientCommutatorEqualsA3 ≡ false
naiveUnitCoefficientCommutatorEqualsA3IsFalse = refl

newNonlinearEstimateIntroducedIsFalse :
  newNonlinearEstimateIntroduced ≡ false
newNonlinearEstimateIntroducedIsFalse = refl
