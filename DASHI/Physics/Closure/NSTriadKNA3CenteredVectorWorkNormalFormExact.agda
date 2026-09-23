{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNA3CenteredVectorWorkNormalFormExact where

------------------------------------------------------------------------
-- A3 / CENTERED VECTOR-WORK NORMAL FORM
--
-- The live A3 scalar is currently presented as an unordered pair sum
--
--   sum_{alpha<beta}
--     (r_alpha-r_beta) W(M, A_alpha-A_beta).
--
-- Existing owners already prove:
--
--   * scalar pair-difference centering (D1b2);
--   * W(M,A_alpha)-W(M,A_beta) = W(M,A_alpha-A_beta);
--   * finite work sums collapse against the vector fold.
--
-- Compose those exact theorems to remove the quadratic pair enumeration:
--
--   PairVectorWork
--     = n * sum_alpha r_alpha W(M,A_alpha)
--       - (sum_alpha r_alpha) W(M, sum_alpha A_alpha).
--
-- On the literal fixed-output family M = sum_alpha A_alpha:
--
--   PairVectorWork
--     = n * sum_alpha r_alpha W(M,A_alpha)
--       - (sum_alpha r_alpha) W(M,M).
--
-- Thus the signed A3 payment is exactly one division-free centered covariance
-- numerator.  No inequality, absolute value, Cauchy estimate, incidence
-- separation, Pluecker input, or cutoff factor is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; _-_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentWorkDifferenceVectorBridgeExact as Vector

F = Pair.F

pairDifferenceVectorWorkClosedForm :
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (mixed : C3.Complex3 F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  Vector.pairDifferenceVectorWorkSum rate mixed value items
  ≡
  Pair.natAsRational (length items)
    * Pair.weightedWorkSum rate (Pair.cellWork mixed value) items
    - Pair.rateSum rate items
      * Work.coherentWork mixed (R224.foldVector value items)
pairDifferenceVectorWorkClosedForm rate mixed value items =
  trans
    (sym
      (Vector.pairDifferenceWorkSumIsVectorDifferenceWorkSum
        rate mixed value items))
    (trans
      (Pair.pairDifferenceClosedForm
        rate (Pair.cellWork mixed value) items)
      (cong
        (λ workTotal →
          Pair.natAsRational (length items)
            * Pair.weightedWorkSum rate (Pair.cellWork mixed value) items
            - Pair.rateSum rate items * workTotal)
        (Pair.workSumAgainstFold mixed value items)))

fixedOutputA3CenteredNormalForm :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (rho : Z3.FourierMode → ℚ) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    rate = Pair.cellRate rho
  in
  Vector.pairDifferenceVectorWorkSum rate mixed value items
  ≡
  Pair.natAsRational (length items)
    * Pair.weightedWorkSum rate (Pair.cellWork mixed value) items
    - Pair.rateSum rate items * Work.coherentWork mixed mixed
fixedOutputA3CenteredNormalForm rho S velocity cutoff output =
  pairDifferenceVectorWorkClosedForm
    (Pair.cellRate rho)
    (R224.foldVector
      (D1a.mixedProductCell S velocity)
      (Output.physicalOutputFiber cutoff output))
    (D1a.mixedProductCell S velocity)
    (Output.physicalOutputFiber cutoff output)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

a3PairEnumerationCollapsedToCenteredNormalForm : Bool
a3PairEnumerationCollapsedToCenteredNormalForm = true

a3CenteredNormalFormUsesCompleteFibreFold : Bool
a3CenteredNormalFormUsesCompleteFibreFold = true

a3CenteredNormalFormIntroducesQuantitativeEstimate : Bool
a3CenteredNormalFormIntroducesQuantitativeEstimate = false

a3CenteredNormalFormUsesPointwiseIncidenceSeparation : Bool
a3CenteredNormalFormUsesPointwiseIncidenceSeparation = false

a3PairEnumerationCollapsedToCenteredNormalFormIsTrue :
  a3PairEnumerationCollapsedToCenteredNormalForm ≡ true
a3PairEnumerationCollapsedToCenteredNormalFormIsTrue = refl

a3CenteredNormalFormUsesCompleteFibreFoldIsTrue :
  a3CenteredNormalFormUsesCompleteFibreFold ≡ true
a3CenteredNormalFormUsesCompleteFibreFoldIsTrue = refl

a3CenteredNormalFormIntroducesQuantitativeEstimateIsFalse :
  a3CenteredNormalFormIntroducesQuantitativeEstimate ≡ false
a3CenteredNormalFormIntroducesQuantitativeEstimateIsFalse = refl

a3CenteredNormalFormUsesPointwiseIncidenceSeparationIsFalse :
  a3CenteredNormalFormUsesPointwiseIncidenceSeparation ≡ false
a3CenteredNormalFormUsesPointwiseIncidenceSeparationIsFalse = refl
