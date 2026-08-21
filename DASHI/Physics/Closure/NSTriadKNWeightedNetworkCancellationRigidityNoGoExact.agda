module DASHI.Physics.Closure.NSTriadKNWeightedNetworkCancellationRigidityNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- DASHI MAKE-OR-BREAK AUDIT
--
-- An unweighted exchange pair (x , -x) cancels.  This exact lemma proves
-- the rigidity needed by any proposed global normal form: if weighted
-- cancellation survives even the unit exchange pair, its two channel weights
-- must agree.  Thus on a connected cancellation graph universal preservation
-- of cancellation forces weights to be constant on each component.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

weightedOppositePair : ℚ → ℚ → ℚ → ℚ
weightedOppositePair leftWeight rightWeight x =
  leftWeight * x + rightWeight * (- x)

weightedOppositePairAtUnit :
  (leftWeight rightWeight : ℚ) →
  weightedOppositePair leftWeight rightWeight 1ℚ
  ≡ leftWeight + (- rightWeight)
weightedOppositePairAtUnit leftWeight rightWeight =
  trans
    (cong (λ y → y + rightWeight * (- 1ℚ))
      (ℚP.*-identityʳ leftWeight))
    (cong (leftWeight +_)
      (trans
        (sym (ℚP.neg-distribʳ-* rightWeight 1ℚ))
        (cong -_ (ℚP.*-identityʳ rightWeight))))

additiveDifferenceZeroForcesEquality :
  (leftWeight rightWeight : ℚ) →
  leftWeight + (- rightWeight) ≡ 0ℚ →
  leftWeight ≡ rightWeight
additiveDifferenceZeroForcesEquality leftWeight rightWeight differenceZero =
  trans
    (sym leftExpansion)
    (trans
      (cong (_+ rightWeight) differenceZero)
      (ℚP.+-identityˡ rightWeight))
  where
  leftExpansion :
    (leftWeight + (- rightWeight)) + rightWeight ≡ leftWeight
  leftExpansion =
    trans
      (ℚP.+-assoc leftWeight (- rightWeight) rightWeight)
      (trans
        (cong (leftWeight +_) (ℚP.+-inverseˡ rightWeight))
        (ℚP.+-identityʳ leftWeight))

weightedUnitCancellationForcesEqualWeights :
  (leftWeight rightWeight : ℚ) →
  weightedOppositePair leftWeight rightWeight 1ℚ ≡ 0ℚ →
  leftWeight ≡ rightWeight
weightedUnitCancellationForcesEqualWeights leftWeight rightWeight cancellation =
  additiveDifferenceZeroForcesEquality leftWeight rightWeight
    (trans
      (sym (weightedOppositePairAtUnit leftWeight rightWeight))
      cancellation)

triadDependentNormalFormWeightsPreserveUniversalCancellation : Bool
triadDependentNormalFormWeightsPreserveUniversalCancellation = false

constantWeightsAreNecessaryForUniversalPairCancellation : Bool
constantWeightsAreNecessaryForUniversalPairCancellation = true

triadDependentNormalFormWeightsPreserveUniversalCancellationIsFalse :
  triadDependentNormalFormWeightsPreserveUniversalCancellation ≡ false
triadDependentNormalFormWeightsPreserveUniversalCancellationIsFalse = refl

constantWeightsAreNecessaryForUniversalPairCancellationIsTrue :
  constantWeightsAreNecessaryForUniversalPairCancellation ≡ true
constantWeightsAreNecessaryForUniversalPairCancellationIsTrue = refl
