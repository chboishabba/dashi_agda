{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedR230WeightRound798Exact where

------------------------------------------------------------------------
-- ROUND798 / THE FULLY-SEPARATED MASK IS A LITERAL R294 PHYSICAL WEIGHT
--
-- R781 proves ccTouched is invariant under physical p/q swap.  Therefore the
-- indicator of the complementary fully-separated family is a valid
-- SwapInvariantCellWeight in the exact R294 sense:
--
--   chi_sep(beta) = 1  if ccTouched beta = false
--                 = 0  if ccTouched beta = true.
--
-- R294 may therefore be specialized directly:
--
--   fold chi_sep * ProductRule
--     = fold chi_sep * Commutator
--
-- on every complete fixed-output fibre.
--
-- This is the SI-style physical-identification move: attach the exact physical
-- mask BEFORE the finite reindexing, then preserve it through the same-object
-- vector identity.  No estimate or absolute value is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781

separatedWeight :
  ∀ {r} (F : C3.RealField r) →
  R294.SwapInvariantCellWeight F
separatedWeight F = record
  { R294.weight = weight
  ; R294.swapInvariant = invariant
  }
  where
  weight : Physical.PhysicalTriadIncidence → C3.Complex F
  weight beta with R781.ccTouched beta
  ... | true = C3.complexZero F
  ... | false = C3.complexOne F

  invariant :
    (beta : Physical.PhysicalTriadIncidence) →
    weight (Symmetry.swapTriad beta)
    ≡ weight beta
  invariant beta
    rewrite R781.ccTouchedSwapInvariant beta =
    refl

fixedOutputSeparatedProductRuleIsCommutator :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat) (output : Z3.FourierMode) →
  R224.foldVector
    (R294.weightedProductRuleCell
      (separatedWeight F) S velocity forcing)
    (Output.physicalOutputFiber
      cutoff output)
  ≡
  R224.foldVector
    (R294.weightedCommutatorCell
      (separatedWeight F) S velocity forcing)
    (Output.physicalOutputFiber
      cutoff output)
fixedOutputSeparatedProductRuleIsCommutator
    {F = F} S velocity forcing cutoff output =
  R294.fixedOutputWeightedProductRuleIsCommutator
    (separatedWeight F) S velocity forcing cutoff output

round798SeparatedMaskIsR294SwapInvariantWeight : Bool
round798SeparatedMaskIsR294SwapInvariantWeight = true

round798SeparatedProductRuleToCommutatorClosed : Bool
round798SeparatedProductRuleToCommutatorClosed = true

round798IntroducesEstimate : Bool
round798IntroducesEstimate = false

round798W2Closed : Bool
round798W2Closed = false

round798ClayPromotion : Bool
round798ClayPromotion = false

round798SeparatedMaskIsR294SwapInvariantWeightIsTrue :
  round798SeparatedMaskIsR294SwapInvariantWeight ≡ true
round798SeparatedMaskIsR294SwapInvariantWeightIsTrue = refl

round798SeparatedProductRuleToCommutatorClosedIsTrue :
  round798SeparatedProductRuleToCommutatorClosed ≡ true
round798SeparatedProductRuleToCommutatorClosedIsTrue = refl

round798IntroducesEstimateIsFalse :
  round798IntroducesEstimate ≡ false
round798IntroducesEstimateIsFalse = refl

round798W2ClosedIsFalse :
  round798W2Closed ≡ false
round798W2ClosedIsFalse = refl

round798ClayPromotionIsFalse :
  round798ClayPromotion ≡ false
round798ClayPromotionIsFalse = refl
