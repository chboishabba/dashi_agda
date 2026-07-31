module DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicCellWeightExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact scalar normalization for the one-step four-dimensional dyadic block.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The geometric sibling module proves that one coarse four-cell contains
-- sixteen fine four-cells.  Here that exact integer relation is transported to
-- any commutative scalar algebra.  In particular,
--
--   q = 16 p
--
-- implies the weighted-adjoint coefficient p^{-1} q is exactly 16, while the
-- CMP109 block-average coefficient is the multiplicative inverse of 16.
------------------------------------------------------------------------

record CommutativeScalarAlgebra (Scalar : Set) : Set₁ where
  field
    zero one : Scalar
    add multiply : Scalar → Scalar → Scalar

    multiplyAssociative : ∀ left middle right →
      multiply (multiply left middle) right
      ≡ multiply left (multiply middle right)

    multiplyCommutative : ∀ left right →
      multiply left right ≡ multiply right left

    multiplyIdentityLeft : ∀ value → multiply one value ≡ value
    multiplyIdentityRight : ∀ value → multiply value one ≡ value

open CommutativeScalarAlgebra public

doubleScalar :
  ∀ {Scalar} → CommutativeScalarAlgebra Scalar → Scalar → Scalar
doubleScalar algebra value = add algebra value value

twoScalar :
  ∀ {Scalar} → CommutativeScalarAlgebra Scalar → Scalar
twoScalar algebra = doubleScalar algebra (one algebra)

fourScalar :
  ∀ {Scalar} → CommutativeScalarAlgebra Scalar → Scalar
fourScalar algebra = doubleScalar algebra (twoScalar algebra)

eightScalar :
  ∀ {Scalar} → CommutativeScalarAlgebra Scalar → Scalar
eightScalar algebra = doubleScalar algebra (fourScalar algebra)

sixteenScalar :
  ∀ {Scalar} → CommutativeScalarAlgebra Scalar → Scalar
sixteenScalar algebra = doubleScalar algebra (eightScalar algebra)

record CMP109DyadicCellWeights (Scalar : Set) : Set₁ where
  field
    algebra : CommutativeScalarAlgebra Scalar

    fineCellWeight coarseCellWeight : Scalar
    inverseFineCellWeight : Scalar
    blockAverageWeight : Scalar

    fineInverseExact :
      multiply algebra inverseFineCellWeight fineCellWeight
      ≡ one algebra

    coarseIsSixteenFine :
      coarseCellWeight
      ≡ multiply algebra (sixteenScalar algebra) fineCellWeight

    blockAverageIsInverseSixteen :
      multiply algebra blockAverageWeight (sixteenScalar algebra)
      ≡ one algebra

open CMP109DyadicCellWeights public

weightedAdjointFineInverseTimesCoarse :
  ∀ {Scalar}
    (weights : CMP109DyadicCellWeights Scalar) →
  multiply (algebra weights)
    (inverseFineCellWeight weights)
    (coarseCellWeight weights)
  ≡ sixteenScalar (algebra weights)
weightedAdjointFineInverseTimesCoarse weights =
  trans
    (cong
      (multiply (algebra weights) (inverseFineCellWeight weights))
      (coarseIsSixteenFine weights))
    (trans
      (sym
        (multiplyAssociative (algebra weights)
          (inverseFineCellWeight weights)
          (sixteenScalar (algebra weights))
          (fineCellWeight weights)))
      (trans
        (cong
          (λ firstProduct →
            multiply (algebra weights)
              firstProduct (fineCellWeight weights))
          (multiplyCommutative (algebra weights)
            (inverseFineCellWeight weights)
            (sixteenScalar (algebra weights))))
        (trans
          (multiplyAssociative (algebra weights)
            (sixteenScalar (algebra weights))
            (inverseFineCellWeight weights)
            (fineCellWeight weights))
          (trans
            (cong
              (multiply (algebra weights)
                (sixteenScalar (algebra weights)))
              (fineInverseExact weights))
            (multiplyIdentityRight (algebra weights)
              (sixteenScalar (algebra weights)))))))

blockAverageCancelsDyadicVolume :
  ∀ {Scalar}
    (weights : CMP109DyadicCellWeights Scalar) →
  multiply (algebra weights)
    (blockAverageWeight weights)
    (sixteenScalar (algebra weights))
  ≡ one (algebra weights)
blockAverageCancelsDyadicVolume = blockAverageIsInverseSixteen

cmp109DyadicCellWeightScalingLevel : ProofLevel
cmp109DyadicCellWeightScalingLevel = machineChecked

cmp109DyadicWeightedAdjointRatioLevel : ProofLevel
cmp109DyadicWeightedAdjointRatioLevel = machineChecked

cmp109DyadicBlockAverageCancellationLevel : ProofLevel
cmp109DyadicBlockAverageCancellationLevel = machineChecked

physicalScalarCellWeightInstantiationInputsLevel : ProofLevel
physicalScalarCellWeightInstantiationInputsLevel = conditional
