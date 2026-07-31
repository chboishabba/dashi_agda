module DASHI.Physics.YangMills.BalabanClayGate4HRBetaLocalToUniformExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Local-to-uniform reduction for the H-R_beta remainder.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The hard physical theorem is local: after determinant/interaction/chart/
-- gauge/localization contributions are assigned to cells or polymers, each
-- absolute local remainder must be absorbed by its local half-increment.  The
-- finite algebra below proves that this implies the volume-uniform estimate
--
--   |r_k| <= Delta_k / 2
--
-- whenever the global remainder and half-increment are the corresponding
-- finite sums.  Thus volume uniformity is no longer a separate analytic input;
-- only the local decomposition, local estimates and normalization identities
-- remain physical.
------------------------------------------------------------------------

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList function [] = []
mapList function (value ∷ values) =
  function value ∷ mapList function values

record OrderedAbsoluteAdditiveAlgebra (Scalar : Set) : Set₁ where
  field
    zero : Scalar
    add : Scalar → Scalar → Scalar
    absolute : Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (add left right) (add lower upper)

    absoluteZero : absolute zero ≡ zero
    absoluteTriangle : ∀ left right →
      LessEqual
        (absolute (add left right))
        (add (absolute left) (absolute right))

open OrderedAbsoluteAdditiveAlgebra public

finiteSum :
  ∀ {Scalar} → OrderedAbsoluteAdditiveAlgebra Scalar →
  List Scalar → Scalar
finiteSum algebra [] = zero algebra
finiteSum algebra (value ∷ values) =
  add algebra value (finiteSum algebra values)

finiteSumPointwiseMonotone :
  ∀ {A Scalar}
    (algebra : OrderedAbsoluteAdditiveAlgebra Scalar)
    (left right : A → Scalar) (values : List A) →
  (∀ value → LessEqual algebra (left value) (right value)) →
  LessEqual algebra
    (finiteSum algebra (mapList left values))
    (finiteSum algebra (mapList right values))
finiteSumPointwiseMonotone algebra left right [] pointwise =
  reflexive algebra (zero algebra)
finiteSumPointwiseMonotone algebra left right (value ∷ values) pointwise =
  addMonotone algebra
    (pointwise value)
    (finiteSumPointwiseMonotone algebra left right values pointwise)

absoluteFiniteSumBelowSumAbsolute :
  ∀ {Scalar}
    (algebra : OrderedAbsoluteAdditiveAlgebra Scalar)
    (values : List Scalar) →
  LessEqual algebra
    (absolute algebra (finiteSum algebra values))
    (finiteSum algebra (mapList (absolute algebra) values))
absoluteFiniteSumBelowSumAbsolute algebra [] =
  subst
    (λ lower → LessEqual algebra lower (zero algebra))
    (sym (absoluteZero algebra))
    (reflexive algebra (zero algebra))
absoluteFiniteSumBelowSumAbsolute algebra (value ∷ values) =
  transitive algebra
    (absoluteTriangle algebra value (finiteSum algebra values))
    (addMonotone algebra
      (reflexive algebra (absolute algebra value))
      (absoluteFiniteSumBelowSumAbsolute algebra values))

record LocalHRBetaAbsorption
    (Cell Scalar : Set) : Set₁ where
  field
    algebra : OrderedAbsoluteAdditiveAlgebra Scalar
    cells : List Cell

    localRemainder localHalfIncrement : Cell → Scalar
    totalRemainder totalHalfIncrement : Scalar

    totalRemainderMeaning :
      totalRemainder
      ≡ finiteSum algebra (mapList localRemainder cells)

    totalHalfIncrementMeaning :
      totalHalfIncrement
      ≡ finiteSum algebra (mapList localHalfIncrement cells)

    localAbsorption : ∀ cell →
      LessEqual algebra
        (absolute algebra (localRemainder cell))
        (localHalfIncrement cell)

open LocalHRBetaAbsorption public

uniformHalfRemainderFromLocalAbsorption :
  ∀ {Cell Scalar}
    (dataSet : LocalHRBetaAbsorption Cell Scalar) →
  LessEqual (algebra dataSet)
    (absolute (algebra dataSet) (totalRemainder dataSet))
    (totalHalfIncrement dataSet)
uniformHalfRemainderFromLocalAbsorption dataSet =
  subst
    (λ upper →
      LessEqual (algebra dataSet)
        (absolute (algebra dataSet) (totalRemainder dataSet)) upper)
    (sym (totalHalfIncrementMeaning dataSet))
    (subst
      (λ selectedRemainder →
        LessEqual (algebra dataSet)
          (absolute (algebra dataSet) selectedRemainder)
          (finiteSum (algebra dataSet)
            (mapList (localHalfIncrement dataSet) (cells dataSet))))
      (sym (totalRemainderMeaning dataSet))
      (transitive (algebra dataSet)
        (absoluteFiniteSumBelowSumAbsolute
          (algebra dataSet)
          (mapList (localRemainder dataSet) (cells dataSet)))
        (finiteSumPointwiseMonotone
          (algebra dataSet)
          (λ cell → absolute (algebra dataSet)
            (localRemainder dataSet cell))
          (localHalfIncrement dataSet)
          (cells dataSet)
          (localAbsorption dataSet))))

record PhysicalHRBetaNormalization
    (Cell Scalar : Set) : Set₁ where
  field
    local : LocalHRBetaAbsorption Cell Scalar
    Delta : Scalar
    halfDelta : Scalar
    halfDeltaMeaning : halfDelta ≡ totalHalfIncrement local
    PhysicalHalf : Scalar → Scalar
    physicalHalfMeaning : PhysicalHalf Delta ≡ halfDelta

open PhysicalHRBetaNormalization public

physicalUniformHRBetaRemainder :
  ∀ {Cell Scalar}
    (dataSet : PhysicalHRBetaNormalization Cell Scalar) →
  LessEqual (algebra (local dataSet))
    (absolute (algebra (local dataSet))
      (totalRemainder (local dataSet)))
    (PhysicalHalf dataSet (Delta dataSet))
physicalUniformHRBetaRemainder dataSet =
  subst
    (λ upper →
      LessEqual (algebra (local dataSet))
        (absolute (algebra (local dataSet))
          (totalRemainder (local dataSet))) upper)
    (sym (physicalHalfMeaning dataSet))
    (subst
      (λ upper →
        LessEqual (algebra (local dataSet))
          (absolute (algebra (local dataSet))
            (totalRemainder (local dataSet))) upper)
      (sym (halfDeltaMeaning dataSet))
      (uniformHalfRemainderFromLocalAbsorption (local dataSet)))

hrBetaFiniteAbsoluteTriangleLevel : ProofLevel
hrBetaFiniteAbsoluteTriangleLevel = machineChecked

hrBetaLocalToUniformAbsorptionLevel : ProofLevel
hrBetaLocalToUniformAbsorptionLevel = machineChecked

hrBetaPhysicalHalfNormalizationAssemblyLevel : ProofLevel
hrBetaPhysicalHalfNormalizationAssemblyLevel = machineChecked

physicalHRBetaLocalDecompositionInputsLevel : ProofLevel
physicalHRBetaLocalDecompositionInputsLevel = conditional

physicalHRBetaLocalAbsoluteEstimatesInputsLevel : ProofLevel
physicalHRBetaLocalAbsoluteEstimatesInputsLevel = conditional
