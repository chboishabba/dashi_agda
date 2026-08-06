module DASHI.Biology.PadicCylinderLODReasoningField where

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Geometry.SSP369Ultrametric as U369

------------------------------------------------------------------------
-- Finite-prefix p-adic reasoning field and exact level-of-detail laws.
--
-- The address is the state; the voxel is only an observation layout.  Every
-- coarsening retains an exact parent cylinder identifier while discarding the
-- finer child digit.  Mass is aggregated before class normalisation.

DepthOneAddress : Set
DepthOneAddress = U369.Address 1

DepthTwoAddress : Set
DepthTwoAddress = U369.Address 2

DepthThreeAddress : Set
DepthThreeAddress = U369.Address 3

DepthSixAddress : Set
DepthSixAddress = U369.Address 6

prefixTwoToOne : DepthTwoAddress → DepthOneAddress
prefixTwoToOne (a vcons b vcons vnil) = a vcons vnil

refineOne : DepthOneAddress → U369.Digit369 → DepthTwoAddress
refineOne (a vcons vnil) child = a vcons child vcons vnil

prefixRefinementReturnsParent :
  (a : DepthOneAddress) (child : U369.Digit369) →
  prefixTwoToOne (refineOne a child) ≡ a
prefixRefinementReturnsParent (a vcons vnil) child = refl

------------------------------------------------------------------------
-- A depth-one cylinder has three depth-two children.

record ThreeChildren (A : Set) : Set where
  constructor threeChildren
  field
    child3 : A
    child6 : A
    child9 : A

open ThreeChildren public

aggregateNat : ThreeChildren Nat → Nat
aggregateNat children =
  child3 children + child6 children + child9 children

canonicalChildMasses : ThreeChildren Nat
canonicalChildMasses = threeChildren 2 3 4

canonicalParentMassIsNine :
  aggregateNat canonicalChildMasses ≡ 9
canonicalParentMassIsNine = refl

record NodeField : Set where
  constructor nodeField
  field
    totalMass : Nat
    class3Mass : Nat
    class6Mass : Nat
    class9Mass : Nat

open NodeField public

aggregateNodeFields : ThreeChildren NodeField → NodeField
aggregateNodeFields children =
  nodeField
    (totalMass (child3 children)
      + totalMass (child6 children)
      + totalMass (child9 children))
    (class3Mass (child3 children)
      + class3Mass (child6 children)
      + class3Mass (child9 children))
    (class6Mass (child3 children)
      + class6Mass (child6 children)
      + class6Mass (child9 children))
    (class9Mass (child3 children)
      + class9Mass (child6 children)
      + class9Mass (child9 children))

canonicalChildFields : ThreeChildren NodeField
canonicalChildFields =
  threeChildren
    (nodeField 2 2 0 0)
    (nodeField 3 0 3 0)
    (nodeField 4 0 0 4)

canonicalCoarseField : NodeField
canonicalCoarseField = aggregateNodeFields canonicalChildFields

coarseTotalPreservesChildSum : totalMass canonicalCoarseField ≡ 9
coarseTotalPreservesChildSum = refl

coarseClassMassesPreserved :
  class3Mass canonicalCoarseField ≡ 2
  ×
  class6Mass canonicalCoarseField ≡ 3
  ×
  class9Mass canonicalCoarseField ≡ 4
coarseClassMassesPreserved = refl , (refl , refl)

------------------------------------------------------------------------
-- Finite conditional-average certificate.  Avoiding division keeps the law
-- constructive: parent * 3 equals the sum of the three equal-measure children.

record ThreeWayAverageCertificate : Set where
  constructor threeWayAverageCertificate
  field
    parentValue : Nat
    childValues : ThreeChildren Nat
    threeTimesParentIsChildSum :
      (3 * parentValue) ≡ aggregateNat childValues

open ThreeWayAverageCertificate public

canonicalAverageCertificate : ThreeWayAverageCertificate
canonicalAverageCertificate =
  threeWayAverageCertificate
    6
    (threeChildren 3 6 9)
    refl

------------------------------------------------------------------------
-- Morton-like depth-three and depth-six observation layouts.

digitCoordinate : U369.Digit369 → Nat
digitCoordinate U369.digit3 = 0
digitCoordinate U369.digit6 = 1
digitCoordinate U369.digit9 = 2

record Voxel3 : Set where
  constructor voxel3
  field
    voxelX : Nat
    voxelY : Nat
    voxelZ : Nat

open Voxel3 public

embedDepthThree : DepthThreeAddress → Voxel3
embedDepthThree (a vcons b vcons c vcons vnil) =
  voxel3 (digitCoordinate a) (digitCoordinate b) (digitCoordinate c)

record HierarchicalVoxel : Set where
  constructor hierarchicalVoxel
  field
    coarseVoxel : Voxel3
    fineVoxel : Voxel3

open HierarchicalVoxel public

embedDepthSix : DepthSixAddress → HierarchicalVoxel
embedDepthSix
  (a0 vcons a1 vcons a2 vcons a3 vcons a4 vcons a5 vcons vnil) =
  hierarchicalVoxel
    (voxel3 (digitCoordinate a0) (digitCoordinate a1) (digitCoordinate a2))
    (voxel3 (digitCoordinate a3) (digitCoordinate a4) (digitCoordinate a5))

flattenDigitPair : Nat → Nat → Nat
flattenDigitPair coarse fine = 3 * coarse + fine

flattenHierarchicalVoxel : HierarchicalVoxel → Voxel3
flattenHierarchicalVoxel v =
  voxel3
    (flattenDigitPair (voxelX (coarseVoxel v)) (voxelX (fineVoxel v)))
    (flattenDigitPair (voxelY (coarseVoxel v)) (voxelY (fineVoxel v)))
    (flattenDigitPair (voxelZ (coarseVoxel v)) (voxelZ (fineVoxel v)))

sampleDepthSix : DepthSixAddress
sampleDepthSix =
  U369.digit6 vcons
  U369.digit9 vcons
  U369.digit3 vcons
  U369.digit9 vcons
  U369.digit6 vcons
  U369.digit3 vcons
  vnil

sampleCoarseVoxel : coarseVoxel (embedDepthSix sampleDepthSix) ≡ voxel3 1 2 0
sampleCoarseVoxel = refl

sampleFlattenedVoxel :
  flattenHierarchicalVoxel (embedDepthSix sampleDepthSix)
  ≡
  voxel3 5 7 0
sampleFlattenedVoxel = refl

------------------------------------------------------------------------
-- Exact ultrametric cylinder witness: two depth-three addresses sharing two
-- leading digits are at branch-distance one in the existing SSP369 metric.

cylinderAddressA : DepthThreeAddress
cylinderAddressA =
  U369.digit3 vcons U369.digit6 vcons U369.digit3 vcons vnil

cylinderAddressB : DepthThreeAddress
cylinderAddressB =
  U369.digit3 vcons U369.digit6 vcons U369.digit9 vcons vnil

sharedDepthTwoWitness :
  U369.PrefixMatch 2 cylinderAddressA cylinderAddressB
sharedDepthTwoWitness =
  U369.prefix-cons U369.digit3
    (U369.prefix-cons U369.digit6 U369.prefix-zero)

sharedDepthTwoHasDistanceOne :
  U369.distance cylinderAddressA cylinderAddressB ≡ 1
sharedDepthTwoHasDistanceOne = refl

------------------------------------------------------------------------
-- Adaptive refinement is driven by child variation, not by camera zoom alone.

childVariation : ThreeChildren Nat → Nat
childVariation children =
  (child3 children ⊔ child6 children ⊔ child9 children)
  ∸
  (child3 children ⊓ child6 children ⊓ child9 children)

canonicalVariationIsTwo :
  childVariation (threeChildren 3 4 5) ≡ 2
canonicalVariationIsTwo = refl

record PadicLODReasoningBoundary : Set where
  constructor padicLODReasoningBoundary
  field
    truncationRecoversDiscardedFineDigits : Bool
    truncationRecoversDiscardedFineDigitsIsFalse :
      truncationRecoversDiscardedFineDigits ≡ false

    voxelIsPrimaryReasoningState : Bool
    voxelIsPrimaryReasoningStateIsFalse :
      voxelIsPrimaryReasoningState ≡ false

    euclideanEmbeddingIsAnUltrametricIsometry : Bool
    euclideanEmbeddingIsAnUltrametricIsometryIsFalse :
      euclideanEmbeddingIsAnUltrametricIsometry ≡ false

    parentMassComesFromChildAggregation : Bool
    parentMassComesFromChildAggregationIsTrue :
      parentMassComesFromChildAggregation ≡ true

open PadicLODReasoningBoundary public

canonicalPadicLODReasoningBoundary : PadicLODReasoningBoundary
canonicalPadicLODReasoningBoundary =
  padicLODReasoningBoundary false refl false refl false refl true refl
