module DASHI.Moonshine.OggSmallCharacteristicIsotropyOrderCrossPollinationExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC ISOTROPY-ORDER CROSS-POLLINATION
--
-- External arithmetic authority:
--   p=2 supersingular automorphism order = 24
--   p=3 supersingular automorphism order = 12
--
-- Existing repository finite skeletons:
--   affine E6 / binary tetrahedral dimension-square sum = 24
--   rotational tetrahedral order = 12
--
-- DASHI contribution:
--   record the exact numerical alignment and the factor-two comparison while
--   refusing to identify these finite representation skeletons with the
--   arithmetic automorphism groups, the exponent-residual source groupoids,
--   or the retained p=2 orientation fibre.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Foundations.BinaryPolyhedralMcKayDimensionExact as McKay
import DASHI.Foundations.TetrahedralSO3RestrictionJ0To35Exact as Tetra
import DASHI.Moonshine.OggSmallCharacteristicAutomorphismOrderAttributionExact as OggAut
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Source

p2ExternalOrderMatchesBinaryTetrahedralSkeleton :
  OggAut.externalSupersingularAutomorphismOrder OggAut.p2
  ≡ McKay.e6DimensionSquareSum
p2ExternalOrderMatchesBinaryTetrahedralSkeleton =
  trans
    OggAut.p2ExternalAutomorphismOrderIs24
    (sym McKay.e6BinaryTetrahedralOrder)

p3ExternalOrderMatchesRotationalTetrahedralSkeleton :
  OggAut.externalSupersingularAutomorphismOrder OggAut.p3
  ≡ Tetra.tetrahedralOrder
p3ExternalOrderMatchesRotationalTetrahedralSkeleton = refl

binaryTetrahedralOrderIsTwiceRotationalTetrahedralOrder :
  McKay.e6DimensionSquareSum
  ≡ 2 * Tetra.tetrahedralOrder
binaryTetrahedralOrderIsTwiceRotationalTetrahedralOrder = refl

externalFactorTwoMatchesSkeletonFactorTwo :
  OggAut.externalSupersingularAutomorphismOrder OggAut.p2
  ≡ 2 * OggAut.externalSupersingularAutomorphismOrder OggAut.p3
externalFactorTwoMatchesSkeletonFactorTwo =
  OggAut.p2OrderIsTwiceP3Order

data NumericalOrderMatchIdentifiesArithmeticAutomorphismGroup : Set where
data FactorTwoIdentifiesRetainedOrientationFibre : Set where
data IsotropyOrderConstructsExponentResidualSource : Set where
data BinaryTetrahedralSkeletonIsCharacteristicTwoAutGroup : Set where
data TetrahedralSkeletonIsCharacteristicThreeAutGroup : Set where

numericalOrderMatchDoesNotIdentifyArithmeticAutomorphismGroup :
  NumericalOrderMatchIdentifiesArithmeticAutomorphismGroup -> ⊥
numericalOrderMatchDoesNotIdentifyArithmeticAutomorphismGroup ()

factorTwoDoesNotIdentifyRetainedOrientationFibre :
  FactorTwoIdentifiesRetainedOrientationFibre -> ⊥
factorTwoDoesNotIdentifyRetainedOrientationFibre ()

isotropyOrderDoesNotConstructExponentResidualSource :
  IsotropyOrderConstructsExponentResidualSource -> ⊥
isotropyOrderDoesNotConstructExponentResidualSource ()

binaryTetrahedralSkeletonNotPromotedToCharacteristicTwoAutGroup :
  BinaryTetrahedralSkeletonIsCharacteristicTwoAutGroup -> ⊥
binaryTetrahedralSkeletonNotPromotedToCharacteristicTwoAutGroup ()

tetrahedralSkeletonNotPromotedToCharacteristicThreeAutGroup :
  TetrahedralSkeletonIsCharacteristicThreeAutGroup -> ⊥
tetrahedralSkeletonNotPromotedToCharacteristicThreeAutGroup ()

comparisonOrigin : Source.ClaimOrigin
comparisonOrigin = Source.repositoryCrossModuleInference

record SmallCharacteristicIsotropyOrderBoundary : Set where
  constructor small-characteristic-isotropy-order-boundary
  field
    p2ExternalOrderMatchesRepo24Skeleton : Bool
    p3ExternalOrderMatchesRepo12Skeleton : Bool
    factorTwoSharedNumerically : Bool
    numericalMatchPromotedToGroupIsomorphism : Bool
    factorTwoPromotedToResidualOrientation : Bool
    isotropyOrderPromotedToExponentResidualSource : Bool

canonicalSmallCharacteristicIsotropyOrderBoundary :
  SmallCharacteristicIsotropyOrderBoundary
canonicalSmallCharacteristicIsotropyOrderBoundary =
  small-characteristic-isotropy-order-boundary
    true true true false false false
