module DASHI.Cognition.Teleodynamics.AlbertE6WeightRoleCorrectionExact where

------------------------------------------------------------------------
-- CORRECT THE THREE DIFFERENT "27" ROLES
--
-- 1. Ternary27Point is a finite 27-element codebook carrier.
-- 2. RationalAlbert is a 27-dimensional rational vector-space-like algebra.
-- 3. A 27-root mixed fibre in E8 -> E6 x A2 is a finite 27-element weight-orbit
--    candidate for the minuscule E6 representation, not the representation
--    space itself.
--
-- Consequently, the right exceptional recognition target for the E8 mixed
-- fibre is a 27-WEIGHT system with action intertwining.  A finite fibre <->
-- RationalAlbert carrier equivalence is not the intended same-object theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (Set₁)

import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as A
import DASHI.Mathematics.Algebra.RationalAlbertAdvancedFrontierExact as AF
import DASHI.Cognition.Teleodynamics.E8ExceptionalBranchingBridgeExact as Branch
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry

record FiniteCodebookEmbedding (Source : Set) : Set₁ where
  field
    encode : Source → A.RationalAlbert
    injective : ∀ {x y} → encode x ≡ encode y → x ≡ y
    distinguishedPointMapsToUnit : Bool
    closedUnderAlbertProduct : Bool
    cubicNormSemanticsDeclared : Bool

record WeightOrbitRecognition (Fibre Weight : Set) : Set₁ where
  field
    toWeight : Fibre → Weight
    fromWeight : Weight → Fibre
    fromAfterTo : (x : Fibre) → fromWeight (toWeight x) ≡ x
    toAfterFrom : (w : Weight) → toWeight (fromWeight w) ≡ w
    fibreAction : Set
    weightAction : Set
    actionIntertwiningPaid : Bool

record AlbertE6WeightRoleBoundary : Set where
  constructor boundary
  field
    rationalAlbertRepresentationDimension27 : Bool
    finiteTernaryCodebookHas27Points : Bool
    e8MixedFibreHas27Roots : Bool
    finiteRootFibreIsAlbertRepresentationSpace : Bool
    finiteTernaryCarrierIsAlbertRepresentationSpace : Bool
    e8MixedFibreTargetsWeightOrbit : Bool
    ternary27TargetsCodebookEmbedding : Bool
    universalJordanIdentitySourceWritten : Bool
    cubicCharacteristicIdentitySourceWritten : Bool
    concreteC3AlbertAutomorphismSubgroup : Bool
    concreteC3NormStabilizerSubgroup : Bool
    e6WeightOrbitIntertwinerConstructed : Bool
    ternaryAlbertCodebookEmbeddingConstructed : Bool
    fullF4ActionConstructed : Bool
    fullE6ActionConstructed : Bool

open AlbertE6WeightRoleBoundary public

canonicalRoleBoundary : AlbertE6WeightRoleBoundary
canonicalRoleBoundary =
  boundary
    true true true
    false false
    true true
    (AF.universalJordanIdentitySourceWritten AF.currentAdvancedFrontier)
    (AF.cubicCharacteristicIdentitySourceWritten AF.currentAdvancedFrontier)
    true true
    false false false false

rationalAlbertDimensionIs27 : A.rationalAlbertDimension ≡ 27
rationalAlbertDimensionIs27 = A.rationalAlbertDimensionIs27

branchMixedFibreCountIs27 :
  Branch.positiveFibreCount Branch.canonicalE8E6A2RootSplitReceipt ≡ 27
branchMixedFibreCountIs27 = refl

-- Explicitly retain the finite ternary carrier as a codebook candidate rather
-- than silently promoting its 27 points to a 27-dimensional algebra.
TernaryCodebook : Set
TernaryCodebook = Geometry.Ternary27Point
