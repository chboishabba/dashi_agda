module DASHI.Cognition.Teleodynamics.AlbertE6BranchingWeldExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as A
import DASHI.Cognition.Teleodynamics.E8ExceptionalBranchingBridgeExact as Branch
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry

------------------------------------------------------------------------
-- Three different 27-sized objects now coexist and must not be collapsed:
--
-- 1. the repo-native ternary 27 finite carrier;
-- 2. the rational Albert algebra H_3(O_Q), with product/unit/cubic norm;
-- 3. each 27-root mixed fibre in the E8 -> E6 x A2 branching audit.
--
-- This module makes the missing SAME-OBJECT obligations explicit.
------------------------------------------------------------------------

record ProductNormRecognition
  (Source Target : Set)
  : Set₁ where
  field
    toTarget : Source → Target
    fromTarget : Target → Source
    fromAfterTo : (x : Source) → fromTarget (toTarget x) ≡ x
    toAfterFrom : (y : Target) → toTarget (fromTarget y) ≡ y

record Ternary27AlbertRecognition : Set₁ where
  field
    carrierRecognition :
      ProductNormRecognition Geometry.Ternary27Point A.RationalAlbert
    productTransported : Bool
    cubicNormTransported : Bool
    distinguishedOriginMapsToAlbertUnit : Bool

record E8FibreAlbertRecognition (Fibre : Set) : Set₁ where
  field
    carrierRecognition : ProductNormRecognition Fibre A.RationalAlbert
    e6ActionOnFibre : Set
    e6ActionOnAlbert : Set
    sameE6ActionIntertwined : Bool
    productCompatible : Bool
    cubicNormCompatible : Bool

record AlbertE6BranchingBoundary : Set where
  constructor boundary
  field
    rationalAlbert27Available : Bool
    rationalAlbertProductAvailable : Bool
    rationalAlbertCubicNormAvailable : Bool
    e8ThreeBy27FibresExecutable : Bool
    ternary27FiniteCarrierAvailable : Bool
    ternary27RecognizedAsRationalAlbert : Bool
    e8Fibre27RecognizedAsRationalAlbert : Bool
    e8FibreCarriesE6FundamentalActionHere : Bool
    f4AutomorphismActionInhabitedHere : Bool
    e6NormStabilizerActionInhabitedHere : Bool

open AlbertE6BranchingBoundary public

canonicalAlbertE6BranchingBoundary : AlbertE6BranchingBoundary
canonicalAlbertE6BranchingBoundary =
  boundary
    true true true true true
    false false false false false

rationalAlbertDimension27 : A.rationalAlbertDimension ≡ 27
rationalAlbertDimension27 = A.rationalAlbertDimensionIs27

branchFibreDimension27 : Branch.positiveFibreCount Branch.canonicalE8E6A2RootSplitReceipt ≡ 27
branchFibreDimension27 = refl
