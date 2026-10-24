module DASHI.Biology.IITPointedTernary27Origin26Exact where

------------------------------------------------------------------------
-- EXACT ORIGIN + 26 POINTED-CUBE DECOMPOSITION FOR IIT USE
--
-- Reuse the existing same-carrier theorem:
--
--   Ternary27Point <-> ScalarLine ⊎ NonOrigin26.
--
-- This is stronger than the arithmetic identity 27 = 1 + 26: `NonOrigin26`
-- has 26 explicit constructors, maps back into the existing geometric cube,
-- and round-trips through the exact carrier decomposition.  The distinguished
-- scalar summand is exactly the geometric origin.
--
-- The IIT lane consumes only that finite pointed-carrier structure.  It does
-- not inherit Albert/Jordan/F4/E6 semantics from the source module.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Wikimedia.IbrahimTernary27OriginTraceless26AlbertShapeBidiExact as Origin26
import DASHI.Biology.IITPointedTernary27FaceGluingExact as Pointed

------------------------------------------------------------------------
-- 1. Exact non-origin complement carrier.
------------------------------------------------------------------------

NonActive26 : Set
NonActive26 = Origin26.NonOrigin26

nonActiveConstructorCount : Nat
nonActiveConstructorCount = Origin26.nonOriginConstructorCount

nonActiveConstructorCountIsTwentySix :
  nonActiveConstructorCount ≡ 26
nonActiveConstructorCountIsTwentySix = refl

nonActiveToCubie : NonActive26 → Geometry.Ternary27Point
nonActiveToCubie = Origin26.nonOriginToPoint

canonicalActivePointedCube : Pointed.PointedTernary27Cube
canonicalActivePointedCube = Pointed.canonicalCentrePointedCube

canonicalActiveCubieIsOrigin :
  Pointed.activeCubie canonicalActivePointedCube ≡ Geometry.origin
canonicalActiveCubieIsOrigin = refl

------------------------------------------------------------------------
-- 2. The 26 constructors really exclude the distinguished active origin.
------------------------------------------------------------------------

nonOriginBranchCannotEqualScalarBranch :
  (q : NonActive26) →
  inj₂ q ≡ inj₁ Exceptional.scalarLine →
  ⊥
nonOriginBranchCannotEqualScalarBranch q ()

nonActiveCubieIsNotOrigin :
  (q : NonActive26) →
  nonActiveToCubie q ≡ Geometry.origin →
  ⊥
nonActiveCubieIsNotOrigin q equality =
  nonOriginBranchCannotEqualScalarBranch q branchEquality
  where
  branchEquality :
    inj₂ q ≡ inj₁ Exceptional.scalarLine
  branchEquality =
    trans
      (sym (Origin26.toAfterFrom (inj₂ q)))
      (trans
        (cong Origin26.toAlbertShape equality)
        Origin26.originMapsToScalar)

------------------------------------------------------------------------
-- 3. Re-export the exact two-sided 1+26 carrier chart.
------------------------------------------------------------------------

PointedOriginShape27 : Set
PointedOriginShape27 = Origin26.CubeAlbert27

toOriginPlus26 : Geometry.Ternary27Point → PointedOriginShape27
toOriginPlus26 = Origin26.toAlbertShape

fromOriginPlus26 : PointedOriginShape27 → Geometry.Ternary27Point
fromOriginPlus26 = Origin26.fromAlbertShape

originPlus26FromAfterTo :
  (point : Geometry.Ternary27Point) →
  fromOriginPlus26 (toOriginPlus26 point) ≡ point
originPlus26FromAfterTo = Origin26.fromAfterTo

originPlus26ToAfterFrom :
  (shape : PointedOriginShape27) →
  toOriginPlus26 (fromOriginPlus26 shape) ≡ shape
originPlus26ToAfterFrom = Origin26.toAfterFrom

originMapsToDistinguishedScalar :
  toOriginPlus26 Geometry.origin ≡ inj₁ Exceptional.scalarLine
originMapsToDistinguishedScalar = Origin26.originMapsToScalar

------------------------------------------------------------------------
-- 4. This exact origin-pointed decomposition is not an arbitrary-point
--    recentering theorem and does not promote exceptional algebra semantics.
------------------------------------------------------------------------

record IITOrigin26Boundary : Set where
  constructor iit-origin26-boundary
  field
    explicitTwentySixConstructorComplementReused : Bool
    originPlusTwentySixBijectionReused : Bool
    distinguishedActiveCubieIsGeometricOrigin : Bool
    everyNonActiveConstructorExcludesOrigin : Bool
    arbitraryActiveCubieIsOriginByDefinition : Bool
    carrierBijectionCreatesJordanProduct : Bool
    carrierBijectionCreatesF4OrE6Action : Bool
    originPlusTwentySixEqualsIITPhiByDefinition : Bool

open IITOrigin26Boundary public

canonicalIITOrigin26Boundary : IITOrigin26Boundary
canonicalIITOrigin26Boundary =
  iit-origin26-boundary
    true true true true
    false false false false

originPointingIsNotArbitraryPointing :
  arbitraryActiveCubieIsOriginByDefinition canonicalIITOrigin26Boundary ≡ false
originPointingIsNotArbitraryPointing = refl

origin26DoesNotCreateExceptionalAction :
  carrierBijectionCreatesF4OrE6Action canonicalIITOrigin26Boundary ≡ false
origin26DoesNotCreateExceptionalAction = refl

origin26DoesNotSelfPromoteToPhi :
  originPlusTwentySixEqualsIITPhiByDefinition canonicalIITOrigin26Boundary ≡ false
origin26DoesNotSelfPromoteToPhi = refl
