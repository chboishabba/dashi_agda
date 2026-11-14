module DASHI.Cognition.Teleodynamics.AlbertPriorBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (inj₁)

import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as AF
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Wikimedia.IbrahimTernary27OriginTraceless26AlbertShapeBidiExact as Albert
import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as RationalAlbert
import DASHI.Cognition.Teleodynamics.GeometricLearnerPriorExact as Prior

------------------------------------------------------------------------
-- ALBERT-SHAPED 1+26 EXPERIMENT ARM
--
-- This reuses the exact existing ternary-27 carrier bijection
--   Ternary27Point <-> ScalarLine + NonOrigin26
-- as an experiment codebook shape.
--
-- The repository now ALSO owns an independent rational H_3(O_Q) carrier with
-- a concrete Jordan-product formula, unit and cubic norm.  That does not make
-- the ternary-27 carrier an Albert algebra: promotion now requires an explicit
-- two-sided carrier map which preserves the Jordan product and cubic norm.
------------------------------------------------------------------------

scalarArmPoint : Albert.CubeAlbert27
scalarArmPoint = inj₁ AF.scalarLine

originMapsToPriorScalar :
  Albert.toAlbertShape Geometry.origin ≡ scalarArmPoint
originMapsToPriorScalar = Albert.originMapsToScalar

repoNativeRationalAlbertDimension : RationalAlbert.rationalAlbertDimension ≡ 27
repoNativeRationalAlbertDimension = RationalAlbert.rationalAlbertDimensionIs27

ternaryAlbertPrior : Prior.GeometricLearnerPrior
ternaryAlbertPrior =
  Prior.geometricLearnerPrior
    "ternary 27 / scalar+26 experiment prior"
    "Ternary27Point"
    "application-supplied projection to ternary carrier"
    "ScalarLine + NonOrigin26"
    "discrete application-supplied geometry"
    "optional categorical/soft projection"
    "none required"
    "optional occupancy/alignment observer"
    "DASHI carrier-shape bridge; rational Albert algebra exists separately"
    true false false false

data TernaryPriorInheritsAlbertJordanProduct : Set where
data AlbertPriorCreatesF4Action : Set where
data AlbertPriorCreatesE6Action : Set where

ternaryPriorDoesNotInheritAlbertJordanProduct :
  TernaryPriorInheritsAlbertJordanProduct → ⊥
ternaryPriorDoesNotInheritAlbertJordanProduct ()

albertPriorDoesNotCreateF4Action : AlbertPriorCreatesF4Action → ⊥
albertPriorDoesNotCreateF4Action ()

albertPriorDoesNotCreateE6Action : AlbertPriorCreatesE6Action → ⊥
albertPriorDoesNotCreateE6Action ()

record AlbertPriorBoundary : Set where
  constructor albertPriorBoundary
  field
    exactTernary27CarrierReused : Bool
    exactOriginPlus26BijectionReused : Bool
    repoNativeRationalAlbertCarrierAvailable : Bool
    repoNativeJordanProductFormulaAvailable : Bool
    repoNativeCubicNormFormulaAvailable : Bool
    ternaryToRationalAlbertBijectionConstructed : Bool
    ternaryProductIntertwinerConstructed : Bool
    ternaryCubicNormPreservationProved : Bool
    jordanProductInheritedByTernaryPrior : Bool
    f4ActionCreated : Bool
    e6ActionCreated : Bool

canonicalAlbertPriorBoundary : AlbertPriorBoundary
canonicalAlbertPriorBoundary =
  albertPriorBoundary
    true true
    true true true
    false false false false
    false false
