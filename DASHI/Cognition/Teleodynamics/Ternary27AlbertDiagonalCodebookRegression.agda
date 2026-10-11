module DASHI.Cognition.Teleodynamics.Ternary27AlbertDiagonalCodebookRegression where

import DASHI.Cognition.Teleodynamics.Ternary27AlbertDiagonalCodebookExact as C
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as G
import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as A

open import Agda.Builtin.Equality using (_≡_)

positiveCornerMapsToUnit :
  C.encodePoint G.positiveCorner ≡ A.albertUnit
positiveCornerMapsToUnit = C.positiveCornerToUnit

originMapsToZero :
  C.encodePoint G.origin ≡ C.zeroAlbert
originMapsToZero = C.originToZero

productIntertwiningPinned : (p q : G.Ternary27Point) →
  A.jordanProduct (C.encodePoint p) (C.encodePoint q)
  ≡ C.encodePoint (C.pointMul p q)
productIntertwiningPinned = C.encodePreservesProduct
