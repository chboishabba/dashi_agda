module DASHI.Wikimedia.KeyShoeNativeFieldIncidenceExact where

-- H19d: reuse native ternary 27-point carrier and Griess arithmetic.
-- Coordinates in the polynomial basis are a chart, not the original grid metric.
-- KeyShoe source diagrams remain provisional; no creator operator or Monster identification.
open import DASHI.Core.Prelude
import DASHI.Foundations.SSPTritCarrier as S
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as C
import DASHI.Moonshine.Griess1990Moufang81IbrahimProjective13Exact as F
import DASHI.Analysis.RHFourWindowC26NativeHyperfabricSquareExact as G
import DASHI.Wikimedia.KeyShoeCLARAR13DihedralExact as R
import DASHI.Wikimedia.KeyShoeIndexedTrigramWeaveExact as K

Point : Set
Point = C.Ternary27Point

open F using (add3; sub3; mul3; neg3)
open C using (ternary27Point)

-- Exact finite chart from signed R13 into polynomial coefficients.
toPolynomial : K.Value → Point
toPolynomial K.zeroValue = (C.ternary27Point S.sspZero S.sspZero S.sspZero)
toPolynomial (K.signedSlot (R.slot R.b0 R.first)) = (C.ternary27Point S.sspZero S.sspNegOne S.sspPosOne)
toPolynomial (K.signedSlot (R.slot R.b0 R.second)) = (C.ternary27Point S.sspZero S.sspPosOne S.sspNegOne)
toPolynomial (K.signedSlot (R.slot R.b1 R.first)) = (C.ternary27Point S.sspPosOne S.sspPosOne S.sspNegOne)
toPolynomial (K.signedSlot (R.slot R.b1 R.second)) = (C.ternary27Point S.sspNegOne S.sspNegOne S.sspPosOne)
toPolynomial (K.signedSlot (R.slot R.b2 R.first)) = (C.ternary27Point S.sspNegOne S.sspZero S.sspPosOne)
toPolynomial (K.signedSlot (R.slot R.b2 R.second)) = (C.ternary27Point S.sspPosOne S.sspZero S.sspNegOne)
toPolynomial (K.signedSlot (R.slot R.b3 R.first)) = (C.ternary27Point S.sspPosOne S.sspZero S.sspZero)
toPolynomial (K.signedSlot (R.slot R.b3 R.second)) = (C.ternary27Point S.sspNegOne S.sspZero S.sspZero)
toPolynomial (K.signedSlot (R.slot R.b4 R.first)) = (C.ternary27Point S.sspZero S.sspPosOne S.sspZero)
toPolynomial (K.signedSlot (R.slot R.b4 R.second)) = (C.ternary27Point S.sspZero S.sspNegOne S.sspZero)
toPolynomial (K.signedSlot (R.slot R.b5 R.first)) = (C.ternary27Point S.sspZero S.sspZero S.sspPosOne)
toPolynomial (K.signedSlot (R.slot R.b5 R.second)) = (C.ternary27Point S.sspZero S.sspZero S.sspNegOne)
toPolynomial (K.signedSlot (R.slot R.b6 R.first)) = (C.ternary27Point S.sspPosOne S.sspPosOne S.sspZero)
toPolynomial (K.signedSlot (R.slot R.b6 R.second)) = (C.ternary27Point S.sspNegOne S.sspNegOne S.sspZero)
toPolynomial (K.signedSlot (R.slot R.b7 R.first)) = (C.ternary27Point S.sspZero S.sspPosOne S.sspPosOne)
toPolynomial (K.signedSlot (R.slot R.b7 R.second)) = (C.ternary27Point S.sspZero S.sspNegOne S.sspNegOne)
toPolynomial (K.signedSlot (R.slot R.b8 R.first)) = (C.ternary27Point S.sspPosOne S.sspPosOne S.sspPosOne)
toPolynomial (K.signedSlot (R.slot R.b8 R.second)) = (C.ternary27Point S.sspNegOne S.sspNegOne S.sspNegOne)
toPolynomial (K.signedSlot (R.slot R.b9 R.first)) = (C.ternary27Point S.sspPosOne S.sspNegOne S.sspPosOne)
toPolynomial (K.signedSlot (R.slot R.b9 R.second)) = (C.ternary27Point S.sspNegOne S.sspPosOne S.sspNegOne)
toPolynomial (K.signedSlot (R.slot R.b10 R.first)) = (C.ternary27Point S.sspPosOne S.sspNegOne S.sspNegOne)
toPolynomial (K.signedSlot (R.slot R.b10 R.second)) = (C.ternary27Point S.sspNegOne S.sspPosOne S.sspPosOne)
toPolynomial (K.signedSlot (R.slot R.b11 R.first)) = (C.ternary27Point S.sspNegOne S.sspZero S.sspNegOne)
toPolynomial (K.signedSlot (R.slot R.b11 R.second)) = (C.ternary27Point S.sspPosOne S.sspZero S.sspPosOne)
toPolynomial (K.signedSlot (R.slot R.b12 R.first)) = (C.ternary27Point S.sspNegOne S.sspPosOne S.sspZero)
toPolynomial (K.signedSlot (R.slot R.b12 R.second)) = (C.ternary27Point S.sspPosOne S.sspNegOne S.sspZero)

fromPolynomial : Point → K.Value
fromPolynomial (C.ternary27Point S.sspZero S.sspZero S.sspZero) = K.zeroValue
fromPolynomial (C.ternary27Point S.sspZero S.sspNegOne S.sspPosOne) = (K.signedSlot (R.slot R.b0 R.first))
fromPolynomial (C.ternary27Point S.sspZero S.sspPosOne S.sspNegOne) = (K.signedSlot (R.slot R.b0 R.second))
fromPolynomial (C.ternary27Point S.sspPosOne S.sspPosOne S.sspNegOne) = (K.signedSlot (R.slot R.b1 R.first))
fromPolynomial (C.ternary27Point S.sspNegOne S.sspNegOne S.sspPosOne) = (K.signedSlot (R.slot R.b1 R.second))
fromPolynomial (C.ternary27Point S.sspNegOne S.sspZero S.sspPosOne) = (K.signedSlot (R.slot R.b2 R.first))
fromPolynomial (C.ternary27Point S.sspPosOne S.sspZero S.sspNegOne) = (K.signedSlot (R.slot R.b2 R.second))
fromPolynomial (C.ternary27Point S.sspPosOne S.sspZero S.sspZero) = (K.signedSlot (R.slot R.b3 R.first))
fromPolynomial (C.ternary27Point S.sspNegOne S.sspZero S.sspZero) = (K.signedSlot (R.slot R.b3 R.second))
fromPolynomial (C.ternary27Point S.sspZero S.sspPosOne S.sspZero) = (K.signedSlot (R.slot R.b4 R.first))
fromPolynomial (C.ternary27Point S.sspZero S.sspNegOne S.sspZero) = (K.signedSlot (R.slot R.b4 R.second))
fromPolynomial (C.ternary27Point S.sspZero S.sspZero S.sspPosOne) = (K.signedSlot (R.slot R.b5 R.first))
fromPolynomial (C.ternary27Point S.sspZero S.sspZero S.sspNegOne) = (K.signedSlot (R.slot R.b5 R.second))
fromPolynomial (C.ternary27Point S.sspPosOne S.sspPosOne S.sspZero) = (K.signedSlot (R.slot R.b6 R.first))
fromPolynomial (C.ternary27Point S.sspNegOne S.sspNegOne S.sspZero) = (K.signedSlot (R.slot R.b6 R.second))
fromPolynomial (C.ternary27Point S.sspZero S.sspPosOne S.sspPosOne) = (K.signedSlot (R.slot R.b7 R.first))
fromPolynomial (C.ternary27Point S.sspZero S.sspNegOne S.sspNegOne) = (K.signedSlot (R.slot R.b7 R.second))
fromPolynomial (C.ternary27Point S.sspPosOne S.sspPosOne S.sspPosOne) = (K.signedSlot (R.slot R.b8 R.first))
fromPolynomial (C.ternary27Point S.sspNegOne S.sspNegOne S.sspNegOne) = (K.signedSlot (R.slot R.b8 R.second))
fromPolynomial (C.ternary27Point S.sspPosOne S.sspNegOne S.sspPosOne) = (K.signedSlot (R.slot R.b9 R.first))
fromPolynomial (C.ternary27Point S.sspNegOne S.sspPosOne S.sspNegOne) = (K.signedSlot (R.slot R.b9 R.second))
fromPolynomial (C.ternary27Point S.sspPosOne S.sspNegOne S.sspNegOne) = (K.signedSlot (R.slot R.b10 R.first))
fromPolynomial (C.ternary27Point S.sspNegOne S.sspPosOne S.sspPosOne) = (K.signedSlot (R.slot R.b10 R.second))
fromPolynomial (C.ternary27Point S.sspNegOne S.sspZero S.sspNegOne) = (K.signedSlot (R.slot R.b11 R.first))
fromPolynomial (C.ternary27Point S.sspPosOne S.sspZero S.sspPosOne) = (K.signedSlot (R.slot R.b11 R.second))
fromPolynomial (C.ternary27Point S.sspNegOne S.sspPosOne S.sspZero) = (K.signedSlot (R.slot R.b12 R.first))
fromPolynomial (C.ternary27Point S.sspPosOne S.sspNegOne S.sspZero) = (K.signedSlot (R.slot R.b12 R.second))

slotRoundTrip : (x : K.Value) → fromPolynomial (toPolynomial x) ≡ x
slotRoundTrip K.zeroValue = refl
slotRoundTrip (K.signedSlot (R.slot R.b0 R.first)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b0 R.second)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b1 R.first)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b1 R.second)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b2 R.first)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b2 R.second)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b3 R.first)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b3 R.second)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b4 R.first)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b4 R.second)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b5 R.first)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b5 R.second)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b6 R.first)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b6 R.second)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b7 R.first)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b7 R.second)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b8 R.first)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b8 R.second)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b9 R.first)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b9 R.second)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b10 R.first)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b10 R.second)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b11 R.first)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b11 R.second)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b12 R.first)) = refl
slotRoundTrip (K.signedSlot (R.slot R.b12 R.second)) = refl

polynomialRoundTrip : (x : Point) → toPolynomial (fromPolynomial x) ≡ x
polynomialRoundTrip (C.ternary27Point S.sspZero S.sspZero S.sspZero) = refl
polynomialRoundTrip (C.ternary27Point S.sspPosOne S.sspZero S.sspZero) = refl
polynomialRoundTrip (C.ternary27Point S.sspNegOne S.sspZero S.sspZero) = refl
polynomialRoundTrip (C.ternary27Point S.sspZero S.sspPosOne S.sspZero) = refl
polynomialRoundTrip (C.ternary27Point S.sspPosOne S.sspPosOne S.sspZero) = refl
polynomialRoundTrip (C.ternary27Point S.sspNegOne S.sspPosOne S.sspZero) = refl
polynomialRoundTrip (C.ternary27Point S.sspZero S.sspNegOne S.sspZero) = refl
polynomialRoundTrip (C.ternary27Point S.sspPosOne S.sspNegOne S.sspZero) = refl
polynomialRoundTrip (C.ternary27Point S.sspNegOne S.sspNegOne S.sspZero) = refl
polynomialRoundTrip (C.ternary27Point S.sspZero S.sspZero S.sspPosOne) = refl
polynomialRoundTrip (C.ternary27Point S.sspPosOne S.sspZero S.sspPosOne) = refl
polynomialRoundTrip (C.ternary27Point S.sspNegOne S.sspZero S.sspPosOne) = refl
polynomialRoundTrip (C.ternary27Point S.sspZero S.sspPosOne S.sspPosOne) = refl
polynomialRoundTrip (C.ternary27Point S.sspPosOne S.sspPosOne S.sspPosOne) = refl
polynomialRoundTrip (C.ternary27Point S.sspNegOne S.sspPosOne S.sspPosOne) = refl
polynomialRoundTrip (C.ternary27Point S.sspZero S.sspNegOne S.sspPosOne) = refl
polynomialRoundTrip (C.ternary27Point S.sspPosOne S.sspNegOne S.sspPosOne) = refl
polynomialRoundTrip (C.ternary27Point S.sspNegOne S.sspNegOne S.sspPosOne) = refl
polynomialRoundTrip (C.ternary27Point S.sspZero S.sspZero S.sspNegOne) = refl
polynomialRoundTrip (C.ternary27Point S.sspPosOne S.sspZero S.sspNegOne) = refl
polynomialRoundTrip (C.ternary27Point S.sspNegOne S.sspZero S.sspNegOne) = refl
polynomialRoundTrip (C.ternary27Point S.sspZero S.sspPosOne S.sspNegOne) = refl
polynomialRoundTrip (C.ternary27Point S.sspPosOne S.sspPosOne S.sspNegOne) = refl
polynomialRoundTrip (C.ternary27Point S.sspNegOne S.sspPosOne S.sspNegOne) = refl
polynomialRoundTrip (C.ternary27Point S.sspZero S.sspNegOne S.sspNegOne) = refl
polynomialRoundTrip (C.ternary27Point S.sspPosOne S.sspNegOne S.sspNegOne) = refl
polynomialRoundTrip (C.ternary27Point S.sspNegOne S.sspNegOne S.sspNegOne) = refl

-- B and B^-1 from the original gradeOrder13 cyclic basis.
toNative : Point → Point
toNative (ternary27Point a b c) =
  ternary27Point (add3 (add3 a b) c) c (sub3 b c)

fromNative : Point → Point
fromNative (ternary27Point x y z) =
  ternary27Point (sub3 (add3 x y) z) (add3 y z) y

nativeRoundTrip : (x : Point) → fromNative (toNative x) ≡ x
nativeRoundTrip (C.ternary27Point S.sspZero S.sspZero S.sspZero) = refl
nativeRoundTrip (C.ternary27Point S.sspPosOne S.sspZero S.sspZero) = refl
nativeRoundTrip (C.ternary27Point S.sspNegOne S.sspZero S.sspZero) = refl
nativeRoundTrip (C.ternary27Point S.sspZero S.sspPosOne S.sspZero) = refl
nativeRoundTrip (C.ternary27Point S.sspPosOne S.sspPosOne S.sspZero) = refl
nativeRoundTrip (C.ternary27Point S.sspNegOne S.sspPosOne S.sspZero) = refl
nativeRoundTrip (C.ternary27Point S.sspZero S.sspNegOne S.sspZero) = refl
nativeRoundTrip (C.ternary27Point S.sspPosOne S.sspNegOne S.sspZero) = refl
nativeRoundTrip (C.ternary27Point S.sspNegOne S.sspNegOne S.sspZero) = refl
nativeRoundTrip (C.ternary27Point S.sspZero S.sspZero S.sspPosOne) = refl
nativeRoundTrip (C.ternary27Point S.sspPosOne S.sspZero S.sspPosOne) = refl
nativeRoundTrip (C.ternary27Point S.sspNegOne S.sspZero S.sspPosOne) = refl
nativeRoundTrip (C.ternary27Point S.sspZero S.sspPosOne S.sspPosOne) = refl
nativeRoundTrip (C.ternary27Point S.sspPosOne S.sspPosOne S.sspPosOne) = refl
nativeRoundTrip (C.ternary27Point S.sspNegOne S.sspPosOne S.sspPosOne) = refl
nativeRoundTrip (C.ternary27Point S.sspZero S.sspNegOne S.sspPosOne) = refl
nativeRoundTrip (C.ternary27Point S.sspPosOne S.sspNegOne S.sspPosOne) = refl
nativeRoundTrip (C.ternary27Point S.sspNegOne S.sspNegOne S.sspPosOne) = refl
nativeRoundTrip (C.ternary27Point S.sspZero S.sspZero S.sspNegOne) = refl
nativeRoundTrip (C.ternary27Point S.sspPosOne S.sspZero S.sspNegOne) = refl
nativeRoundTrip (C.ternary27Point S.sspNegOne S.sspZero S.sspNegOne) = refl
nativeRoundTrip (C.ternary27Point S.sspZero S.sspPosOne S.sspNegOne) = refl
nativeRoundTrip (C.ternary27Point S.sspPosOne S.sspPosOne S.sspNegOne) = refl
nativeRoundTrip (C.ternary27Point S.sspNegOne S.sspPosOne S.sspNegOne) = refl
nativeRoundTrip (C.ternary27Point S.sspZero S.sspNegOne S.sspNegOne) = refl
nativeRoundTrip (C.ternary27Point S.sspPosOne S.sspNegOne S.sspNegOne) = refl
nativeRoundTrip (C.ternary27Point S.sspNegOne S.sspNegOne S.sspNegOne) = refl

nativeInverseRoundTrip : (x : Point) → toNative (fromNative x) ≡ x
nativeInverseRoundTrip (C.ternary27Point S.sspZero S.sspZero S.sspZero) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspPosOne S.sspZero S.sspZero) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspNegOne S.sspZero S.sspZero) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspZero S.sspPosOne S.sspZero) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspPosOne S.sspPosOne S.sspZero) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspNegOne S.sspPosOne S.sspZero) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspZero S.sspNegOne S.sspZero) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspPosOne S.sspNegOne S.sspZero) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspNegOne S.sspNegOne S.sspZero) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspZero S.sspZero S.sspPosOne) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspPosOne S.sspZero S.sspPosOne) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspNegOne S.sspZero S.sspPosOne) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspZero S.sspPosOne S.sspPosOne) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspPosOne S.sspPosOne S.sspPosOne) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspNegOne S.sspPosOne S.sspPosOne) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspZero S.sspNegOne S.sspPosOne) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspPosOne S.sspNegOne S.sspPosOne) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspNegOne S.sspNegOne S.sspPosOne) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspZero S.sspZero S.sspNegOne) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspPosOne S.sspZero S.sspNegOne) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspNegOne S.sspZero S.sspNegOne) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspZero S.sspPosOne S.sspNegOne) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspPosOne S.sspPosOne S.sspNegOne) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspNegOne S.sspPosOne S.sspNegOne) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspZero S.sspNegOne S.sspNegOne) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspPosOne S.sspNegOne S.sspNegOne) = refl
nativeInverseRoundTrip (C.ternary27Point S.sspNegOne S.sspNegOne S.sspNegOne) = refl

timesT : Point → Point
timesT (ternary27Point a b c) = ternary27Point c (add3 a c) b

nativeSingerIntertwines : (x : Point) → toNative (timesT x) ≡ G.gradeOrder13 (toNative x)
nativeSingerIntertwines (C.ternary27Point S.sspZero S.sspZero S.sspZero) = refl
nativeSingerIntertwines (C.ternary27Point S.sspPosOne S.sspZero S.sspZero) = refl
nativeSingerIntertwines (C.ternary27Point S.sspNegOne S.sspZero S.sspZero) = refl
nativeSingerIntertwines (C.ternary27Point S.sspZero S.sspPosOne S.sspZero) = refl
nativeSingerIntertwines (C.ternary27Point S.sspPosOne S.sspPosOne S.sspZero) = refl
nativeSingerIntertwines (C.ternary27Point S.sspNegOne S.sspPosOne S.sspZero) = refl
nativeSingerIntertwines (C.ternary27Point S.sspZero S.sspNegOne S.sspZero) = refl
nativeSingerIntertwines (C.ternary27Point S.sspPosOne S.sspNegOne S.sspZero) = refl
nativeSingerIntertwines (C.ternary27Point S.sspNegOne S.sspNegOne S.sspZero) = refl
nativeSingerIntertwines (C.ternary27Point S.sspZero S.sspZero S.sspPosOne) = refl
nativeSingerIntertwines (C.ternary27Point S.sspPosOne S.sspZero S.sspPosOne) = refl
nativeSingerIntertwines (C.ternary27Point S.sspNegOne S.sspZero S.sspPosOne) = refl
nativeSingerIntertwines (C.ternary27Point S.sspZero S.sspPosOne S.sspPosOne) = refl
nativeSingerIntertwines (C.ternary27Point S.sspPosOne S.sspPosOne S.sspPosOne) = refl
nativeSingerIntertwines (C.ternary27Point S.sspNegOne S.sspPosOne S.sspPosOne) = refl
nativeSingerIntertwines (C.ternary27Point S.sspZero S.sspNegOne S.sspPosOne) = refl
nativeSingerIntertwines (C.ternary27Point S.sspPosOne S.sspNegOne S.sspPosOne) = refl
nativeSingerIntertwines (C.ternary27Point S.sspNegOne S.sspNegOne S.sspPosOne) = refl
nativeSingerIntertwines (C.ternary27Point S.sspZero S.sspZero S.sspNegOne) = refl
nativeSingerIntertwines (C.ternary27Point S.sspPosOne S.sspZero S.sspNegOne) = refl
nativeSingerIntertwines (C.ternary27Point S.sspNegOne S.sspZero S.sspNegOne) = refl
nativeSingerIntertwines (C.ternary27Point S.sspZero S.sspPosOne S.sspNegOne) = refl
nativeSingerIntertwines (C.ternary27Point S.sspPosOne S.sspPosOne S.sspNegOne) = refl
nativeSingerIntertwines (C.ternary27Point S.sspNegOne S.sspPosOne S.sspNegOne) = refl
nativeSingerIntertwines (C.ternary27Point S.sspZero S.sspNegOne S.sspNegOne) = refl
nativeSingerIntertwines (C.ternary27Point S.sspPosOne S.sspNegOne S.sspNegOne) = refl
nativeSingerIntertwines (C.ternary27Point S.sspNegOne S.sspNegOne S.sspNegOne) = refl

negative : Point → Point
negative (ternary27Point a b c) = ternary27Point (neg3 a) (neg3 b) (neg3 c)

slotSignIntertwines : (x : K.Value) → toPolynomial (K.negativeValue x) ≡ negative (toPolynomial x)
slotSignIntertwines K.zeroValue = refl
slotSignIntertwines (K.signedSlot (R.slot R.b0 R.first)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b0 R.second)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b1 R.first)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b1 R.second)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b2 R.first)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b2 R.second)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b3 R.first)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b3 R.second)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b4 R.first)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b4 R.second)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b5 R.first)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b5 R.second)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b6 R.first)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b6 R.second)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b7 R.first)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b7 R.second)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b8 R.first)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b8 R.second)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b9 R.first)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b9 R.second)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b10 R.first)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b10 R.second)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b11 R.first)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b11 R.second)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b12 R.first)) = refl
slotSignIntertwines (K.signedSlot (R.slot R.b12 R.second)) = refl

-- Pull back the existing signed inversion, with occupied zero retained.
inverse : Point → Point
inverse x = toPolynomial (K.inverseValue (fromPolynomial x))

inverseInvolutive : (x : Point) → inverse (inverse x) ≡ x
inverseInvolutive x
  rewrite slotRoundTrip (K.inverseValue (fromPolynomial x))
        | K.inverse² (fromPolynomial x)
        | polynomialRoundTrip x = refl

add sub : Point → Point → Point
add (ternary27Point a b c) (ternary27Point d e f) =
  ternary27Point (add3 a d) (add3 b e) (add3 c f)
sub (ternary27Point a b c) (ternary27Point d e f) =
  ternary27Point (sub3 a d) (sub3 b e) (sub3 c f)

-- Polynomial product reduced by t^3=t+1, t^4=t^2+t.
mul : Point → Point → Point
mul (ternary27Point a b c) (ternary27Point d e f) =
  let p0 = mul3 a d
      p1 = add3 (mul3 a e) (mul3 b d)
      p2 = add3 (add3 (mul3 a f) (mul3 b e)) (mul3 c d)
      p3 = add3 (mul3 b f) (mul3 c e)
      p4 = mul3 c f
  in ternary27Point (add3 p0 p3) (add3 (add3 p1 p3) p4) (add3 p2 p4)

dot : Point → Point → S.SSPTrit
dot (ternary27Point a b c) (ternary27Point d e f) =
  add3 (add3 (mul3 a d) (mul3 b e)) (mul3 c f)

-- B^-T normal transform, not the point transform B.
dualNative : Point → Point
dualNative (ternary27Point a b c) =
  ternary27Point a (add3 (add3 a b) c) (sub3 b a)

-- Nonzero projective point is kept as a premise, not silently inferred.
LineAt : Point → Point → Set
LineAt n x = (x ≡ C.origin → ⊥) × (dot n x ≡ S.sspZero)

-- Indexed conic predicate via the exact inverse chart. Quadratic
-- recognition via x^3*x^9 is separately checked by the H17d replay.
ConicAt : Point → Point → Set
ConicAt n x = LineAt n (inverse x)

lineToConic : (n x : Point) → LineAt n x → ConicAt n (inverse x)
lineToConic n x h = subst (LineAt n) (sym (inverseInvolutive x)) h

conicToLine : (n x : Point) → ConicAt n x → LineAt n (inverse x)
conicToLine n x h = h

-- Distinct role anchors and ratio sheet are explicit in the predicate.
ratio₁ ratio₂ one : Point
ratio₁ = (C.ternary27Point S.sspPosOne S.sspPosOne S.sspNegOne)
ratio₂ = (C.ternary27Point S.sspNegOne S.sspPosOne S.sspPosOne)
one = (C.ternary27Point S.sspPosOne S.sspZero S.sspZero)

data RatioSheet : Set where
  direct reflected : RatioSheet

ratioOf : RatioSheet → Point
ratioOf direct = ratio₁
ratioOf reflected = ratio₂

completeRight : RatioSheet → Point → Point → Point
completeRight sheet a b = add a (mul (ratioOf sheet) (sub b a))

completeMiddle : RatioSheet → Point → Point → Point
completeMiddle sheet a c = add a (mul (inverse (ratioOf sheet)) (sub c a))

completeLeft : RatioSheet → Point → Point → Point
completeLeft sheet b c =
  mul (inverse (sub one (ratioOf sheet))) (sub c (mul (ratioOf sheet) b))

RatioRelation : RatioSheet → K.Triple → Set
RatioRelation sheet (K.tri a b c) =
  (toPolynomial a ≡ toPolynomial b → ⊥) ×
  (toPolynomial c ≡ completeRight sheet (toPolynomial a) (toPolynomial b))

-- Exact predicate attachment to the prior native indexed letter weave.
-- It is the original canonical ratio relation, not a false invariant
-- of arbitrary raw-coordinate inversion or role reversal.
IndexedRatio : K.Mask → RatioSheet → K.Triple → Set
IndexedRatio m sheet x = RatioRelation sheet (K.decode m x)

ratioTransport : (m n : K.Mask) (sheet : RatioSheet) (x : K.Triple) →
  IndexedRatio m sheet x → IndexedRatio n sheet (K.encode n (K.decode m x))
ratioTransport m n sheet x = K.transportPreservesCanonicalPredicate (RatioRelation sheet) m n x

-- All-pair solver soundness, full field axioms, quadratic conic recognition
-- and source-attested Hebrew operator remain separate native obligations.
