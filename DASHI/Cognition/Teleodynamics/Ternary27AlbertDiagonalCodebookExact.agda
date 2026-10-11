module DASHI.Cognition.Teleodynamics.Ternary27AlbertDiagonalCodebookExact where

------------------------------------------------------------------------
-- CANONICAL FINITE TERNARY-27 CODEBOOK INSIDE THE RATIONAL ALBERT ALGEBRA
--
-- This is an embedding, not an identification of carriers:
--
--   (x,y,z) in {-1,0,+1}^3  |->  diag(x,y,z) in H_3(O_Q).
--
-- It preserves the natural pointwise ternary multiplication through the Albert
-- Jordan product and sends the Albert cubic norm to x*y*z.  The positive corner
-- maps to the Albert unit; the ternary origin maps to the Albert zero element.
-- The finite 27-point image is therefore a concrete codebook/submagma inside the
-- infinite 27-dimensional rational Albert algebra, not the whole representation
-- space and not an F4/E6 recognition by itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as G
import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanUnitExact as U
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O

tritToQ : SSP.SSPTrit → ℚ
tritToQ SSP.sspNegOne = - 1ℚ
tritToQ SSP.sspZero = 0ℚ
tritToQ SSP.sspPosOne = 1ℚ

tritMul : SSP.SSPTrit → SSP.SSPTrit → SSP.SSPTrit
tritMul SSP.sspNegOne SSP.sspNegOne = SSP.sspPosOne
tritMul SSP.sspNegOne SSP.sspZero = SSP.sspZero
tritMul SSP.sspNegOne SSP.sspPosOne = SSP.sspNegOne
tritMul SSP.sspZero _ = SSP.sspZero
tritMul SSP.sspPosOne right = right

tritMulToQ : (left right : SSP.SSPTrit) →
  tritToQ left * tritToQ right ≡ tritToQ (tritMul left right)
tritMulToQ SSP.sspNegOne SSP.sspNegOne = refl
tritMulToQ SSP.sspNegOne SSP.sspZero = refl
tritMulToQ SSP.sspNegOne SSP.sspPosOne = refl
tritMulToQ SSP.sspZero SSP.sspNegOne = refl
tritMulToQ SSP.sspZero SSP.sspZero = refl
tritMulToQ SSP.sspZero SSP.sspPosOne = refl
tritMulToQ SSP.sspPosOne SSP.sspNegOne = refl
tritMulToQ SSP.sspPosOne SSP.sspZero = refl
tritMulToQ SSP.sspPosOne SSP.sspPosOne = refl

tritToQInjective : ∀ {left right} →
  tritToQ left ≡ tritToQ right → left ≡ right
tritToQInjective {SSP.sspNegOne} {SSP.sspNegOne} refl = refl
tritToQInjective {SSP.sspNegOne} {SSP.sspZero} ()
tritToQInjective {SSP.sspNegOne} {SSP.sspPosOne} ()
tritToQInjective {SSP.sspZero} {SSP.sspNegOne} ()
tritToQInjective {SSP.sspZero} {SSP.sspZero} refl = refl
tritToQInjective {SSP.sspZero} {SSP.sspPosOne} ()
tritToQInjective {SSP.sspPosOne} {SSP.sspNegOne} ()
tritToQInjective {SSP.sspPosOne} {SSP.sspZero} ()
tritToQInjective {SSP.sspPosOne} {SSP.sspPosOne} refl = refl

diagAlbert : ℚ → ℚ → ℚ → A.RationalAlbert
diagAlbert a b c = A.albert a b c O.zeroO O.zeroO O.zeroO

zeroAlbert : A.RationalAlbert
zeroAlbert = diagAlbert 0ℚ 0ℚ 0ℚ

encodePoint : G.Ternary27Point → A.RationalAlbert
encodePoint (G.ternary27Point x y z) =
  diagAlbert (tritToQ x) (tritToQ y) (tritToQ z)

pointMul : G.Ternary27Point → G.Ternary27Point → G.Ternary27Point
pointMul
  (G.ternary27Point x y z)
  (G.ternary27Point x′ y′ z′) =
  G.ternary27Point (tritMul x x′) (tritMul y y′) (tritMul z z′)

encodeInjective : ∀ {left right} →
  encodePoint left ≡ encodePoint right → left ≡ right
encodeInjective
  {G.ternary27Point x y z}
  {G.ternary27Point x′ y′ z′}
  equality
  with tritToQInjective (cong A.diag1 equality)
     | tritToQInjective (cong A.diag2 equality)
     | tritToQInjective (cong A.diag3 equality)
... | refl | refl | refl = refl

diagJordanProduct : (a b c d e f : ℚ) →
  A.jordanProduct (diagAlbert a b c) (diagAlbert d e f)
  ≡ diagAlbert (a * d) (b * e) (c * f)
diagJordanProduct a b c d e f =
  U.albertExt
    (solve vars) (solve vars) (solve vars)
    refl refl refl
  where
    vars : List ℚ
    vars = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []

encodePreservesProduct : (left right : G.Ternary27Point) →
  A.jordanProduct (encodePoint left) (encodePoint right)
  ≡ encodePoint (pointMul left right)
encodePreservesProduct
  (G.ternary27Point x y z)
  (G.ternary27Point x′ y′ z′) =
  trans
    (diagJordanProduct
      (tritToQ x) (tritToQ y) (tritToQ z)
      (tritToQ x′) (tritToQ y′) (tritToQ z′))
    (U.albertExt
      (tritMulToQ x x′)
      (tritMulToQ y y′)
      (tritMulToQ z z′)
      refl refl refl)

ternaryCubicCode : G.Ternary27Point → ℚ
ternaryCubicCode (G.ternary27Point x y z) =
  tritToQ x * tritToQ y * tritToQ z

diagCubicNorm : (a b c : ℚ) →
  A.cubicNorm (diagAlbert a b c) ≡ a * b * c
diagCubicNorm a b c = solve (a ∷ b ∷ c ∷ [])

encodePreservesCubicNorm : (point : G.Ternary27Point) →
  A.cubicNorm (encodePoint point) ≡ ternaryCubicCode point
encodePreservesCubicNorm (G.ternary27Point x y z) =
  diagCubicNorm (tritToQ x) (tritToQ y) (tritToQ z)

originToZero : encodePoint G.origin ≡ zeroAlbert
originToZero = refl

positiveCornerToUnit : encodePoint G.positiveCorner ≡ A.albertUnit
positiveCornerToUnit = refl

record DiagonalCodebookBoundary : Set where
  constructor boundary
  field
    finite27CodebookEmbedded : Bool
    injectionSourceWritten : Bool
    jordanProductIntertwiningSourceWritten : Bool
    cubicNormIntertwiningSourceWritten : Bool
    positiveCornerMapsToUnit : Bool
    originMapsToZero : Bool
    imageEqualsWholeAlbertCarrier : Bool
    embeddingConstructsFullF4Action : Bool
    embeddingConstructsFullE6Action : Bool

open DiagonalCodebookBoundary public

canonicalBoundary : DiagonalCodebookBoundary
canonicalBoundary = boundary true true true true true true false false false
