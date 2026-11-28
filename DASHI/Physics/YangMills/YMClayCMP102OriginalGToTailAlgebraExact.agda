module DASHI.Physics.YangMills.YMClayCMP102OriginalGToTailAlgebraExact where

------------------------------------------------------------------------
-- Section 31: exact original CMP102 finite-G -> finite-Cauchy-tail
-- algebra, with one EXPLICIT original shifted row-normal-form input.
-- The input is the still-open Fin(suc count) reindexing from the
-- actual original shifted Cauchy endpoint source. It is NOT an
-- independently postulated identity or an assumed G=0.
--
-- All remaining algebra, including the otherwise easy-to-drop last
-- B term, is source-written on the original represented Bishop real.
-- Pinned Agda 2.9 acceptance remains pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (1ℚᵘ; 0ℚᵘ; _/_)
import Real as R
import RealProperties as P

import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original
import DASHI.Physics.YangMills.YMClayCMP102OriginalEndpointCauchyShiftExact as CMP102
import DASHI.Physics.YangMills.YMClayCMP102OriginalSignedTriangleZeroExact as Signed
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteCauchyWingBoundsExact as Wing
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailGeometryExact as Tail
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import Data.Nat.Base as N

infixl 6 _⊞_ _⊟_
infixl 7 _⊠_
_⊞_ _⊟_ _⊠_ : R.ℝ → R.ℝ → R.ℝ
_⊞_ = R._+_
_⊟_ = R._-_
_⊠_ = R._*_

-- All these terms are exactly original CMP109 prefixes and Cauchy
-- triangles evaluated at X, not an independently chosen power series.
originalALowTriangle : R.ℝ → Nat → R.ℝ
originalALowTriangle X count =
  Row.trianglePartial (Wing.aTerm X) (Wing.aTerm X)
    (count N.∸ 1)

originalBLowTriangle : R.ℝ → Nat → R.ℝ
originalBLowTriangle X count =
  Row.trianglePartial (Wing.bTerm X) (Wing.bTerm X)
    (count N.∸ 2)

originalLastB : R.ℝ → Nat → R.ℝ
originalLastB X n = Wing.bTerm X n

-- The EXACT right-hand source form of the truncated shifted rows.
-- Its equality with Signed.originalSignedTriangle is one precise
-- remaining original Fin triangle reindexing proof, not an axiom.
originalShiftedRowNormal : R.ℝ → Nat → R.ℝ
originalShiftedRowNormal X n =
  let count = suc n
      A = Original.aPrefix X count
      B = Original.bPrefix X count
      TA = originalALowTriangle X count
      TB = originalBLowTriangle X count
      last = originalLastB X n
  in
  (((R.1ℝ ⊟ (CMP102.two ⊠ A)) ⊟ (X ⊠ TA))
    ⊞ ((CMP102.two ⊠ X) ⊠ (B ⊟ last)))
    ⊞ ((X ⊠ X) ⊠ TB)

-- Original finite residual written BEFORE expanding squares into
-- rectangles. This is exactly the source tail algebra of the true
-- five-term CMP102 G-prefix expression.
originalRawSquareWingTail : R.ℝ → Nat → R.ℝ
originalRawSquareWingTail X n =
  let count = suc n
      A = Original.aPrefix X count
      B = Original.bPrefix X count
      TA = originalALowTriangle X count
      TB = originalBLowTriangle X count
      last = originalLastB X n
  in
  ((R.- (X ⊠ ((A ⊠ A) ⊟ TA)))
    ⊞ ((CMP102.two ⊠ X) ⊠ last))
    ⊞ ((X ⊠ X) ⊠ ((B ⊠ B) ⊟ TB))

-- Exact finite original source G=shifted row+raw wings algebra.
-- NO assumptions on X, no analytic limit, no source G-zero premise.
originalGIsSourceNormalPlusRawWings : ∀ X n →
  R._≃_
    (Original.originalGPrefix X (suc n))
    ((originalShiftedRowNormal X n) ⊞
     (originalRawSquareWingTail X n))
originalGIsSourceNormalPlusRawWings X n =
  let count = suc n
      A = Original.aPrefix X count
      B = Original.bPrefix X count
      TA = originalALowTriangle X count
      TB = originalBLowTriangle X count
      last = originalLastB X n
      open P.ℝ-Solver
  in
  solve 6
    (λ x a b ta tb last →
      (((Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ a))
         ⊖ (x ⊗ (a ⊗ a)))
         ⊕ ((Κ (+ 2 / 1) ⊗ x) ⊗ b)
         ⊕ ((x ⊗ x) ⊗ (b ⊗ b))
      ⊜
      (((Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ a))
         ⊖ (x ⊗ ta))
         ⊕ ((Κ (+ 2 / 1) ⊗ x) ⊗ (b ⊖ last))
         ⊕ ((x ⊗ x) ⊗ tb))
       ⊕
      (((⊝ (x ⊗ ((a ⊗ a) ⊖ ta)))
         ⊕ ((Κ (+ 2 / 1) ⊗ x) ⊗ last))
         ⊕ ((x ⊗ x) ⊗ ((b ⊗ b) ⊖ tb)))))
    P.≃-refl X A B TA TB last

-- The SOURCE Fin-index lemma still required by original CMP102:
-- the previously-proved shifted row coefficient sum equals the
-- actual truncated original A/B triangle normal form.
OriginalShiftedRowFinReindex : R.ℝ → Nat → Set
OriginalShiftedRowFinReindex X n =
  R._≃_
    (Signed.originalSignedTriangle X (suc n))
    (originalShiftedRowNormal X n)

-- This theorem reduces the original ALL-degree G-to-wing equality
-- to that one named source-level reindexing, with no hidden premise.
originalGIsActualSignedTrianglePlusRawWings :
  ∀ X n → OriginalShiftedRowFinReindex X n →
  R._≃_
    (Original.originalGPrefix X (suc n))
    ((Signed.originalSignedTriangle X (suc n)) ⊞
     (originalRawSquareWingTail X n))
originalGIsActualSignedTrianglePlusRawWings X n hrow =
  P.≃-trans
    (originalGIsSourceNormalPlusRawWings X n)
    (P.+-cong (P.≃-symm hrow) P.≃-refl)

-- Consumes the ALREADY source-written shifted Cauchy cancellation,
-- giving a true original finite G = raw source wing conditional
-- ONLY on the original row reindex equality above.
originalGIsRawWingsFromOriginalFinReindex :
  ∀ X n → OriginalShiftedRowFinReindex X n →
  R._≃_
    (Original.originalGPrefix X (suc n))
    (originalRawSquareWingTail X n)
originalGIsRawWingsFromOriginalFinReindex X n hrow =
  P.≃-trans
    (originalGIsActualSignedTrianglePlusRawWings X n hrow)
    (P.≃-trans
      (P.+-cong (Signed.originalSignedTriangleZero X (suc n))
        P.≃-refl)
      (let open P.ℝ-Solver
       in solve 1
            (λ tail → Κ 0ℚᵘ ⊕ tail ⊜ tail)
            P.≃-refl (originalRawSquareWingTail X n)))


-- The two original finite squares are now transported to the actual
-- two original Bishop Cauchy rectangles. Thus the raw square
-- difference is literally the source `originalAWing/originalBWing`.
-- This does not require a new analytic argument or limit.
originalRawSquareWingsAreActualCauchyTail :
  ∀ X n →
  R._≃_
    (originalRawSquareWingTail X n)
    (Tail.originalSignedCauchyTail X n)
originalRawSquareWingsAreActualCauchyTail X n =
  let
    count = suc n
    A = Original.aPrefix X count
    B = Original.bPrefix X count
    TA = originalALowTriangle X count
    TB = originalBLowTriangle X count
    hAWing :
      R._≃_
        ((A ⊠ A) ⊟ TA)
        (Tail.originalAWing X count)
    hAWing =
      P.+-cong
        (Wing.originalASquareIsOriginalRectangle X count)
        (P.-‿cong P.≃-refl)
    hBWing :
      R._≃_
        ((B ⊠ B) ⊟ TB)
        (Tail.originalBWing X count)
    hBWing =
      P.+-cong
        (Wing.originalBSquareIsOriginalRectangle X count)
        (P.-‿cong P.≃-refl)
  in
  P.+-cong
    (P.+-cong
      (P.-‿cong (P.*-congˡ hAWing))
      P.≃-refl)
    (P.*-congˡ hBWing)

-- Original G_count -> EXACT ORIGINAL signed Cauchy source tail:
-- one remaining owner-specific finite row reindex witness and all
-- other data strictly from original Agda finite Cauchy constructors.
originalGIsOriginalSignedCauchyTail :
  ∀ X n → OriginalShiftedRowFinReindex X n →
  R._≃_
    (Original.originalGPrefix X (suc n))
    (Tail.originalSignedCauchyTail X n)
originalGIsOriginalSignedCauchyTail X n hrow =
  P.≃-trans
    (originalGIsRawWingsFromOriginalFinReindex X n hrow)
    (originalRawSquareWingsAreActualCauchyTail X n)
