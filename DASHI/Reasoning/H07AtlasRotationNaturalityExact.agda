module DASHI.Reasoning.H07AtlasRotationNaturalityExact where

-- Literal original rotateVec/rotateMark, preserving the pivot-order sign.
-- Source-written; no kernel acceptance claimed.
open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)
import DASHI.Codec.IndexedCubeAffinePivotOverlapExact as O
import DASHI.Reasoning.H07FullAtlasSectionExact as H
import DASHI.Reasoning.H07AtlasProjectionLawsExact as P

reciprocalValue : (t : Trit) (nz : O.Nonzero t) → O.reciprocal t nz ≡ t
reciprocalValue neg O.negative = refl
reciprocalValue zer ()
reciprocalValue pos O.positive = refl

-- Nonzero F3 elements are self-reciprocal. The plain expressions below
-- are proof intermediates ONLY; the actual projection still requires Mark.
plainA plainB : H.Direction → H.Pivot → H.Vec5 → Trit
plainA L q x = H.linear2 (H.determinant L q)
  (H.at (H.second q) (H.Direction.v L)) (H.at (H.first q) (H.Direction.v L))
  (H.at (H.first q) x) (H.at (H.second q) x)
plainB L q x = H.linear2 (H.determinant L q)
  (H.at (H.first q) (H.Direction.u L)) (H.at (H.second q) (H.Direction.u L))
  (H.at (H.second q) x) (H.at (H.first q) x)

coeffAPlain : {V : H.Direction} (q : H.Mark V) (x : H.Vec5) →
  H.coefficientA q x ≡ plainA V (H.Mark.pivot q) x
coeffAPlain {H.direction u v} (H.mark q nz) x
  rewrite reciprocalValue (H.determinant (H.direction u v) q) nz = refl

coeffBPlain : {V : H.Direction} (q : H.Mark V) (x : H.Vec5) →
  H.coefficientB q x ≡ plainB V (H.Mark.pivot q) x
coeffBPlain {H.direction u v} (H.mark q nz) x
  rewrite reciprocalValue (H.determinant (H.direction u v) q) nz = refl

-- Simultaneous reversal of selected rows and determinant sign.
linear2Flip : (d a b x y : Trit) →
  H.linear2 (inv d) b a y x ≡ H.linear2 d a b x y
linear2Flip neg neg neg neg neg = refl
linear2Flip neg neg neg neg zer = refl
linear2Flip neg neg neg neg pos = refl
linear2Flip neg neg neg zer neg = refl
linear2Flip neg neg neg zer zer = refl
linear2Flip neg neg neg zer pos = refl
linear2Flip neg neg neg pos neg = refl
linear2Flip neg neg neg pos zer = refl
linear2Flip neg neg neg pos pos = refl
linear2Flip neg neg zer neg neg = refl
linear2Flip neg neg zer neg zer = refl
linear2Flip neg neg zer neg pos = refl
linear2Flip neg neg zer zer neg = refl
linear2Flip neg neg zer zer zer = refl
linear2Flip neg neg zer zer pos = refl
linear2Flip neg neg zer pos neg = refl
linear2Flip neg neg zer pos zer = refl
linear2Flip neg neg zer pos pos = refl
linear2Flip neg neg pos neg neg = refl
linear2Flip neg neg pos neg zer = refl
linear2Flip neg neg pos neg pos = refl
linear2Flip neg neg pos zer neg = refl
linear2Flip neg neg pos zer zer = refl
linear2Flip neg neg pos zer pos = refl
linear2Flip neg neg pos pos neg = refl
linear2Flip neg neg pos pos zer = refl
linear2Flip neg neg pos pos pos = refl
linear2Flip neg zer neg neg neg = refl
linear2Flip neg zer neg neg zer = refl
linear2Flip neg zer neg neg pos = refl
linear2Flip neg zer neg zer neg = refl
linear2Flip neg zer neg zer zer = refl
linear2Flip neg zer neg zer pos = refl
linear2Flip neg zer neg pos neg = refl
linear2Flip neg zer neg pos zer = refl
linear2Flip neg zer neg pos pos = refl
linear2Flip neg zer zer neg neg = refl
linear2Flip neg zer zer neg zer = refl
linear2Flip neg zer zer neg pos = refl
linear2Flip neg zer zer zer neg = refl
linear2Flip neg zer zer zer zer = refl
linear2Flip neg zer zer zer pos = refl
linear2Flip neg zer zer pos neg = refl
linear2Flip neg zer zer pos zer = refl
linear2Flip neg zer zer pos pos = refl
linear2Flip neg zer pos neg neg = refl
linear2Flip neg zer pos neg zer = refl
linear2Flip neg zer pos neg pos = refl
linear2Flip neg zer pos zer neg = refl
linear2Flip neg zer pos zer zer = refl
linear2Flip neg zer pos zer pos = refl
linear2Flip neg zer pos pos neg = refl
linear2Flip neg zer pos pos zer = refl
linear2Flip neg zer pos pos pos = refl
linear2Flip neg pos neg neg neg = refl
linear2Flip neg pos neg neg zer = refl
linear2Flip neg pos neg neg pos = refl
linear2Flip neg pos neg zer neg = refl
linear2Flip neg pos neg zer zer = refl
linear2Flip neg pos neg zer pos = refl
linear2Flip neg pos neg pos neg = refl
linear2Flip neg pos neg pos zer = refl
linear2Flip neg pos neg pos pos = refl
linear2Flip neg pos zer neg neg = refl
linear2Flip neg pos zer neg zer = refl
linear2Flip neg pos zer neg pos = refl
linear2Flip neg pos zer zer neg = refl
linear2Flip neg pos zer zer zer = refl
linear2Flip neg pos zer zer pos = refl
linear2Flip neg pos zer pos neg = refl
linear2Flip neg pos zer pos zer = refl
linear2Flip neg pos zer pos pos = refl
linear2Flip neg pos pos neg neg = refl
linear2Flip neg pos pos neg zer = refl
linear2Flip neg pos pos neg pos = refl
linear2Flip neg pos pos zer neg = refl
linear2Flip neg pos pos zer zer = refl
linear2Flip neg pos pos zer pos = refl
linear2Flip neg pos pos pos neg = refl
linear2Flip neg pos pos pos zer = refl
linear2Flip neg pos pos pos pos = refl
linear2Flip zer neg neg neg neg = refl
linear2Flip zer neg neg neg zer = refl
linear2Flip zer neg neg neg pos = refl
linear2Flip zer neg neg zer neg = refl
linear2Flip zer neg neg zer zer = refl
linear2Flip zer neg neg zer pos = refl
linear2Flip zer neg neg pos neg = refl
linear2Flip zer neg neg pos zer = refl
linear2Flip zer neg neg pos pos = refl
linear2Flip zer neg zer neg neg = refl
linear2Flip zer neg zer neg zer = refl
linear2Flip zer neg zer neg pos = refl
linear2Flip zer neg zer zer neg = refl
linear2Flip zer neg zer zer zer = refl
linear2Flip zer neg zer zer pos = refl
linear2Flip zer neg zer pos neg = refl
linear2Flip zer neg zer pos zer = refl
linear2Flip zer neg zer pos pos = refl
linear2Flip zer neg pos neg neg = refl
linear2Flip zer neg pos neg zer = refl
linear2Flip zer neg pos neg pos = refl
linear2Flip zer neg pos zer neg = refl
linear2Flip zer neg pos zer zer = refl
linear2Flip zer neg pos zer pos = refl
linear2Flip zer neg pos pos neg = refl
linear2Flip zer neg pos pos zer = refl
linear2Flip zer neg pos pos pos = refl
linear2Flip zer zer neg neg neg = refl
linear2Flip zer zer neg neg zer = refl
linear2Flip zer zer neg neg pos = refl
linear2Flip zer zer neg zer neg = refl
linear2Flip zer zer neg zer zer = refl
linear2Flip zer zer neg zer pos = refl
linear2Flip zer zer neg pos neg = refl
linear2Flip zer zer neg pos zer = refl
linear2Flip zer zer neg pos pos = refl
linear2Flip zer zer zer neg neg = refl
linear2Flip zer zer zer neg zer = refl
linear2Flip zer zer zer neg pos = refl
linear2Flip zer zer zer zer neg = refl
linear2Flip zer zer zer zer zer = refl
linear2Flip zer zer zer zer pos = refl
linear2Flip zer zer zer pos neg = refl
linear2Flip zer zer zer pos zer = refl
linear2Flip zer zer zer pos pos = refl
linear2Flip zer zer pos neg neg = refl
linear2Flip zer zer pos neg zer = refl
linear2Flip zer zer pos neg pos = refl
linear2Flip zer zer pos zer neg = refl
linear2Flip zer zer pos zer zer = refl
linear2Flip zer zer pos zer pos = refl
linear2Flip zer zer pos pos neg = refl
linear2Flip zer zer pos pos zer = refl
linear2Flip zer zer pos pos pos = refl
linear2Flip zer pos neg neg neg = refl
linear2Flip zer pos neg neg zer = refl
linear2Flip zer pos neg neg pos = refl
linear2Flip zer pos neg zer neg = refl
linear2Flip zer pos neg zer zer = refl
linear2Flip zer pos neg zer pos = refl
linear2Flip zer pos neg pos neg = refl
linear2Flip zer pos neg pos zer = refl
linear2Flip zer pos neg pos pos = refl
linear2Flip zer pos zer neg neg = refl
linear2Flip zer pos zer neg zer = refl
linear2Flip zer pos zer neg pos = refl
linear2Flip zer pos zer zer neg = refl
linear2Flip zer pos zer zer zer = refl
linear2Flip zer pos zer zer pos = refl
linear2Flip zer pos zer pos neg = refl
linear2Flip zer pos zer pos zer = refl
linear2Flip zer pos zer pos pos = refl
linear2Flip zer pos pos neg neg = refl
linear2Flip zer pos pos neg zer = refl
linear2Flip zer pos pos neg pos = refl
linear2Flip zer pos pos zer neg = refl
linear2Flip zer pos pos zer zer = refl
linear2Flip zer pos pos zer pos = refl
linear2Flip zer pos pos pos neg = refl
linear2Flip zer pos pos pos zer = refl
linear2Flip zer pos pos pos pos = refl
linear2Flip pos neg neg neg neg = refl
linear2Flip pos neg neg neg zer = refl
linear2Flip pos neg neg neg pos = refl
linear2Flip pos neg neg zer neg = refl
linear2Flip pos neg neg zer zer = refl
linear2Flip pos neg neg zer pos = refl
linear2Flip pos neg neg pos neg = refl
linear2Flip pos neg neg pos zer = refl
linear2Flip pos neg neg pos pos = refl
linear2Flip pos neg zer neg neg = refl
linear2Flip pos neg zer neg zer = refl
linear2Flip pos neg zer neg pos = refl
linear2Flip pos neg zer zer neg = refl
linear2Flip pos neg zer zer zer = refl
linear2Flip pos neg zer zer pos = refl
linear2Flip pos neg zer pos neg = refl
linear2Flip pos neg zer pos zer = refl
linear2Flip pos neg zer pos pos = refl
linear2Flip pos neg pos neg neg = refl
linear2Flip pos neg pos neg zer = refl
linear2Flip pos neg pos neg pos = refl
linear2Flip pos neg pos zer neg = refl
linear2Flip pos neg pos zer zer = refl
linear2Flip pos neg pos zer pos = refl
linear2Flip pos neg pos pos neg = refl
linear2Flip pos neg pos pos zer = refl
linear2Flip pos neg pos pos pos = refl
linear2Flip pos zer neg neg neg = refl
linear2Flip pos zer neg neg zer = refl
linear2Flip pos zer neg neg pos = refl
linear2Flip pos zer neg zer neg = refl
linear2Flip pos zer neg zer zer = refl
linear2Flip pos zer neg zer pos = refl
linear2Flip pos zer neg pos neg = refl
linear2Flip pos zer neg pos zer = refl
linear2Flip pos zer neg pos pos = refl
linear2Flip pos zer zer neg neg = refl
linear2Flip pos zer zer neg zer = refl
linear2Flip pos zer zer neg pos = refl
linear2Flip pos zer zer zer neg = refl
linear2Flip pos zer zer zer zer = refl
linear2Flip pos zer zer zer pos = refl
linear2Flip pos zer zer pos neg = refl
linear2Flip pos zer zer pos zer = refl
linear2Flip pos zer zer pos pos = refl
linear2Flip pos zer pos neg neg = refl
linear2Flip pos zer pos neg zer = refl
linear2Flip pos zer pos neg pos = refl
linear2Flip pos zer pos zer neg = refl
linear2Flip pos zer pos zer zer = refl
linear2Flip pos zer pos zer pos = refl
linear2Flip pos zer pos pos neg = refl
linear2Flip pos zer pos pos zer = refl
linear2Flip pos zer pos pos pos = refl
linear2Flip pos pos neg neg neg = refl
linear2Flip pos pos neg neg zer = refl
linear2Flip pos pos neg neg pos = refl
linear2Flip pos pos neg zer neg = refl
linear2Flip pos pos neg zer zer = refl
linear2Flip pos pos neg zer pos = refl
linear2Flip pos pos neg pos neg = refl
linear2Flip pos pos neg pos zer = refl
linear2Flip pos pos neg pos pos = refl
linear2Flip pos pos zer neg neg = refl
linear2Flip pos pos zer neg zer = refl
linear2Flip pos pos zer neg pos = refl
linear2Flip pos pos zer zer neg = refl
linear2Flip pos pos zer zer zer = refl
linear2Flip pos pos zer zer pos = refl
linear2Flip pos pos zer pos neg = refl
linear2Flip pos pos zer pos zer = refl
linear2Flip pos pos zer pos pos = refl
linear2Flip pos pos pos neg neg = refl
linear2Flip pos pos pos neg zer = refl
linear2Flip pos pos pos neg pos = refl
linear2Flip pos pos pos zer neg = refl
linear2Flip pos pos pos zer zer = refl
linear2Flip pos pos pos zer pos = refl
linear2Flip pos pos pos pos neg = refl
linear2Flip pos pos pos pos zer = refl
linear2Flip pos pos pos pos pos = refl

rotatePlainA : (p q : H.Pivot) (V : H.Direction) (x : H.Vec5) →
  plainA (H.rotateDirection p V) (H.rotatePivot p q) (H.rotateVec p x) ≡ plainA V q x
rotatePlainA H.p01 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p01 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p01 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p01 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p01 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p01 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p01 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p01 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u2 u3 v2 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p23) v3 v2 x2 x3
rotatePlainA H.p01 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u2 u4 v2 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p24) v4 v2 x2 x4
rotatePlainA H.p01 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p02 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p02 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p02 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p02 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p02 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u2 v1 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p12) v2 v1 x1 x2
rotatePlainA H.p02 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u3 v1 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p13) v3 v1 x1 x3
rotatePlainA H.p02 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u4 v1 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p14) v4 v1 x1 x4
rotatePlainA H.p02 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u2 u3 v2 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p23) v3 v2 x2 x3
rotatePlainA H.p02 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p02 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p03 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p03 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p03 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p03 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p03 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u2 v1 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p12) v2 v1 x1 x2
rotatePlainA H.p03 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u3 v1 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p13) v3 v1 x1 x3
rotatePlainA H.p03 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u4 v1 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p14) v4 v1 x1 x4
rotatePlainA H.p03 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p03 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p03 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u3 u4 v3 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p34) v4 v3 x3 x4
rotatePlainA H.p04 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p04 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p04 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p04 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p04 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u2 v1 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p12) v2 v1 x1 x2
rotatePlainA H.p04 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u3 v1 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p13) v3 v1 x1 x3
rotatePlainA H.p04 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p04 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p04 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p04 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p12 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u1 v0 v1 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p01) v1 v0 x0 x1
rotatePlainA H.p12 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u2 v0 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p02) v2 v0 x0 x2
rotatePlainA H.p12 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u3 v0 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p03) v3 v0 x0 x3
rotatePlainA H.p12 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u4 v0 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p04) v4 v0 x0 x4
rotatePlainA H.p12 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p12 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u3 v1 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p13) v3 v1 x1 x3
rotatePlainA H.p12 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p12 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u2 u3 v2 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p23) v3 v2 x2 x3
rotatePlainA H.p12 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p12 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p13 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u1 v0 v1 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p01) v1 v0 x0 x1
rotatePlainA H.p13 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u2 v0 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p02) v2 v0 x0 x2
rotatePlainA H.p13 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u3 v0 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p03) v3 v0 x0 x3
rotatePlainA H.p13 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u4 v0 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p04) v4 v0 x0 x4
rotatePlainA H.p13 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u2 v1 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p12) v2 v1 x1 x2
rotatePlainA H.p13 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p13 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p13 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p13 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p13 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u3 u4 v3 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p34) v4 v3 x3 x4
rotatePlainA H.p14 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u1 v0 v1 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p01) v1 v0 x0 x1
rotatePlainA H.p14 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u2 v0 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p02) v2 v0 x0 x2
rotatePlainA H.p14 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u3 v0 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p03) v3 v0 x0 x3
rotatePlainA H.p14 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p14 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u2 v1 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p12) v2 v1 x1 x2
rotatePlainA H.p14 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p14 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p14 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p14 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p14 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p23 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u1 v0 v1 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p01) v1 v0 x0 x1
rotatePlainA H.p23 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u2 v0 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p02) v2 v0 x0 x2
rotatePlainA H.p23 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u3 v0 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p03) v3 v0 x0 x3
rotatePlainA H.p23 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u4 v0 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p04) v4 v0 x0 x4
rotatePlainA H.p23 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p23 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p23 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p23 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p23 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u2 u4 v2 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p24) v4 v2 x2 x4
rotatePlainA H.p23 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u3 u4 v3 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p34) v4 v3 x3 x4
rotatePlainA H.p24 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u1 v0 v1 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p01) v1 v0 x0 x1
rotatePlainA H.p24 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u2 v0 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p02) v2 v0 x0 x2
rotatePlainA H.p24 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u3 v0 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p03) v3 v0 x0 x3
rotatePlainA H.p24 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p24 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p24 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p24 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p24 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u2 u3 v2 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p23) v3 v2 x2 x3
rotatePlainA H.p24 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p24 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p34 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u1 v0 v1 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p01) v1 v0 x0 x1
rotatePlainA H.p34 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u2 v0 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p02) v2 v0 x0 x2
rotatePlainA H.p34 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p34 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p34 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p34 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p34 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p34 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p34 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainA H.p34 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl

rotatePlainB : (p q : H.Pivot) (V : H.Direction) (x : H.Vec5) →
  plainB (H.rotateDirection p V) (H.rotatePivot p q) (H.rotateVec p x) ≡ plainB V q x
rotatePlainB H.p01 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p01 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p01 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p01 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p01 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p01 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p01 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p01 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u2 u3 v2 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p23) u2 u3 x3 x2
rotatePlainB H.p01 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u2 u4 v2 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p24) u2 u4 x4 x2
rotatePlainB H.p01 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p02 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p02 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p02 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p02 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p02 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u2 v1 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p12) u1 u2 x2 x1
rotatePlainB H.p02 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u3 v1 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p13) u1 u3 x3 x1
rotatePlainB H.p02 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u4 v1 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p14) u1 u4 x4 x1
rotatePlainB H.p02 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u2 u3 v2 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p23) u2 u3 x3 x2
rotatePlainB H.p02 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p02 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p03 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p03 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p03 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p03 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p03 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u2 v1 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p12) u1 u2 x2 x1
rotatePlainB H.p03 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u3 v1 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p13) u1 u3 x3 x1
rotatePlainB H.p03 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u4 v1 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p14) u1 u4 x4 x1
rotatePlainB H.p03 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p03 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p03 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u3 u4 v3 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p34) u3 u4 x4 x3
rotatePlainB H.p04 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p04 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p04 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p04 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p04 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u2 v1 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p12) u1 u2 x2 x1
rotatePlainB H.p04 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u3 v1 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p13) u1 u3 x3 x1
rotatePlainB H.p04 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p04 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p04 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p04 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p12 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u1 v0 v1 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p01) u0 u1 x1 x0
rotatePlainB H.p12 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u2 v0 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p02) u0 u2 x2 x0
rotatePlainB H.p12 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u3 v0 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p03) u0 u3 x3 x0
rotatePlainB H.p12 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u4 v0 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p04) u0 u4 x4 x0
rotatePlainB H.p12 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p12 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u3 v1 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p13) u1 u3 x3 x1
rotatePlainB H.p12 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p12 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u2 u3 v2 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p23) u2 u3 x3 x2
rotatePlainB H.p12 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p12 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p13 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u1 v0 v1 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p01) u0 u1 x1 x0
rotatePlainB H.p13 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u2 v0 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p02) u0 u2 x2 x0
rotatePlainB H.p13 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u3 v0 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p03) u0 u3 x3 x0
rotatePlainB H.p13 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u4 v0 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p04) u0 u4 x4 x0
rotatePlainB H.p13 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u2 v1 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p12) u1 u2 x2 x1
rotatePlainB H.p13 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p13 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p13 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p13 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p13 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u3 u4 v3 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p34) u3 u4 x4 x3
rotatePlainB H.p14 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u1 v0 v1 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p01) u0 u1 x1 x0
rotatePlainB H.p14 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u2 v0 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p02) u0 u2 x2 x0
rotatePlainB H.p14 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u3 v0 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p03) u0 u3 x3 x0
rotatePlainB H.p14 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p14 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u1 u2 v1 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p12) u1 u2 x2 x1
rotatePlainB H.p14 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p14 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p14 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p14 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p14 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p23 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u1 v0 v1 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p01) u0 u1 x1 x0
rotatePlainB H.p23 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u2 v0 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p02) u0 u2 x2 x0
rotatePlainB H.p23 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u3 v0 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p03) u0 u3 x3 x0
rotatePlainB H.p23 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u4 v0 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p04) u0 u4 x4 x0
rotatePlainB H.p23 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p23 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p23 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p23 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p23 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u2 u4 v2 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p24) u2 u4 x4 x2
rotatePlainB H.p23 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u3 u4 v3 v4 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p34) u3 u4 x4 x3
rotatePlainB H.p24 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u1 v0 v1 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p01) u0 u1 x1 x0
rotatePlainB H.p24 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u2 v0 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p02) u0 u2 x2 x0
rotatePlainB H.p24 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u3 v0 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p03) u0 u3 x3 x0
rotatePlainB H.p24 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p24 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p24 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p24 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p24 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u2 u3 v2 v3 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p23) u2 u3 x3 x2
rotatePlainB H.p24 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p24 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p34 H.p01 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u1 v0 v1 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p01) u0 u1 x1 x0
rotatePlainB H.p34 H.p02 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4)
  rewrite H.detSwap u0 u2 v0 v2 =
    linear2Flip (H.determinant (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) H.p02) u0 u2 x2 x0
rotatePlainB H.p34 H.p03 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p34 H.p04 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p34 H.p12 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p34 H.p13 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p34 H.p14 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p34 H.p23 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p34 H.p24 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl
rotatePlainB H.p34 H.p34 (H.direction (H.vec5 u0 u1 u2 u3 u4) (H.vec5 v0 v1 v2 v3 v4)) (H.vec5 x0 x1 x2 x3 x4) = refl

rotateCoeffA : (p : H.Pivot) {V : H.Direction} (q : H.Mark V) (x : H.Vec5) →
  H.coefficientA (H.rotateMark p q) (H.rotateVec p x) ≡ H.coefficientA q x
rotateCoeffA p {V} (H.mark q nz) x =
  trans (coeffAPlain (H.rotateMark p (H.mark q nz)) (H.rotateVec p x))
    (trans (rotatePlainA p q V x) (sym (coeffAPlain (H.mark q nz) x)))

rotateCoeffB : (p : H.Pivot) {V : H.Direction} (q : H.Mark V) (x : H.Vec5) →
  H.coefficientB (H.rotateMark p q) (H.rotateVec p x) ≡ H.coefficientB q x
rotateCoeffB p {V} (H.mark q nz) x =
  trans (coeffBPlain (H.rotateMark p (H.mark q nz)) (H.rotateVec p x))
    (trans (rotatePlainB p q V x) (sym (coeffBPlain (H.mark q nz) x)))

rotateAdd : (p : H.Pivot) (x y : H.Vec5) →
  H.rotateVec p (H.add x y) ≡ H.add (H.rotateVec p x) (H.rotateVec p y)
rotateAdd H.p01 (H.vec5 x0 x1 x2 x3 x4) (H.vec5 y0 y1 y2 y3 y4) = refl
rotateAdd H.p02 (H.vec5 x0 x1 x2 x3 x4) (H.vec5 y0 y1 y2 y3 y4) = refl
rotateAdd H.p03 (H.vec5 x0 x1 x2 x3 x4) (H.vec5 y0 y1 y2 y3 y4) = refl
rotateAdd H.p04 (H.vec5 x0 x1 x2 x3 x4) (H.vec5 y0 y1 y2 y3 y4) = refl
rotateAdd H.p12 (H.vec5 x0 x1 x2 x3 x4) (H.vec5 y0 y1 y2 y3 y4) = refl
rotateAdd H.p13 (H.vec5 x0 x1 x2 x3 x4) (H.vec5 y0 y1 y2 y3 y4) = refl
rotateAdd H.p14 (H.vec5 x0 x1 x2 x3 x4) (H.vec5 y0 y1 y2 y3 y4) = refl
rotateAdd H.p23 (H.vec5 x0 x1 x2 x3 x4) (H.vec5 y0 y1 y2 y3 y4) = refl
rotateAdd H.p24 (H.vec5 x0 x1 x2 x3 x4) (H.vec5 y0 y1 y2 y3 y4) = refl
rotateAdd H.p34 (H.vec5 x0 x1 x2 x3 x4) (H.vec5 y0 y1 y2 y3 y4) = refl

rotateScale : (p : H.Pivot) (n : Trit) (x : H.Vec5) →
  H.rotateVec p (H.scale n x) ≡ H.scale n (H.rotateVec p x)
rotateScale H.p01 n (H.vec5 x0 x1 x2 x3 x4) = refl
rotateScale H.p02 n (H.vec5 x0 x1 x2 x3 x4) = refl
rotateScale H.p03 n (H.vec5 x0 x1 x2 x3 x4) = refl
rotateScale H.p04 n (H.vec5 x0 x1 x2 x3 x4) = refl
rotateScale H.p12 n (H.vec5 x0 x1 x2 x3 x4) = refl
rotateScale H.p13 n (H.vec5 x0 x1 x2 x3 x4) = refl
rotateScale H.p14 n (H.vec5 x0 x1 x2 x3 x4) = refl
rotateScale H.p23 n (H.vec5 x0 x1 x2 x3 x4) = refl
rotateScale H.p24 n (H.vec5 x0 x1 x2 x3 x4) = refl
rotateScale H.p34 n (H.vec5 x0 x1 x2 x3 x4) = refl

rotateSub : (p : H.Pivot) (x y : H.Vec5) →
  H.rotateVec p (H.sub x y) ≡ H.sub (H.rotateVec p x) (H.rotateVec p y)
rotateSub p x y = trans (rotateAdd p x (H.scale neg y))
  (cong (H.add (H.rotateVec p x)) (rotateScale p neg y))

rotateProject : (p : H.Pivot) {V : H.Direction} (q : H.Mark V) (x : H.Vec5) →
  H.project (H.rotateMark p q) (H.rotateVec p x) ≡ H.rotateVec p (H.project q x)
rotateProject p {H.direction u v} q x
  rewrite rotateCoeffA p q x | rotateCoeffB p q x =
  sym (trans (rotateSub p x
      (H.add (H.scale (H.coefficientA q x) u) (H.scale (H.coefficientB q x) v)))
    (cong (H.sub (H.rotateVec p x))
      (trans (rotateAdd p (H.scale (H.coefficientA q x) u)
                         (H.scale (H.coefficientB q x) v))
        (cong₂ H.add (rotateScale p (H.coefficientA q x) u)
                     (rotateScale p (H.coefficientB q x) v)))))

rotateIndicator : (p q : H.Pivot) →
  H.indicator (H.rotatePivot p q) ≡ H.rotateVec p (H.indicator q)
rotateIndicator H.p01 H.p01 = refl
rotateIndicator H.p01 H.p02 = refl
rotateIndicator H.p01 H.p03 = refl
rotateIndicator H.p01 H.p04 = refl
rotateIndicator H.p01 H.p12 = refl
rotateIndicator H.p01 H.p13 = refl
rotateIndicator H.p01 H.p14 = refl
rotateIndicator H.p01 H.p23 = refl
rotateIndicator H.p01 H.p24 = refl
rotateIndicator H.p01 H.p34 = refl
rotateIndicator H.p02 H.p01 = refl
rotateIndicator H.p02 H.p02 = refl
rotateIndicator H.p02 H.p03 = refl
rotateIndicator H.p02 H.p04 = refl
rotateIndicator H.p02 H.p12 = refl
rotateIndicator H.p02 H.p13 = refl
rotateIndicator H.p02 H.p14 = refl
rotateIndicator H.p02 H.p23 = refl
rotateIndicator H.p02 H.p24 = refl
rotateIndicator H.p02 H.p34 = refl
rotateIndicator H.p03 H.p01 = refl
rotateIndicator H.p03 H.p02 = refl
rotateIndicator H.p03 H.p03 = refl
rotateIndicator H.p03 H.p04 = refl
rotateIndicator H.p03 H.p12 = refl
rotateIndicator H.p03 H.p13 = refl
rotateIndicator H.p03 H.p14 = refl
rotateIndicator H.p03 H.p23 = refl
rotateIndicator H.p03 H.p24 = refl
rotateIndicator H.p03 H.p34 = refl
rotateIndicator H.p04 H.p01 = refl
rotateIndicator H.p04 H.p02 = refl
rotateIndicator H.p04 H.p03 = refl
rotateIndicator H.p04 H.p04 = refl
rotateIndicator H.p04 H.p12 = refl
rotateIndicator H.p04 H.p13 = refl
rotateIndicator H.p04 H.p14 = refl
rotateIndicator H.p04 H.p23 = refl
rotateIndicator H.p04 H.p24 = refl
rotateIndicator H.p04 H.p34 = refl
rotateIndicator H.p12 H.p01 = refl
rotateIndicator H.p12 H.p02 = refl
rotateIndicator H.p12 H.p03 = refl
rotateIndicator H.p12 H.p04 = refl
rotateIndicator H.p12 H.p12 = refl
rotateIndicator H.p12 H.p13 = refl
rotateIndicator H.p12 H.p14 = refl
rotateIndicator H.p12 H.p23 = refl
rotateIndicator H.p12 H.p24 = refl
rotateIndicator H.p12 H.p34 = refl
rotateIndicator H.p13 H.p01 = refl
rotateIndicator H.p13 H.p02 = refl
rotateIndicator H.p13 H.p03 = refl
rotateIndicator H.p13 H.p04 = refl
rotateIndicator H.p13 H.p12 = refl
rotateIndicator H.p13 H.p13 = refl
rotateIndicator H.p13 H.p14 = refl
rotateIndicator H.p13 H.p23 = refl
rotateIndicator H.p13 H.p24 = refl
rotateIndicator H.p13 H.p34 = refl
rotateIndicator H.p14 H.p01 = refl
rotateIndicator H.p14 H.p02 = refl
rotateIndicator H.p14 H.p03 = refl
rotateIndicator H.p14 H.p04 = refl
rotateIndicator H.p14 H.p12 = refl
rotateIndicator H.p14 H.p13 = refl
rotateIndicator H.p14 H.p14 = refl
rotateIndicator H.p14 H.p23 = refl
rotateIndicator H.p14 H.p24 = refl
rotateIndicator H.p14 H.p34 = refl
rotateIndicator H.p23 H.p01 = refl
rotateIndicator H.p23 H.p02 = refl
rotateIndicator H.p23 H.p03 = refl
rotateIndicator H.p23 H.p04 = refl
rotateIndicator H.p23 H.p12 = refl
rotateIndicator H.p23 H.p13 = refl
rotateIndicator H.p23 H.p14 = refl
rotateIndicator H.p23 H.p23 = refl
rotateIndicator H.p23 H.p24 = refl
rotateIndicator H.p23 H.p34 = refl
rotateIndicator H.p24 H.p01 = refl
rotateIndicator H.p24 H.p02 = refl
rotateIndicator H.p24 H.p03 = refl
rotateIndicator H.p24 H.p04 = refl
rotateIndicator H.p24 H.p12 = refl
rotateIndicator H.p24 H.p13 = refl
rotateIndicator H.p24 H.p14 = refl
rotateIndicator H.p24 H.p23 = refl
rotateIndicator H.p24 H.p24 = refl
rotateIndicator H.p24 H.p34 = refl
rotateIndicator H.p34 H.p01 = refl
rotateIndicator H.p34 H.p02 = refl
rotateIndicator H.p34 H.p03 = refl
rotateIndicator H.p34 H.p04 = refl
rotateIndicator H.p34 H.p12 = refl
rotateIndicator H.p34 H.p13 = refl
rotateIndicator H.p34 H.p14 = refl
rotateIndicator H.p34 H.p23 = refl
rotateIndicator H.p34 H.p24 = refl
rotateIndicator H.p34 H.p34 = refl

rotateW : (p : H.Pivot) {V : H.Direction} (q : H.Mark V) →
  H.w (H.rotateMark p q) ≡ H.rotateVec p (H.w q)
rotateW p (H.mark q nz) = rotateIndicator p q

rotateShift : (p : H.Pivot) {V : H.Direction} (q : H.Mark V) (x : H.Vec5) (n : Trit) →
  H.rotateVec p (H.add x (H.scale n (H.w q))) ≡
  H.add (H.rotateVec p x) (H.scale n (H.w (H.rotateMark p q)))
rotateShift p q x n = trans (rotateAdd p x (H.scale n (H.w q)))
  (cong (H.add (H.rotateVec p x))
    (trans (rotateScale p n (H.w q)) (cong (H.scale n) (sym (rotateW p q)))))

rotateRaw : (p : H.Pivot) {V : H.Direction} (q : H.Mark V) (x : H.Vec5) (n : Trit) →
  H.raw (H.rotateMark p q) (H.rotateVec p x) n ≡ H.rotateVec p (H.raw q x n)
rotateRaw p q x n = trans
  (cong (H.project (H.rotateMark p q)) (sym (rotateShift p q x n)))
  (rotateProject p q (H.add x (H.scale n (H.w q))))

rotateActual : (p : H.Pivot) {V : H.Direction} (a q : H.Mark V) (x : H.Vec5) (n : Trit) →
  H.actual (H.rotateMark p a) (H.rotateMark p q) (H.rotateVec p x) n ≡
  H.rotateVec p (H.actual a q x n)
rotateActual p a q x n = trans
  (cong (H.project (H.rotateMark p q)) (sym (rotateShift p a x n)))
  (rotateProject p q (H.add x (H.scale n (H.w a))))

rotateDifference : (p : H.Pivot) {V : H.Direction} (a q : H.Mark V) →
  H.rotateVec p (H.sub (H.w a) (H.w q)) ≡
  H.sub (H.w (H.rotateMark p a)) (H.w (H.rotateMark p q))
rotateDifference p a q = trans (rotateSub p (H.w a) (H.w q))
  (cong₂ H.sub (sym (rotateW p a)) (sym (rotateW p q)))

rotateCorrection : (p : H.Pivot) {V : H.Direction} (a q : H.Mark V) (n : Trit) →
  H.correction (H.rotateMark p a) (H.rotateMark p q) n ≡
  H.rotateVec p (H.correction a q n)
rotateCorrection p a q n = trans (cong (H.scale n)
  (trans (cong (H.project (H.rotateMark p q)) (sym (rotateDifference p a q)))
    (rotateProject p q (H.sub (H.w a) (H.w q)))))
  (sym (rotateScale p n (H.project q (H.sub (H.w a) (H.w q)))))

rotateRestriction : (p : H.Pivot) {V : H.Direction} (a v q : H.Mark V)
  (x : H.Vec5) (n : Trit) →
  H.project (H.rotateMark p q)
    (H.add (H.raw (H.rotateMark p v) (H.rotateVec p x) n)
      (H.correction (H.rotateMark p a) (H.rotateMark p v) n))
  ≡ H.rotateVec p (H.project q (H.add (H.raw v x n) (H.correction a v n)))
rotateRestriction p a v q x n =
  trans (cong (H.project (H.rotateMark p q))
    (trans (cong₂ H.add (rotateRaw p v x n) (rotateCorrection p a v n))
      (sym (rotateAdd p (H.raw v x n) (H.correction a v n)))))
    (rotateProject p q (H.add (H.raw v x n) (H.correction a v n)))

-- The actual source mark, signed correction and independently retained
-- winding are transported; no fixed-target inversion or erased residual.
