module DASHI.Codec.IndexedCubeAffinePivotOverlapExact where

-- H07 selected genuine overlapping chart (0,1) -> (0,2) on
-- affine two-planes in F3^5.  Only the nonzero third-coordinate
-- coefficient of the second slope permits the change of pivots.
-- Source-written; no Agda kernel. This is a PARTIAL chart change,
-- NOT a global invertible chart on the whole codec cube.

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)
import DASHI.Codec.TriadicMaskSignFactorization as M
import DASHI.Codec.IndexedCubeMarkedAffine9Exact as A

data Nonzero : Trit → Set where
  negative : Nonzero neg
  positive : Nonzero pos

reciprocal : (t : Trit) → Nonzero t → Trit
reciprocal neg negative = neg
reciprocal zer ()
reciprocal pos positive = pos

reciprocalNonzero : (t : Trit) → (n : Nonzero t) →
  Nonzero (reciprocal t n)
reciprocalNonzero neg negative = negative
reciprocalNonzero zer ()
reciprocalNonzero pos positive = positive

-- Retain the domain witness: no zero-to-inverse coercion.
Overlap01to02 : A.Affine9 Trit → Set
Overlap01to02 plane = Nonzero (M.first (A.slopeV plane))

-- This is the same affine graph reparametrized by (u,w),
-- where w is the OLD first dependent coordinate.
-- OLD: (u,v,b+uA+vV)
-- NEW: (u, b0+u*a0+w*v0, w, ...).
-- t=1/V_0, a0=-A_0*t, b0=-b_0*t.
swapPivot : (p : A.Affine9 Trit) → Overlap01to02 p →
  A.Affine9 Trit
swapPivot (A.affine9 A.pivot01
    (M.triple a0 a1 a2)
    (M.triple v0 v1 v2)
    (M.triple b0 b1 b2)) nz =
  A.affine9 A.pivot01
    (M.triple aa
      (A.add3 a1 (A.mul3 v1 aa))
      (A.add3 a2 (A.mul3 v2 aa)))
    (M.triple t (A.mul3 v1 t) (A.mul3 v2 t))
    (M.triple bb
      (A.add3 b1 (A.mul3 v1 bb))
      (A.add3 b2 (A.mul3 v2 bb)))
  where
    t : Trit
    t = reciprocal v0 nz

    aa : Trit
    aa = A.mul3 (inv a0) t

    bb : Trit
    bb = A.mul3 (inv b0) t

-- The inverse chart has the same formula after exchanging
-- the old independent coordinate v with the new independent w.
-- In particular the reciprocal of a nonzero coefficient is nonzero.
swapPivotAdmissible :
  (p : A.Affine9 Trit) (nz : Overlap01to02 p) →
  Overlap01to02 (swapPivot p nz)
swapPivotAdmissible
  (A.affine9 A.pivot01
    (M.triple a0 a1 a2)
    (M.triple neg v1 v2)
    (M.triple b0 b1 b2)) negative = negative
swapPivotAdmissible
  (A.affine9 A.pivot01
    (M.triple a0 a1 a2)
    (M.triple pos v1 v2)
    (M.triple b0 b1 b2)) positive = positive

-- Distinct ambient coordinate ordering for the alternate pivot:
-- selected (u,w) maps to (u, v(u,w), w, z1(u,w), z2(u,w)).
record Point5Pivot02 : Set where
  constructor point5Pivot02
  field
    ambient0 ambient1 ambient2 ambient3 ambient4 : Trit

evaluate02 : A.Affine9 Trit → Trit → Trit → Point5Pivot02
evaluate02 p u w with A.evaluate p u w
... | A.point5 first second (M.triple z0 z1 z2) =
  point5Pivot02 first z0 second z1 z2

-- The original pivot01 source is the first and second ambient axes.
evaluate01 : A.Affine9 Trit → Trit → Trit → Point5Pivot02
evaluate01 p u v with A.evaluate p u v
... | A.point5 first second (M.triple z0 z1 z2) =
  point5Pivot02 first second z0 z1 z2

-- A sample with nontrivial nonzero source coefficient, where the
-- rechart is explicitly inhabited and the chart mark is retained.
sample : A.Affine9 Trit
sample = A.affine9 A.pivot01
  (M.triple zer zer zer)
  (M.triple pos zer zer)
  (M.triple zer zer zer)

sampleOverlap : Overlap01to02 sample
sampleOverlap = positive

sampleSwap : swapPivot sample sampleOverlap ≡ sample
sampleSwap = refl

-- General full-point equality and two-sided transport are NOT asserted
-- without a formal F3 arithmetic certificate. Local exhaustive SymPy
-- verifies them and explicit source-facing obligations below carry them.
record ExactPivotOverlap
    (p : A.Affine9 Trit) (nz : Overlap01to02 p) : Set where
  field
    swapBack :
      swapPivot (swapPivot p nz) (swapPivotAdmissible p nz) ≡ p

    ambientEquality :
      (u v : Trit) →
      evaluate01 p u v ≡
      evaluate02 (swapPivot p nz) u
        (A.add3 (M.first (A.offset p))
          (A.add3
            (A.mul3 u (M.first (A.slopeU p)))
            (A.mul3 v (M.first (A.slopeV p))))

-- Consumer transport across the overlap is a separate obligation.
-- In particular rotation of the original Triple can turn a nonzero
-- pivot coefficient into zero; full six-face chart gluing must
-- restrict to a rotation-stable domain (all three V entries nonzero).
