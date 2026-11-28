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
            (A.mul3 v (M.first (A.slopeV p)))))

-- Consumer transport across the overlap is a separate obligation.
-- In particular rotation of the original Triple can turn a nonzero
-- pivot coefficient into zero; full six-face chart gluing must
-- restrict to a rotation-stable domain (all three V entries nonzero).


-- Componentwise proof of the ORIGINAL partial overlap, allowing zero in
-- either remaining slope. Finite scalar tables, not a new chart or field.
open import Relation.Binary.PropositionalEquality using (sym)

overlapLeadTwice : (s a : Trit) → Nonzero s → A.mul3 (inv (A.mul3 (inv a) s)) s ≡ a
overlapLeadTwice neg neg negative = refl
overlapLeadTwice neg zer negative = refl
overlapLeadTwice neg pos negative = refl
overlapLeadTwice pos neg positive = refl
overlapLeadTwice pos zer positive = refl
overlapLeadTwice pos pos positive = refl
overlapLeadTwice zer _ ()

overlapSlopeTwice : (s h : Trit) → Nonzero s → A.mul3 (A.mul3 h s) s ≡ h
overlapSlopeTwice neg neg negative = refl
overlapSlopeTwice neg zer negative = refl
overlapSlopeTwice neg pos negative = refl
overlapSlopeTwice pos neg positive = refl
overlapSlopeTwice pos zer positive = refl
overlapSlopeTwice pos pos positive = refl
overlapSlopeTwice zer _ ()

overlapTailTwice : (s h a x : Trit) → Nonzero s → A.add3 (A.add3 x (A.mul3 h (A.mul3 (inv a) s))) (A.mul3 (A.mul3 h s) a) ≡ x
overlapTailTwice neg neg neg neg negative = refl
overlapTailTwice neg neg neg zer negative = refl
overlapTailTwice neg neg neg pos negative = refl
overlapTailTwice neg neg zer neg negative = refl
overlapTailTwice neg neg zer zer negative = refl
overlapTailTwice neg neg zer pos negative = refl
overlapTailTwice neg neg pos neg negative = refl
overlapTailTwice neg neg pos zer negative = refl
overlapTailTwice neg neg pos pos negative = refl
overlapTailTwice neg zer neg neg negative = refl
overlapTailTwice neg zer neg zer negative = refl
overlapTailTwice neg zer neg pos negative = refl
overlapTailTwice neg zer zer neg negative = refl
overlapTailTwice neg zer zer zer negative = refl
overlapTailTwice neg zer zer pos negative = refl
overlapTailTwice neg zer pos neg negative = refl
overlapTailTwice neg zer pos zer negative = refl
overlapTailTwice neg zer pos pos negative = refl
overlapTailTwice neg pos neg neg negative = refl
overlapTailTwice neg pos neg zer negative = refl
overlapTailTwice neg pos neg pos negative = refl
overlapTailTwice neg pos zer neg negative = refl
overlapTailTwice neg pos zer zer negative = refl
overlapTailTwice neg pos zer pos negative = refl
overlapTailTwice neg pos pos neg negative = refl
overlapTailTwice neg pos pos zer negative = refl
overlapTailTwice neg pos pos pos negative = refl
overlapTailTwice pos neg neg neg positive = refl
overlapTailTwice pos neg neg zer positive = refl
overlapTailTwice pos neg neg pos positive = refl
overlapTailTwice pos neg zer neg positive = refl
overlapTailTwice pos neg zer zer positive = refl
overlapTailTwice pos neg zer pos positive = refl
overlapTailTwice pos neg pos neg positive = refl
overlapTailTwice pos neg pos zer positive = refl
overlapTailTwice pos neg pos pos positive = refl
overlapTailTwice pos zer neg neg positive = refl
overlapTailTwice pos zer neg zer positive = refl
overlapTailTwice pos zer neg pos positive = refl
overlapTailTwice pos zer zer neg positive = refl
overlapTailTwice pos zer zer zer positive = refl
overlapTailTwice pos zer zer pos positive = refl
overlapTailTwice pos zer pos neg positive = refl
overlapTailTwice pos zer pos zer positive = refl
overlapTailTwice pos zer pos pos positive = refl
overlapTailTwice pos pos neg neg positive = refl
overlapTailTwice pos pos neg zer positive = refl
overlapTailTwice pos pos neg pos positive = refl
overlapTailTwice pos pos zer neg positive = refl
overlapTailTwice pos pos zer zer positive = refl
overlapTailTwice pos pos zer pos positive = refl
overlapTailTwice pos pos pos neg positive = refl
overlapTailTwice pos pos pos zer positive = refl
overlapTailTwice pos pos pos pos positive = refl
overlapTailTwice zer _ _ _ ()

overlapLeadEval : (s a b u v : Trit) → Nonzero s → A.add3 (A.mul3 (inv b) s) (A.add3 (A.mul3 u (A.mul3 (inv a) s)) (A.mul3 (A.add3 b (A.add3 (A.mul3 u a) (A.mul3 v s))) s)) ≡ v
overlapLeadEval neg neg neg neg neg negative = refl
overlapLeadEval neg neg neg neg zer negative = refl
overlapLeadEval neg neg neg neg pos negative = refl
overlapLeadEval neg neg neg zer neg negative = refl
overlapLeadEval neg neg neg zer zer negative = refl
overlapLeadEval neg neg neg zer pos negative = refl
overlapLeadEval neg neg neg pos neg negative = refl
overlapLeadEval neg neg neg pos zer negative = refl
overlapLeadEval neg neg neg pos pos negative = refl
overlapLeadEval neg neg zer neg neg negative = refl
overlapLeadEval neg neg zer neg zer negative = refl
overlapLeadEval neg neg zer neg pos negative = refl
overlapLeadEval neg neg zer zer neg negative = refl
overlapLeadEval neg neg zer zer zer negative = refl
overlapLeadEval neg neg zer zer pos negative = refl
overlapLeadEval neg neg zer pos neg negative = refl
overlapLeadEval neg neg zer pos zer negative = refl
overlapLeadEval neg neg zer pos pos negative = refl
overlapLeadEval neg neg pos neg neg negative = refl
overlapLeadEval neg neg pos neg zer negative = refl
overlapLeadEval neg neg pos neg pos negative = refl
overlapLeadEval neg neg pos zer neg negative = refl
overlapLeadEval neg neg pos zer zer negative = refl
overlapLeadEval neg neg pos zer pos negative = refl
overlapLeadEval neg neg pos pos neg negative = refl
overlapLeadEval neg neg pos pos zer negative = refl
overlapLeadEval neg neg pos pos pos negative = refl
overlapLeadEval neg zer neg neg neg negative = refl
overlapLeadEval neg zer neg neg zer negative = refl
overlapLeadEval neg zer neg neg pos negative = refl
overlapLeadEval neg zer neg zer neg negative = refl
overlapLeadEval neg zer neg zer zer negative = refl
overlapLeadEval neg zer neg zer pos negative = refl
overlapLeadEval neg zer neg pos neg negative = refl
overlapLeadEval neg zer neg pos zer negative = refl
overlapLeadEval neg zer neg pos pos negative = refl
overlapLeadEval neg zer zer neg neg negative = refl
overlapLeadEval neg zer zer neg zer negative = refl
overlapLeadEval neg zer zer neg pos negative = refl
overlapLeadEval neg zer zer zer neg negative = refl
overlapLeadEval neg zer zer zer zer negative = refl
overlapLeadEval neg zer zer zer pos negative = refl
overlapLeadEval neg zer zer pos neg negative = refl
overlapLeadEval neg zer zer pos zer negative = refl
overlapLeadEval neg zer zer pos pos negative = refl
overlapLeadEval neg zer pos neg neg negative = refl
overlapLeadEval neg zer pos neg zer negative = refl
overlapLeadEval neg zer pos neg pos negative = refl
overlapLeadEval neg zer pos zer neg negative = refl
overlapLeadEval neg zer pos zer zer negative = refl
overlapLeadEval neg zer pos zer pos negative = refl
overlapLeadEval neg zer pos pos neg negative = refl
overlapLeadEval neg zer pos pos zer negative = refl
overlapLeadEval neg zer pos pos pos negative = refl
overlapLeadEval neg pos neg neg neg negative = refl
overlapLeadEval neg pos neg neg zer negative = refl
overlapLeadEval neg pos neg neg pos negative = refl
overlapLeadEval neg pos neg zer neg negative = refl
overlapLeadEval neg pos neg zer zer negative = refl
overlapLeadEval neg pos neg zer pos negative = refl
overlapLeadEval neg pos neg pos neg negative = refl
overlapLeadEval neg pos neg pos zer negative = refl
overlapLeadEval neg pos neg pos pos negative = refl
overlapLeadEval neg pos zer neg neg negative = refl
overlapLeadEval neg pos zer neg zer negative = refl
overlapLeadEval neg pos zer neg pos negative = refl
overlapLeadEval neg pos zer zer neg negative = refl
overlapLeadEval neg pos zer zer zer negative = refl
overlapLeadEval neg pos zer zer pos negative = refl
overlapLeadEval neg pos zer pos neg negative = refl
overlapLeadEval neg pos zer pos zer negative = refl
overlapLeadEval neg pos zer pos pos negative = refl
overlapLeadEval neg pos pos neg neg negative = refl
overlapLeadEval neg pos pos neg zer negative = refl
overlapLeadEval neg pos pos neg pos negative = refl
overlapLeadEval neg pos pos zer neg negative = refl
overlapLeadEval neg pos pos zer zer negative = refl
overlapLeadEval neg pos pos zer pos negative = refl
overlapLeadEval neg pos pos pos neg negative = refl
overlapLeadEval neg pos pos pos zer negative = refl
overlapLeadEval neg pos pos pos pos negative = refl
overlapLeadEval pos neg neg neg neg positive = refl
overlapLeadEval pos neg neg neg zer positive = refl
overlapLeadEval pos neg neg neg pos positive = refl
overlapLeadEval pos neg neg zer neg positive = refl
overlapLeadEval pos neg neg zer zer positive = refl
overlapLeadEval pos neg neg zer pos positive = refl
overlapLeadEval pos neg neg pos neg positive = refl
overlapLeadEval pos neg neg pos zer positive = refl
overlapLeadEval pos neg neg pos pos positive = refl
overlapLeadEval pos neg zer neg neg positive = refl
overlapLeadEval pos neg zer neg zer positive = refl
overlapLeadEval pos neg zer neg pos positive = refl
overlapLeadEval pos neg zer zer neg positive = refl
overlapLeadEval pos neg zer zer zer positive = refl
overlapLeadEval pos neg zer zer pos positive = refl
overlapLeadEval pos neg zer pos neg positive = refl
overlapLeadEval pos neg zer pos zer positive = refl
overlapLeadEval pos neg zer pos pos positive = refl
overlapLeadEval pos neg pos neg neg positive = refl
overlapLeadEval pos neg pos neg zer positive = refl
overlapLeadEval pos neg pos neg pos positive = refl
overlapLeadEval pos neg pos zer neg positive = refl
overlapLeadEval pos neg pos zer zer positive = refl
overlapLeadEval pos neg pos zer pos positive = refl
overlapLeadEval pos neg pos pos neg positive = refl
overlapLeadEval pos neg pos pos zer positive = refl
overlapLeadEval pos neg pos pos pos positive = refl
overlapLeadEval pos zer neg neg neg positive = refl
overlapLeadEval pos zer neg neg zer positive = refl
overlapLeadEval pos zer neg neg pos positive = refl
overlapLeadEval pos zer neg zer neg positive = refl
overlapLeadEval pos zer neg zer zer positive = refl
overlapLeadEval pos zer neg zer pos positive = refl
overlapLeadEval pos zer neg pos neg positive = refl
overlapLeadEval pos zer neg pos zer positive = refl
overlapLeadEval pos zer neg pos pos positive = refl
overlapLeadEval pos zer zer neg neg positive = refl
overlapLeadEval pos zer zer neg zer positive = refl
overlapLeadEval pos zer zer neg pos positive = refl
overlapLeadEval pos zer zer zer neg positive = refl
overlapLeadEval pos zer zer zer zer positive = refl
overlapLeadEval pos zer zer zer pos positive = refl
overlapLeadEval pos zer zer pos neg positive = refl
overlapLeadEval pos zer zer pos zer positive = refl
overlapLeadEval pos zer zer pos pos positive = refl
overlapLeadEval pos zer pos neg neg positive = refl
overlapLeadEval pos zer pos neg zer positive = refl
overlapLeadEval pos zer pos neg pos positive = refl
overlapLeadEval pos zer pos zer neg positive = refl
overlapLeadEval pos zer pos zer zer positive = refl
overlapLeadEval pos zer pos zer pos positive = refl
overlapLeadEval pos zer pos pos neg positive = refl
overlapLeadEval pos zer pos pos zer positive = refl
overlapLeadEval pos zer pos pos pos positive = refl
overlapLeadEval pos pos neg neg neg positive = refl
overlapLeadEval pos pos neg neg zer positive = refl
overlapLeadEval pos pos neg neg pos positive = refl
overlapLeadEval pos pos neg zer neg positive = refl
overlapLeadEval pos pos neg zer zer positive = refl
overlapLeadEval pos pos neg zer pos positive = refl
overlapLeadEval pos pos neg pos neg positive = refl
overlapLeadEval pos pos neg pos zer positive = refl
overlapLeadEval pos pos neg pos pos positive = refl
overlapLeadEval pos pos zer neg neg positive = refl
overlapLeadEval pos pos zer neg zer positive = refl
overlapLeadEval pos pos zer neg pos positive = refl
overlapLeadEval pos pos zer zer neg positive = refl
overlapLeadEval pos pos zer zer zer positive = refl
overlapLeadEval pos pos zer zer pos positive = refl
overlapLeadEval pos pos zer pos neg positive = refl
overlapLeadEval pos pos zer pos zer positive = refl
overlapLeadEval pos pos zer pos pos positive = refl
overlapLeadEval pos pos pos neg neg positive = refl
overlapLeadEval pos pos pos neg zer positive = refl
overlapLeadEval pos pos pos neg pos positive = refl
overlapLeadEval pos pos pos zer neg positive = refl
overlapLeadEval pos pos pos zer zer positive = refl
overlapLeadEval pos pos pos zer pos positive = refl
overlapLeadEval pos pos pos pos neg positive = refl
overlapLeadEval pos pos pos pos zer positive = refl
overlapLeadEval pos pos pos pos pos positive = refl
overlapLeadEval zer _ _ _ _ ()

overlapDistMix : (u a h aa : Trit) → A.mul3 u (A.add3 a (A.mul3 h aa)) ≡ A.add3 (A.mul3 u a) (A.mul3 h (A.mul3 u aa))
overlapDistMix neg neg neg neg = refl
overlapDistMix neg neg neg zer = refl
overlapDistMix neg neg neg pos = refl
overlapDistMix neg neg zer neg = refl
overlapDistMix neg neg zer zer = refl
overlapDistMix neg neg zer pos = refl
overlapDistMix neg neg pos neg = refl
overlapDistMix neg neg pos zer = refl
overlapDistMix neg neg pos pos = refl
overlapDistMix neg zer neg neg = refl
overlapDistMix neg zer neg zer = refl
overlapDistMix neg zer neg pos = refl
overlapDistMix neg zer zer neg = refl
overlapDistMix neg zer zer zer = refl
overlapDistMix neg zer zer pos = refl
overlapDistMix neg zer pos neg = refl
overlapDistMix neg zer pos zer = refl
overlapDistMix neg zer pos pos = refl
overlapDistMix neg pos neg neg = refl
overlapDistMix neg pos neg zer = refl
overlapDistMix neg pos neg pos = refl
overlapDistMix neg pos zer neg = refl
overlapDistMix neg pos zer zer = refl
overlapDistMix neg pos zer pos = refl
overlapDistMix neg pos pos neg = refl
overlapDistMix neg pos pos zer = refl
overlapDistMix neg pos pos pos = refl
overlapDistMix zer neg neg neg = refl
overlapDistMix zer neg neg zer = refl
overlapDistMix zer neg neg pos = refl
overlapDistMix zer neg zer neg = refl
overlapDistMix zer neg zer zer = refl
overlapDistMix zer neg zer pos = refl
overlapDistMix zer neg pos neg = refl
overlapDistMix zer neg pos zer = refl
overlapDistMix zer neg pos pos = refl
overlapDistMix zer zer neg neg = refl
overlapDistMix zer zer neg zer = refl
overlapDistMix zer zer neg pos = refl
overlapDistMix zer zer zer neg = refl
overlapDistMix zer zer zer zer = refl
overlapDistMix zer zer zer pos = refl
overlapDistMix zer zer pos neg = refl
overlapDistMix zer zer pos zer = refl
overlapDistMix zer zer pos pos = refl
overlapDistMix zer pos neg neg = refl
overlapDistMix zer pos neg zer = refl
overlapDistMix zer pos neg pos = refl
overlapDistMix zer pos zer neg = refl
overlapDistMix zer pos zer zer = refl
overlapDistMix zer pos zer pos = refl
overlapDistMix zer pos pos neg = refl
overlapDistMix zer pos pos zer = refl
overlapDistMix zer pos pos pos = refl
overlapDistMix pos neg neg neg = refl
overlapDistMix pos neg neg zer = refl
overlapDistMix pos neg neg pos = refl
overlapDistMix pos neg zer neg = refl
overlapDistMix pos neg zer zer = refl
overlapDistMix pos neg zer pos = refl
overlapDistMix pos neg pos neg = refl
overlapDistMix pos neg pos zer = refl
overlapDistMix pos neg pos pos = refl
overlapDistMix pos zer neg neg = refl
overlapDistMix pos zer neg zer = refl
overlapDistMix pos zer neg pos = refl
overlapDistMix pos zer zer neg = refl
overlapDistMix pos zer zer zer = refl
overlapDistMix pos zer zer pos = refl
overlapDistMix pos zer pos neg = refl
overlapDistMix pos zer pos zer = refl
overlapDistMix pos zer pos pos = refl
overlapDistMix pos pos neg neg = refl
overlapDistMix pos pos neg zer = refl
overlapDistMix pos pos neg pos = refl
overlapDistMix pos pos zer neg = refl
overlapDistMix pos pos zer zer = refl
overlapDistMix pos pos zer pos = refl
overlapDistMix pos pos pos neg = refl
overlapDistMix pos pos pos zer = refl
overlapDistMix pos pos pos pos = refl

overlapMulSwap : (w h s : Trit) → A.mul3 w (A.mul3 h s) ≡ A.mul3 h (A.mul3 w s)
overlapMulSwap neg neg neg = refl
overlapMulSwap neg neg zer = refl
overlapMulSwap neg neg pos = refl
overlapMulSwap neg zer neg = refl
overlapMulSwap neg zer zer = refl
overlapMulSwap neg zer pos = refl
overlapMulSwap neg pos neg = refl
overlapMulSwap neg pos zer = refl
overlapMulSwap neg pos pos = refl
overlapMulSwap zer neg neg = refl
overlapMulSwap zer neg zer = refl
overlapMulSwap zer neg pos = refl
overlapMulSwap zer zer neg = refl
overlapMulSwap zer zer zer = refl
overlapMulSwap zer zer pos = refl
overlapMulSwap zer pos neg = refl
overlapMulSwap zer pos zer = refl
overlapMulSwap zer pos pos = refl
overlapMulSwap pos neg neg = refl
overlapMulSwap pos neg zer = refl
overlapMulSwap pos neg pos = refl
overlapMulSwap pos zer neg = refl
overlapMulSwap pos zer zer = refl
overlapMulSwap pos zer pos = refl
overlapMulSwap pos pos neg = refl
overlapMulSwap pos pos zer = refl
overlapMulSwap pos pos pos = refl

overlapAddAssoc : (a b c : Trit) → A.add3 (A.add3 a b) c ≡ A.add3 a (A.add3 b c)
overlapAddAssoc neg neg neg = refl
overlapAddAssoc neg neg zer = refl
overlapAddAssoc neg neg pos = refl
overlapAddAssoc neg zer neg = refl
overlapAddAssoc neg zer zer = refl
overlapAddAssoc neg zer pos = refl
overlapAddAssoc neg pos neg = refl
overlapAddAssoc neg pos zer = refl
overlapAddAssoc neg pos pos = refl
overlapAddAssoc zer neg neg = refl
overlapAddAssoc zer neg zer = refl
overlapAddAssoc zer neg pos = refl
overlapAddAssoc zer zer neg = refl
overlapAddAssoc zer zer zer = refl
overlapAddAssoc zer zer pos = refl
overlapAddAssoc zer pos neg = refl
overlapAddAssoc zer pos zer = refl
overlapAddAssoc zer pos pos = refl
overlapAddAssoc pos neg neg = refl
overlapAddAssoc pos neg zer = refl
overlapAddAssoc pos neg pos = refl
overlapAddAssoc pos zer neg = refl
overlapAddAssoc pos zer zer = refl
overlapAddAssoc pos zer pos = refl
overlapAddAssoc pos pos neg = refl
overlapAddAssoc pos pos zer = refl
overlapAddAssoc pos pos pos = refl

overlapMulAdd : (h a b : Trit) → A.mul3 h (A.add3 a b) ≡ A.add3 (A.mul3 h a) (A.mul3 h b)
overlapMulAdd neg neg neg = refl
overlapMulAdd neg neg zer = refl
overlapMulAdd neg neg pos = refl
overlapMulAdd neg zer neg = refl
overlapMulAdd neg zer zer = refl
overlapMulAdd neg zer pos = refl
overlapMulAdd neg pos neg = refl
overlapMulAdd neg pos zer = refl
overlapMulAdd neg pos pos = refl
overlapMulAdd zer neg neg = refl
overlapMulAdd zer neg zer = refl
overlapMulAdd zer neg pos = refl
overlapMulAdd zer zer neg = refl
overlapMulAdd zer zer zer = refl
overlapMulAdd zer zer pos = refl
overlapMulAdd zer pos neg = refl
overlapMulAdd zer pos zer = refl
overlapMulAdd zer pos pos = refl
overlapMulAdd pos neg neg = refl
overlapMulAdd pos neg zer = refl
overlapMulAdd pos neg pos = refl
overlapMulAdd pos zer neg = refl
overlapMulAdd pos zer zer = refl
overlapMulAdd pos zer pos = refl
overlapMulAdd pos pos neg = refl
overlapMulAdd pos pos zer = refl
overlapMulAdd pos pos pos = refl

overlapInterchange : (a b c d : Trit) → A.add3 (A.add3 a b) (A.add3 c d) ≡ A.add3 (A.add3 a c) (A.add3 b d)
overlapInterchange neg neg neg neg = refl
overlapInterchange neg neg neg zer = refl
overlapInterchange neg neg neg pos = refl
overlapInterchange neg neg zer neg = refl
overlapInterchange neg neg zer zer = refl
overlapInterchange neg neg zer pos = refl
overlapInterchange neg neg pos neg = refl
overlapInterchange neg neg pos zer = refl
overlapInterchange neg neg pos pos = refl
overlapInterchange neg zer neg neg = refl
overlapInterchange neg zer neg zer = refl
overlapInterchange neg zer neg pos = refl
overlapInterchange neg zer zer neg = refl
overlapInterchange neg zer zer zer = refl
overlapInterchange neg zer zer pos = refl
overlapInterchange neg zer pos neg = refl
overlapInterchange neg zer pos zer = refl
overlapInterchange neg zer pos pos = refl
overlapInterchange neg pos neg neg = refl
overlapInterchange neg pos neg zer = refl
overlapInterchange neg pos neg pos = refl
overlapInterchange neg pos zer neg = refl
overlapInterchange neg pos zer zer = refl
overlapInterchange neg pos zer pos = refl
overlapInterchange neg pos pos neg = refl
overlapInterchange neg pos pos zer = refl
overlapInterchange neg pos pos pos = refl
overlapInterchange zer neg neg neg = refl
overlapInterchange zer neg neg zer = refl
overlapInterchange zer neg neg pos = refl
overlapInterchange zer neg zer neg = refl
overlapInterchange zer neg zer zer = refl
overlapInterchange zer neg zer pos = refl
overlapInterchange zer neg pos neg = refl
overlapInterchange zer neg pos zer = refl
overlapInterchange zer neg pos pos = refl
overlapInterchange zer zer neg neg = refl
overlapInterchange zer zer neg zer = refl
overlapInterchange zer zer neg pos = refl
overlapInterchange zer zer zer neg = refl
overlapInterchange zer zer zer zer = refl
overlapInterchange zer zer zer pos = refl
overlapInterchange zer zer pos neg = refl
overlapInterchange zer zer pos zer = refl
overlapInterchange zer zer pos pos = refl
overlapInterchange zer pos neg neg = refl
overlapInterchange zer pos neg zer = refl
overlapInterchange zer pos neg pos = refl
overlapInterchange zer pos zer neg = refl
overlapInterchange zer pos zer zer = refl
overlapInterchange zer pos zer pos = refl
overlapInterchange zer pos pos neg = refl
overlapInterchange zer pos pos zer = refl
overlapInterchange zer pos pos pos = refl
overlapInterchange pos neg neg neg = refl
overlapInterchange pos neg neg zer = refl
overlapInterchange pos neg neg pos = refl
overlapInterchange pos neg zer neg = refl
overlapInterchange pos neg zer zer = refl
overlapInterchange pos neg zer pos = refl
overlapInterchange pos neg pos neg = refl
overlapInterchange pos neg pos zer = refl
overlapInterchange pos neg pos pos = refl
overlapInterchange pos zer neg neg = refl
overlapInterchange pos zer neg zer = refl
overlapInterchange pos zer neg pos = refl
overlapInterchange pos zer zer neg = refl
overlapInterchange pos zer zer zer = refl
overlapInterchange pos zer zer pos = refl
overlapInterchange pos zer pos neg = refl
overlapInterchange pos zer pos zer = refl
overlapInterchange pos zer pos pos = refl
overlapInterchange pos pos neg neg = refl
overlapInterchange pos pos neg zer = refl
overlapInterchange pos pos neg pos = refl
overlapInterchange pos pos zer neg = refl
overlapInterchange pos pos zer zer = refl
overlapInterchange pos pos zer pos = refl
overlapInterchange pos pos pos neg = refl
overlapInterchange pos pos pos zer = refl
overlapInterchange pos pos pos pos = refl

overlapTailEval : (a b h u w aa bb s : Trit) →
  A.add3 (A.add3 b (A.mul3 h bb))
    (A.add3 (A.mul3 u (A.add3 a (A.mul3 h aa))) (A.mul3 w (A.mul3 h s)))
  ≡ A.add3 b (A.add3 (A.mul3 u a)
       (A.mul3 h (A.add3 bb (A.add3 (A.mul3 u aa) (A.mul3 w s)))))
overlapTailEval a b h u w aa bb s
  rewrite overlapDistMix u a h aa | overlapMulSwap w h s
        | overlapAddAssoc (A.mul3 u a) (A.mul3 h (A.mul3 u aa)) (A.mul3 h (A.mul3 w s))
        | sym (overlapMulAdd h (A.mul3 u aa) (A.mul3 w s))
        | overlapInterchange b (A.mul3 h bb) (A.mul3 u a)
            (A.mul3 h (A.add3 (A.mul3 u aa) (A.mul3 w s)))
        | sym (overlapMulAdd h bb (A.add3 (A.mul3 u aa) (A.mul3 w s)))
        | overlapAddAssoc b (A.mul3 u a)
            (A.mul3 h (A.add3 bb (A.add3 (A.mul3 u aa) (A.mul3 w s)))) = refl

generalSwapBack : (p : A.Affine9 Trit) (nz : Overlap01to02 p) →
  swapPivot (swapPivot p nz) (swapPivotAdmissible p nz) ≡ p
generalSwapBack (A.affine9 A.pivot01 (M.triple a0 a1 a2)
  (M.triple neg v1 v2) (M.triple b0 b1 b2)) negative
  rewrite overlapLeadTwice neg a0 negative | overlapLeadTwice neg b0 negative
        | overlapSlopeTwice neg v1 negative | overlapSlopeTwice neg v2 negative
        | overlapTailTwice neg v1 a0 a1 negative | overlapTailTwice neg v2 a0 a2 negative
        | overlapTailTwice neg v1 b0 b1 negative | overlapTailTwice neg v2 b0 b2 negative = refl
generalSwapBack (A.affine9 A.pivot01 (M.triple a0 a1 a2)
  (M.triple pos v1 v2) (M.triple b0 b1 b2)) positive
  rewrite overlapLeadTwice pos a0 positive | overlapLeadTwice pos b0 positive
        | overlapSlopeTwice pos v1 positive | overlapSlopeTwice pos v2 positive
        | overlapTailTwice pos v1 a0 a1 positive | overlapTailTwice pos v2 a0 a2 positive
        | overlapTailTwice pos v1 b0 b1 positive | overlapTailTwice pos v2 b0 b2 positive = refl
generalSwapBack (A.affine9 A.pivot01 a (M.triple zer v1 v2) b) ()

generalAmbientEquality : (p : A.Affine9 Trit) (nz : Overlap01to02 p) →
  (u v : Trit) → evaluate01 p u v ≡ evaluate02 (swapPivot p nz) u
    (A.add3 (M.first (A.offset p))
      (A.add3 (A.mul3 u (M.first (A.slopeU p))) (A.mul3 v (M.first (A.slopeV p)))))
generalAmbientEquality (A.affine9 A.pivot01 (M.triple a0 a1 a2)
  (M.triple neg v1 v2) (M.triple b0 b1 b2)) negative u v
  rewrite overlapTailEval a1 b1 v1 u
      (A.add3 b0 (A.add3 (A.mul3 u a0) (A.mul3 v neg)))
      (A.mul3 (inv a0) neg) (A.mul3 (inv b0) neg) neg
    | overlapTailEval a2 b2 v2 u
      (A.add3 b0 (A.add3 (A.mul3 u a0) (A.mul3 v neg)))
      (A.mul3 (inv a0) neg) (A.mul3 (inv b0) neg) neg
    | overlapLeadEval neg a0 b0 u v negative = refl
generalAmbientEquality (A.affine9 A.pivot01 (M.triple a0 a1 a2)
  (M.triple pos v1 v2) (M.triple b0 b1 b2)) positive u v
  rewrite overlapTailEval a1 b1 v1 u
      (A.add3 b0 (A.add3 (A.mul3 u a0) (A.mul3 v pos)))
      (A.mul3 (inv a0) pos) (A.mul3 (inv b0) pos) pos
    | overlapTailEval a2 b2 v2 u
      (A.add3 b0 (A.add3 (A.mul3 u a0) (A.mul3 v pos)))
      (A.mul3 (inv a0) pos) (A.mul3 (inv b0) pos) pos
    | overlapLeadEval pos a0 b0 u v positive = refl
generalAmbientEquality (A.affine9 A.pivot01 a (M.triple zer v1 v2) b) () u v

generalExactPivotOverlap : (p : A.Affine9 Trit) (nz : Overlap01to02 p) → ExactPivotOverlap p nz
generalExactPivotOverlap p nz = record
  { swapBack = generalSwapBack p nz ; ambientEquality = generalAmbientEquality p nz }

-- Source-written, not kernel-checked. This is the entire original
-- single-nonzero overlap, not merely the rotation-stable subcarrier.
