module DASHI.Reasoning.H06BishopAffineRechartExact where

-- Actual H06 R4 affine row rechart, using the existing guarded Bishop
-- inverse. Equality is the native real setoid, not Cauchy representatives.
-- Source-written, kernel acceptance pending.
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as B
import RealProperties as BP
import Inverse as Inv
import DASHI.Foundations.BishopInverseSquareProductExact as I
import DASHI.Reasoning.H06BishopAffineFrameExact as H

-- Generalize the existing inverse-uniqueness owner to signed pivots.
-- Both witnesses are retained; equality need not identify the witnesses.
inverseCongruentApart : (x y : B.ℝ) (nx : B._≄0 x) (ny : B._≄0 y) →
  B._≃_ x y → B._≃_ (Inv._⁻¹ x nx) (Inv._⁻¹ y ny)
inverseCongruentApart x y nx ny eq =
  I.inverseFromCancellation x (Inv._⁻¹ y ny) nx
    (BP.≃-trans (BP.*-congˡ eq) (Inv.*-inverseˡ y ny))

record Row : Set where
  constructor row
  field
    origin slope0 slope1 : B.ℝ
open Row public

eval : Row → B.ℝ → B.ℝ → B.ℝ
eval (row o r s) u v = (B._+_ o (B._+_ (B._*_ r u) (B._*_ s v)))

normalize : H.Pivot2 → B.ℝ → B.ℝ → Row → Row
normalize (H.pivot2 a b c d nz) ou ov (row o r s) =
  let i = Inv._⁻¹ (H.det2 a b c d) nz
  in row (B._-_ (B._-_ o (B._*_ (B._*_ i (B._-_ (B._*_ d r) (B._*_ c s))) ou)) (B._*_ (B._*_ i (B._-_ (B._*_ a s) (B._*_ b r))) ov)) (B._*_ i (B._-_ (B._*_ d r) (B._*_ c s))) (B._*_ i (B._-_ (B._*_ a s) (B._*_ b r)))

rowForwardPolynomial : (a b c d i r s o ou ov u v : B.ℝ) → B._≃_ (B._+_ (B._-_ (B._-_ o (B._*_ (B._*_ i (B._-_ (B._*_ d r) (B._*_ c s))) ou)) (B._*_ (B._*_ i (B._-_ (B._*_ a s) (B._*_ b r))) ov)) (B._+_ (B._*_ (B._*_ i (B._-_ (B._*_ d r) (B._*_ c s))) (B._+_ ou (B._+_ (B._*_ a u) (B._*_ b v)))) (B._*_ (B._*_ i (B._-_ (B._*_ a s) (B._*_ b r))) (B._+_ ov (B._+_ (B._*_ c u) (B._*_ d v)))))) (B._+_ o (B._*_ (B._*_ i (B._-_ (B._*_ a d) (B._*_ b c))) (B._+_ (B._*_ r u) (B._*_ s v))))
rowForwardPolynomial a b c d i r s o ou ov u v =
  let open BP.ℝ-Solver in
  solve 12 (λ a b c d i r s o ou ov u v → (((o ⊖ ((i ⊗ ((d ⊗ r) ⊖ (c ⊗ s))) ⊗ ou)) ⊖ ((i ⊗ ((a ⊗ s) ⊖ (b ⊗ r))) ⊗ ov)) ⊕ (((i ⊗ ((d ⊗ r) ⊖ (c ⊗ s))) ⊗ (ou ⊕ ((a ⊗ u) ⊕ (b ⊗ v)))) ⊕ ((i ⊗ ((a ⊗ s) ⊖ (b ⊗ r))) ⊗ (ov ⊕ ((c ⊗ u) ⊕ (d ⊗ v)))))) ⊜ (o ⊕ ((i ⊗ ((a ⊗ d) ⊖ (b ⊗ c))) ⊗ ((r ⊗ u) ⊕ (s ⊗ v)))))
    BP.≃-refl a b c d i r s o ou ov u v

rowReversePolynomial : (a b c d i r s o ou ov u v : B.ℝ) → B._≃_ (B._+_ (B._-_ (B._-_ o (B._*_ (B._*_ i (B._-_ (B._*_ d r) (B._*_ c s))) ou)) (B._*_ (B._*_ i (B._-_ (B._*_ a s) (B._*_ b r))) ov)) (B._+_ (B._*_ (B._*_ i (B._-_ (B._*_ d r) (B._*_ c s))) u) (B._*_ (B._*_ i (B._-_ (B._*_ a s) (B._*_ b r))) v))) (B._+_ o (B._+_ (B._*_ r (B._*_ i (B._-_ (B._*_ d (B._-_ u ou)) (B._*_ b (B._-_ v ov))))) (B._*_ s (B._*_ i (B._-_ (B._*_ a (B._-_ v ov)) (B._*_ c (B._-_ u ou)))))))
rowReversePolynomial a b c d i r s o ou ov u v =
  let open BP.ℝ-Solver in
  solve 12 (λ a b c d i r s o ou ov u v → (((o ⊖ ((i ⊗ ((d ⊗ r) ⊖ (c ⊗ s))) ⊗ ou)) ⊖ ((i ⊗ ((a ⊗ s) ⊖ (b ⊗ r))) ⊗ ov)) ⊕ (((i ⊗ ((d ⊗ r) ⊖ (c ⊗ s))) ⊗ u) ⊕ ((i ⊗ ((a ⊗ s) ⊖ (b ⊗ r))) ⊗ v))) ⊜ (o ⊕ ((r ⊗ (i ⊗ ((d ⊗ (u ⊖ ou)) ⊖ (b ⊗ (v ⊖ ov))))) ⊕ (s ⊗ (i ⊗ ((a ⊗ (v ⊖ ov)) ⊖ (c ⊗ (u ⊖ ou))))))))
    BP.≃-refl a b c d i r s o ou ov u v


rowForward : (p : H.Pivot2) (ou ov : B.ℝ) (r : Row) (u v : B.ℝ) →
  B._≃_ (eval (normalize p ou ov r)
    (eval (row ou (H.a p) (H.b p)) u v)
    (eval (row ov (H.c p) (H.d p)) u v)) (eval r u v)
rowForward (H.pivot2 a b c d nz) ou ov (row o r s) u v =
  BP.≃-trans
    (rowForwardPolynomial a b c d (Inv._⁻¹ (H.det2 a b c d) nz) r s o ou ov u v)
    (BP.+-cong BP.≃-refl
      (BP.≃-trans (BP.*-congʳ (Inv.*-inverseˡ (H.det2 a b c d) nz))
        (BP.*-identityˡ (B._+_ (B._*_ r u) (B._*_ s v)))))

rowReverse : (p : H.Pivot2) (ou ov : B.ℝ) (r : Row) (u v : B.ℝ) →
  B._≃_ (eval (normalize p ou ov r) u v)
    (eval r (H.firstCoordinate p (B._-_ u ou) (B._-_ v ov))
            (H.secondCoordinate p (B._-_ u ou) (B._-_ v ov)))
rowReverse (H.pivot2 a b c d nz) ou ov (row o r s) u v =
  rowReversePolynomial a b c d (Inv._⁻¹ (H.det2 a b c d) nz) r s o ou ov u v

-- The four actual ambient coordinate rows and all six pivot choices.
data Axis : Set where
  axis0 axis1 axis2 axis3 : Axis
data Mark : Set where
  p01 p02 p03 p12 p13 p23 : Mark

first second : Mark → Axis
first p01 = axis0
first p02 = axis0
first p03 = axis0
first p12 = axis1
first p13 = axis1
first p23 = axis2
second p01 = axis1
second p02 = axis2
second p03 = axis3
second p12 = axis2
second p13 = axis3
second p23 = axis3

record Plane4 : Set where
  constructor plane4
  field row0 row1 row2 row3 : Row

at : Plane4 → Axis → Row
at p axis0 = Plane4.row0 p
at p axis1 = Plane4.row1 p
at p axis2 = Plane4.row2 p
at p axis3 = Plane4.row3 p

graphPlane : H.Affine6 → Plane4
graphPlane (H.affine6 a b c d e f) = plane4
  (row B.0ℝ B.1ℝ B.0ℝ) (row B.0ℝ B.0ℝ B.1ℝ)
  (row e a b) (row f c d)

detAt : Plane4 → Mark → B.ℝ
detAt p q = H.det2 (slope0 (at p (first q))) (slope1 (at p (first q)))
  (slope0 (at p (second q))) (slope1 (at p (second q)))

record Admissible (p : Plane4) : Set where
  constructor admissible
  field
    mark : Mark
    apart : B._≄0 (detAt p mark)
open Admissible public

pivotAt : (p : Plane4) → Admissible p → H.Pivot2
pivotAt p (admissible q nz) =
  H.pivot2 (slope0 (at p (first q))) (slope1 (at p (first q)))
    (slope0 (at p (second q))) (slope1 (at p (second q))) nz

firstOrigin secondOrigin : (p : Plane4) → Admissible p → B.ℝ
firstOrigin p q = origin (at p (first (mark q)))
secondOrigin p q = origin (at p (second (mark q)))

normalizedAt : (p : Plane4) → Admissible p → Axis → Row
normalizedAt p q k = normalize (pivotAt p q)
  (firstOrigin p q) (secondOrigin p q) (at p k)

rechart : (p : Plane4) → Admissible p → Plane4
rechart p q = plane4 (normalizedAt p q axis0) (normalizedAt p q axis1)
  (normalizedAt p q axis2) (normalizedAt p q axis3)

atRechart : (p : Plane4) (q : Admissible p) (k : Axis) →
  -- The definition only selects a coordinate; no real equality coercion.
  B._≃_ (origin (at (rechart p q) k)) (origin (normalizedAt p q k))
atRechart p q axis0 = BP.≃-refl
atRechart p q axis1 = BP.≃-refl
atRechart p q axis2 = BP.≃-refl
atRechart p q axis3 = BP.≃-refl

forward0 forward1 : (p : Plane4) → Admissible p → B.ℝ → B.ℝ → B.ℝ
forward0 p q u v = eval (at p (first (mark q))) u v
forward1 p q u v = eval (at p (second (mark q))) u v

backward0 backward1 : (p : Plane4) → Admissible p → B.ℝ → B.ℝ → B.ℝ
backward0 p q u v = H.firstCoordinate (pivotAt p q)
  (B._-_ u (firstOrigin p q)) (B._-_ v (secondOrigin p q))
backward1 p q u v = H.secondCoordinate (pivotAt p q)
  (B._-_ u (firstOrigin p q)) (B._-_ v (secondOrigin p q))

-- Both directions compare the literal ambient coordinate values, not just
-- an equal dimension or an equal number of sampled points.
ambientForward : (p : Plane4) (q : Admissible p) (k : Axis) (u v : B.ℝ) →
  B._≃_ (eval (normalizedAt p q k) (forward0 p q u v) (forward1 p q u v))
    (eval (at p k) u v)
ambientForward p (admissible q nz) k u v with at p (first q) | at p (second q)
... | row o a b | row w c d =
  rowForward (H.pivot2 a b c d nz) o w (at p k) u v

ambientReverse : (p : Plane4) (q : Admissible p) (k : Axis) (u v : B.ℝ) →
  B._≃_ (eval (normalizedAt p q k) u v)
    (eval (at p k) (backward0 p q u v) (backward1 p q u v))
ambientReverse p q k u v = rowReverse (pivotAt p q)
  (firstOrigin p q) (secondOrigin p q) (at p k) u v

reopen0 : (p : Plane4) (q : Admissible p) (u v : B.ℝ) →
  B._≃_ (backward0 p q (forward0 p q u v) (forward1 p q u v)) u
reopen0 p (admissible q nz) u v with at p (first q) | at p (second q)
... | row o a b | row w c d = H.recoverFirst (H.pivot2 a b c d nz) o w u v

reopen1 : (p : Plane4) (q : Admissible p) (u v : B.ℝ) →
  B._≃_ (backward1 p q (forward0 p q u v) (forward1 p q u v)) v
reopen1 p (admissible q nz) u v with at p (first q) | at p (second q)
... | row o a b | row w c d = H.recoverSecond (H.pivot2 a b c d nz) o w u v

-- Recharting is actual pointwise setoid transport. The full native
-- coefficient cocycle, all-chart SO3 decoder and original H05 arrow
-- congruence are not asserted by this source.
