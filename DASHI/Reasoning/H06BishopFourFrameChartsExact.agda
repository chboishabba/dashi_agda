module DASHI.Reasoning.H06BishopFourFrameChartsExact where

-- All four projective quaternion charts via actual half-turns.
-- The selected scalar-leading chart is the existing H06 owner.
-- Native equality is componentwise Bishop equivalence.
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (inj₂)
import Real as B
import RealProperties as BP
import Inverse as Inv
import DASHI.Reasoning.H06BishopAffineFrameExact as H
import DASHI.Reasoning.H06BishopAffineRechartExact as A

data Mark : Set where
  scalar axisX axisY axisZ : Mark

-- Left multiplication by a fixed proper half-turn (row signs).
-- For the spatial marks this is the rotation of the respective unit
-- quaternion. The normalized selected ray is (1,x,y,z); its lift back
-- is the corresponding unit quaternion times this ray.
flipColumn : Mark → H.Vec3 → H.Vec3
flipColumn scalar (H.vec3 a b c) = H.vec3 a b c
flipColumn axisX (H.vec3 a b c) = H.vec3 a (B.-_ b) (B.-_ c)
flipColumn axisY (H.vec3 a b c) = H.vec3 (B.-_ a) b (B.-_ c)
flipColumn axisZ (H.vec3 a b c) = H.vec3 (B.-_ a) (B.-_ b) c

flipMatrix : Mark → H.Matrix3 → H.Matrix3
flipMatrix k (H.matrix3 a b c) =
  H.matrix3 (flipColumn k a) (flipColumn k b) (flipColumn k c)

encode : Mark → H.Frame3 → H.Matrix3
encode k f = flipMatrix k (H.frameRotation f)

record MatrixEq (left right : H.Matrix3) : Set where
  constructor eq9
  field
    e00 : B._≃_ (H.v0 (H.col0 left)) (H.v0 (H.col0 right))
    e10 : B._≃_ (H.v1 (H.col0 left)) (H.v1 (H.col0 right))
    e20 : B._≃_ (H.v2 (H.col0 left)) (H.v2 (H.col0 right))
    e01 : B._≃_ (H.v0 (H.col1 left)) (H.v0 (H.col1 right))
    e11 : B._≃_ (H.v1 (H.col1 left)) (H.v1 (H.col1 right))
    e21 : B._≃_ (H.v2 (H.col1 left)) (H.v2 (H.col1 right))
    e02 : B._≃_ (H.v0 (H.col2 left)) (H.v0 (H.col2 right))
    e12 : B._≃_ (H.v1 (H.col2 left)) (H.v1 (H.col2 right))
    e22 : B._≃_ (H.v2 (H.col2 left)) (H.v2 (H.col2 right))
open MatrixEq public

doubleNeg : (a : B.ℝ) → B._≃_ (B.-_ (B.-_ a)) a
doubleNeg a = let open BP.ℝ-Solver in
  solve 1 (λ x → (⊝ (⊝ x)) ⊜ x) BP.≃-refl a

flipTwice : (k : Mark) (r : H.Matrix3) →
  MatrixEq (flipMatrix k (flipMatrix k r)) r
flipTwice scalar (H.matrix3 (H.vec3 a d g) (H.vec3 b e h) (H.vec3 c f j)) = eq9
  BP.≃-refl BP.≃-refl BP.≃-refl BP.≃-refl BP.≃-refl BP.≃-refl BP.≃-refl BP.≃-refl BP.≃-refl
flipTwice axisX (H.matrix3 (H.vec3 a d g) (H.vec3 b e h) (H.vec3 c f j)) = eq9
  BP.≃-refl (doubleNeg d) (doubleNeg g) BP.≃-refl (doubleNeg e) (doubleNeg h) BP.≃-refl (doubleNeg f) (doubleNeg j)
flipTwice axisY (H.matrix3 (H.vec3 a d g) (H.vec3 b e h) (H.vec3 c f j)) = eq9
  (doubleNeg a) BP.≃-refl (doubleNeg g) (doubleNeg b) BP.≃-refl (doubleNeg h) (doubleNeg c) BP.≃-refl (doubleNeg j)
flipTwice axisZ (H.matrix3 (H.vec3 a d g) (H.vec3 b e h) (H.vec3 c f j)) = eq9
  (doubleNeg a) (doubleNeg d) BP.≃-refl (doubleNeg b) (doubleNeg e) BP.≃-refl (doubleNeg c) (doubleNeg f) BP.≃-refl

traceCong : {r s : H.Matrix3} → MatrixEq r s →
  B._≃_ (H.traceDenominator r) (H.traceDenominator s)
traceCong {H.matrix3 (H.vec3 a d g) (H.vec3 b e h) (H.vec3 c f j)}
          {H.matrix3 (H.vec3 a′ d′ g′) (H.vec3 b′ e′ h′) (H.vec3 c′ f′ j′)} eq =
  BP.+-cong BP.≃-refl (BP.+-cong (e00 eq) (BP.+-cong (e11 eq) (e22 eq)))

skewXCong : {r s : H.Matrix3} → MatrixEq r s →
  B._≃_ (H.skewX r) (H.skewX s)
skewXCong {H.matrix3 (H.vec3 a d g) (H.vec3 b e h) (H.vec3 c f j)}
          {H.matrix3 (H.vec3 a′ d′ g′) (H.vec3 b′ e′ h′) (H.vec3 c′ f′ j′)} eq =
  BP.-cong (e21 eq) (e12 eq)

skewYCong : {r s : H.Matrix3} → MatrixEq r s →
  B._≃_ (H.skewY r) (H.skewY s)
skewYCong {H.matrix3 (H.vec3 a d g) (H.vec3 b e h) (H.vec3 c f j)}
          {H.matrix3 (H.vec3 a′ d′ g′) (H.vec3 b′ e′ h′) (H.vec3 c′ f′ j′)} eq =
  BP.-cong (e02 eq) (e20 eq)

skewZCong : {r s : H.Matrix3} → MatrixEq r s →
  B._≃_ (H.skewZ r) (H.skewZ s)
skewZCong {H.matrix3 (H.vec3 a d g) (H.vec3 b e h) (H.vec3 c f j)}
          {H.matrix3 (H.vec3 a′ d′ g′) (H.vec3 b′ e′ h′) (H.vec3 c′ f′ j′)} eq =
  BP.-cong (e10 eq) (e01 eq)

FrameEq : H.Frame3 → H.Frame3 → Set
FrameEq f g = B._≃_ (H.Frame3.x f) (H.Frame3.x g) ×
  (B._≃_ (H.Frame3.y f) (H.Frame3.y g) × B._≃_ (H.Frame3.z f) (H.Frame3.z g))

frameTrans : {f g h : H.Frame3} → FrameEq f g → FrameEq g h → FrameEq f h
frameTrans (a , (b , c)) (d , (e , f)) =
  BP.≃-trans a d , (BP.≃-trans b e , BP.≃-trans c f)

recoverCong : (r s : H.Matrix3)
  (nr : B._≄0 (H.traceDenominator r)) (ns : B._≄0 (H.traceDenominator s)) →
  MatrixEq r s → FrameEq (H.recoverFrame r nr) (H.recoverFrame s ns)
recoverCong r s nr ns eq =
  let i = A.inverseCongruentApart (H.traceDenominator r) (H.traceDenominator s)
        nr ns (traceCong eq)
  in BP.*-cong i (skewXCong eq) ,
    (BP.*-cong i (skewYCong eq) , BP.*-cong i (skewZCong eq))

-- Actual matrix decoder, no stored coordinates. Its domain is the
-- original selected trace guard after undoing the chart half-turn.
decode : (k : Mark) (r : H.Matrix3) →
  B._≄0 (H.traceDenominator (flipMatrix k r)) → H.Frame3
decode k r nz = H.recoverFrame (flipMatrix k r) nz

encodePositive : (k : Mark) (f : H.Frame3) →
  B._<_ B.0ℝ (H.traceDenominator (flipMatrix k (encode k f)))
encodePositive k f =
  BP.<-respʳ-≃ (BP.≃-sym (traceCong (flipTwice k (H.frameRotation f))))
    (H.tracePositive f)

reopens : (k : Mark) (f : H.Frame3) →
  FrameEq (decode k (encode k f) (inj₂ (encodePositive k f))) f
reopens k f = frameTrans
  (recoverCong (flipMatrix k (encode k f)) (H.frameRotation f)
    (inj₂ (encodePositive k f)) (inj₂ (H.tracePositive f))
    (flipTwice k (H.frameRotation f)))
  (H.frameReopens f)

-- Each row sign transformation is an even sign change. Reuse existing
-- normalized Gram and determinant proofs for proper orientation.
flipDot : (k : Mark) (u v : H.Vec3) →
  B._≃_ (H.dot3 (flipColumn k u) (flipColumn k v)) (H.dot3 u v)
flipDot scalar (H.vec3 a b c) (H.vec3 d e f) =
  let open BP.ℝ-Solver in
  solve 6 (λ a b c d e f → ((a ⊗ d) ⊕ ((b ⊗ e) ⊕ (c ⊗ f))) ⊜ ((a ⊗ d) ⊕ ((b ⊗ e) ⊕ (c ⊗ f))))
    BP.≃-refl a b c d e f
flipDot axisX (H.vec3 a b c) (H.vec3 d e f) =
  let open BP.ℝ-Solver in
  solve 6 (λ a b c d e f → ((a ⊗ d) ⊕ (((⊝ b) ⊗ (⊝ e)) ⊕ ((⊝ c) ⊗ (⊝ f)))) ⊜ ((a ⊗ d) ⊕ ((b ⊗ e) ⊕ (c ⊗ f))))
    BP.≃-refl a b c d e f
flipDot axisY (H.vec3 a b c) (H.vec3 d e f) =
  let open BP.ℝ-Solver in
  solve 6 (λ a b c d e f → (((⊝ a) ⊗ (⊝ d)) ⊕ ((b ⊗ e) ⊕ ((⊝ c) ⊗ (⊝ f)))) ⊜ ((a ⊗ d) ⊕ ((b ⊗ e) ⊕ (c ⊗ f))))
    BP.≃-refl a b c d e f
flipDot axisZ (H.vec3 a b c) (H.vec3 d e f) =
  let open BP.ℝ-Solver in
  solve 6 (λ a b c d e f → (((⊝ a) ⊗ (⊝ d)) ⊕ (((⊝ b) ⊗ (⊝ e)) ⊕ (c ⊗ f))) ⊜ ((a ⊗ d) ⊕ ((b ⊗ e) ⊕ (c ⊗ f))))
    BP.≃-refl a b c d e f

flipDet : (k : Mark) (r : H.Matrix3) →
  B._≃_ (H.det3 (flipMatrix k r)) (H.det3 r)
flipDet scalar (H.matrix3 (H.vec3 a d g) (H.vec3 b e h) (H.vec3 c f j)) =
  let open BP.ℝ-Solver in
  solve 9 (λ a b c d e f g h j → (((a ⊗ ((e ⊗ j) ⊖ (f ⊗ h))) ⊖ (b ⊗ ((d ⊗ j) ⊖ (f ⊗ g)))) ⊕ (c ⊗ ((d ⊗ h) ⊖ (e ⊗ g)))) ⊜ (((a ⊗ ((e ⊗ j) ⊖ (f ⊗ h))) ⊖ (b ⊗ ((d ⊗ j) ⊖ (f ⊗ g)))) ⊕ (c ⊗ ((d ⊗ h) ⊖ (e ⊗ g)))))
    BP.≃-refl a b c d e f g h j
flipDet axisX (H.matrix3 (H.vec3 a d g) (H.vec3 b e h) (H.vec3 c f j)) =
  let open BP.ℝ-Solver in
  solve 9 (λ a b c d e f g h j → (((a ⊗ (((⊝ e) ⊗ (⊝ j)) ⊖ ((⊝ f) ⊗ (⊝ h)))) ⊖ (b ⊗ (((⊝ d) ⊗ (⊝ j)) ⊖ ((⊝ f) ⊗ (⊝ g))))) ⊕ (c ⊗ (((⊝ d) ⊗ (⊝ h)) ⊖ ((⊝ e) ⊗ (⊝ g))))) ⊜ (((a ⊗ ((e ⊗ j) ⊖ (f ⊗ h))) ⊖ (b ⊗ ((d ⊗ j) ⊖ (f ⊗ g)))) ⊕ (c ⊗ ((d ⊗ h) ⊖ (e ⊗ g)))))
    BP.≃-refl a b c d e f g h j
flipDet axisY (H.matrix3 (H.vec3 a d g) (H.vec3 b e h) (H.vec3 c f j)) =
  let open BP.ℝ-Solver in
  solve 9 (λ a b c d e f g h j → ((((⊝ a) ⊗ ((e ⊗ (⊝ j)) ⊖ (f ⊗ (⊝ h)))) ⊖ ((⊝ b) ⊗ ((d ⊗ (⊝ j)) ⊖ (f ⊗ (⊝ g))))) ⊕ ((⊝ c) ⊗ ((d ⊗ (⊝ h)) ⊖ (e ⊗ (⊝ g))))) ⊜ (((a ⊗ ((e ⊗ j) ⊖ (f ⊗ h))) ⊖ (b ⊗ ((d ⊗ j) ⊖ (f ⊗ g)))) ⊕ (c ⊗ ((d ⊗ h) ⊖ (e ⊗ g)))))
    BP.≃-refl a b c d e f g h j
flipDet axisZ (H.matrix3 (H.vec3 a d g) (H.vec3 b e h) (H.vec3 c f j)) =
  let open BP.ℝ-Solver in
  solve 9 (λ a b c d e f g h j → ((((⊝ a) ⊗ (((⊝ e) ⊗ j) ⊖ ((⊝ f) ⊗ h))) ⊖ ((⊝ b) ⊗ (((⊝ d) ⊗ j) ⊖ ((⊝ f) ⊗ g)))) ⊕ ((⊝ c) ⊗ (((⊝ d) ⊗ h) ⊖ ((⊝ e) ⊗ g)))) ⊜ (((a ⊗ ((e ⊗ j) ⊖ (f ⊗ h))) ⊖ (b ⊗ ((d ⊗ j) ⊖ (f ⊗ g)))) ⊕ (c ⊗ ((d ⊗ h) ⊖ (e ⊗ g)))))
    BP.≃-refl a b c d e f g h j

encodedDetOne : (k : Mark) (f : H.Frame3) →
  B._≃_ (H.det3 (encode k f)) B.1ℝ
encodedDetOne k f = BP.≃-trans (flipDet k (H.frameRotation f))
  (H.rotationDetOne B.1ℝ (H.Frame3.x f) (H.Frame3.y f) (H.Frame3.z f)
    (H.leadingOneApart f))

-- The scalar chart parameters are in the half-turn-aligned quaternion
-- frame. Chart mark and original Spin sign are retained externally;
-- do not infer the sign from a rotation. Arbitrary proper-matrix image
-- membership, native overlap right-inverse and H05 arrow congruence
-- are separate. Source-written, not kernel-certified.
