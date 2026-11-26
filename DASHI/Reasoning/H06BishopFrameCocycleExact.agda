module DASHI.Reasoning.H06BishopFrameCocycleExact where

-- Consume the existing four selected quaternion charts and actual matrix
-- decoders. Native setoid equality, no equality of Cauchy representatives.
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (inj₂)
import Real as B
import RealProperties as BP
import DASHI.Reasoning.H06BishopAffineFrameExact as H
import DASHI.Reasoning.H06BishopAffineRechartExact as A
import DASHI.Reasoning.H06BishopFourFrameChartsExact as F

matrixRefl : (r : H.Matrix3) → F.MatrixEq r r
matrixRefl r = F.eq9 BP.≃-refl BP.≃-refl BP.≃-refl BP.≃-refl BP.≃-refl BP.≃-refl BP.≃-refl BP.≃-refl BP.≃-refl

matrixSym : {r s : H.Matrix3} → F.MatrixEq r s → F.MatrixEq s r
matrixSym e = F.eq9
  (BP.≃-symm (F.e00 e)) (BP.≃-symm (F.e10 e)) (BP.≃-symm (F.e20 e)) (BP.≃-symm (F.e01 e)) (BP.≃-symm (F.e11 e)) (BP.≃-symm (F.e21 e)) (BP.≃-symm (F.e02 e)) (BP.≃-symm (F.e12 e)) (BP.≃-symm (F.e22 e))

matrixTrans : {r s t : H.Matrix3} →
  F.MatrixEq r s → F.MatrixEq s t → F.MatrixEq r t
matrixTrans e f = F.eq9
  (BP.≃-trans (F.e00 e) (F.e00 f)) (BP.≃-trans (F.e10 e) (F.e10 f)) (BP.≃-trans (F.e20 e) (F.e20 f)) (BP.≃-trans (F.e01 e) (F.e01 f)) (BP.≃-trans (F.e11 e) (F.e11 f)) (BP.≃-trans (F.e21 e) (F.e21 f)) (BP.≃-trans (F.e02 e) (F.e02 f)) (BP.≃-trans (F.e12 e) (F.e12 f)) (BP.≃-trans (F.e22 e) (F.e22 f))

frameSym : {f g : H.Frame3} → F.FrameEq f g → F.FrameEq g f
frameSym (a , (b , c)) = BP.≃-symm a , (BP.≃-symm b , BP.≃-symm c)

-- The complete native numerator, with the actual source norm and
-- actual constructive inverse, respects componentwise equivalence.
normCong : {f g : H.Frame3} → F.FrameEq f g →
  B._≃_ (H.norm4 B.1ℝ (H.Frame3.x f) (H.Frame3.y f) (H.Frame3.z f))
        (H.norm4 B.1ℝ (H.Frame3.x g) (H.Frame3.y g) (H.Frame3.z g))
normCong (ex , (ey , ez)) = (BP.+-cong (BP.*-cong BP.≃-refl BP.≃-refl) (BP.+-cong (BP.*-cong ex ex) (BP.+-cong (BP.*-cong ey ey) (BP.*-cong ez ez))))

rotationCong : {f g : H.Frame3} → F.FrameEq f g →
  F.MatrixEq (H.frameRotation f) (H.frameRotation g)
rotationCong {H.frame3 x y z} {H.frame3 a b c} (ex , (ey , ez)) =
  let f = H.frame3 x y z
      g = H.frame3 a b c
      iEq = A.inverseCongruentApart
        (H.norm4 B.1ℝ x y z) (H.norm4 B.1ℝ a b c)
        (H.leadingOneApart f) (H.leadingOneApart g)
        (normCong {f} {g} (ex , (ey , ez)))
  in F.eq9
    (BP.*-cong iEq (BP.--cong (BP.+-cong (BP.*-cong BP.≃-refl BP.≃-refl) (BP.+-cong (BP.*-cong ex ex) (BP.+-cong (BP.*-cong ey ey) (BP.*-cong ez ez)))) (BP.+-cong (BP.+-cong (BP.*-cong ey ey) (BP.*-cong ez ez)) (BP.+-cong (BP.*-cong ey ey) (BP.*-cong ez ez)))))
    (BP.*-cong iEq (BP.+-cong (BP.+-cong (BP.*-cong ex ey) (BP.*-cong BP.≃-refl ez)) (BP.+-cong (BP.*-cong ex ey) (BP.*-cong BP.≃-refl ez))))
    (BP.*-cong iEq (BP.+-cong (BP.--cong (BP.*-cong ex ez) (BP.*-cong BP.≃-refl ey)) (BP.--cong (BP.*-cong ex ez) (BP.*-cong BP.≃-refl ey))))
    (BP.*-cong iEq (BP.+-cong (BP.--cong (BP.*-cong ex ey) (BP.*-cong BP.≃-refl ez)) (BP.--cong (BP.*-cong ex ey) (BP.*-cong BP.≃-refl ez))))
    (BP.*-cong iEq (BP.--cong (BP.+-cong (BP.*-cong BP.≃-refl BP.≃-refl) (BP.+-cong (BP.*-cong ex ex) (BP.+-cong (BP.*-cong ey ey) (BP.*-cong ez ez)))) (BP.+-cong (BP.+-cong (BP.*-cong ex ex) (BP.*-cong ez ez)) (BP.+-cong (BP.*-cong ex ex) (BP.*-cong ez ez)))))
    (BP.*-cong iEq (BP.+-cong (BP.+-cong (BP.*-cong ey ez) (BP.*-cong BP.≃-refl ex)) (BP.+-cong (BP.*-cong ey ez) (BP.*-cong BP.≃-refl ex))))
    (BP.*-cong iEq (BP.+-cong (BP.+-cong (BP.*-cong ex ez) (BP.*-cong BP.≃-refl ey)) (BP.+-cong (BP.*-cong ex ez) (BP.*-cong BP.≃-refl ey))))
    (BP.*-cong iEq (BP.+-cong (BP.--cong (BP.*-cong ey ez) (BP.*-cong BP.≃-refl ex)) (BP.--cong (BP.*-cong ey ez) (BP.*-cong BP.≃-refl ex))))
    (BP.*-cong iEq (BP.--cong (BP.+-cong (BP.*-cong BP.≃-refl BP.≃-refl) (BP.+-cong (BP.*-cong ex ex) (BP.+-cong (BP.*-cong ey ey) (BP.*-cong ez ez)))) (BP.+-cong (BP.+-cong (BP.*-cong ex ex) (BP.*-cong ey ey)) (BP.+-cong (BP.*-cong ex ex) (BP.*-cong ey ey)))))

flipCong : (k : F.Mark) {r s : H.Matrix3} → F.MatrixEq r s →
  F.MatrixEq (F.flipMatrix k r) (F.flipMatrix k s)
flipCong F.scalar {H.matrix3 (H.vec3 a d g) (H.vec3 b e h) (H.vec3 c f j)}
  {H.matrix3 (H.vec3 a′ d′ g′) (H.vec3 b′ e′ h′) (H.vec3 c′ f′ j′)} eq = F.eq9
  (F.e00 eq) (F.e10 eq) (F.e20 eq) (F.e01 eq) (F.e11 eq) (F.e21 eq) (F.e02 eq) (F.e12 eq) (F.e22 eq)
flipCong F.axisX {H.matrix3 (H.vec3 a d g) (H.vec3 b e h) (H.vec3 c f j)}
  {H.matrix3 (H.vec3 a′ d′ g′) (H.vec3 b′ e′ h′) (H.vec3 c′ f′ j′)} eq = F.eq9
  (F.e00 eq) (BP.-‿cong (F.e10 eq)) (BP.-‿cong (F.e20 eq)) (F.e01 eq) (BP.-‿cong (F.e11 eq)) (BP.-‿cong (F.e21 eq)) (F.e02 eq) (BP.-‿cong (F.e12 eq)) (BP.-‿cong (F.e22 eq))
flipCong F.axisY {H.matrix3 (H.vec3 a d g) (H.vec3 b e h) (H.vec3 c f j)}
  {H.matrix3 (H.vec3 a′ d′ g′) (H.vec3 b′ e′ h′) (H.vec3 c′ f′ j′)} eq = F.eq9
  (BP.-‿cong (F.e00 eq)) (F.e10 eq) (BP.-‿cong (F.e20 eq)) (BP.-‿cong (F.e01 eq)) (F.e11 eq) (BP.-‿cong (F.e21 eq)) (BP.-‿cong (F.e02 eq)) (F.e12 eq) (BP.-‿cong (F.e22 eq))
flipCong F.axisZ {H.matrix3 (H.vec3 a d g) (H.vec3 b e h) (H.vec3 c f j)}
  {H.matrix3 (H.vec3 a′ d′ g′) (H.vec3 b′ e′ h′) (H.vec3 c′ f′ j′)} eq = F.eq9
  (BP.-‿cong (F.e00 eq)) (BP.-‿cong (F.e10 eq)) (F.e20 eq) (BP.-‿cong (F.e01 eq)) (BP.-‿cong (F.e11 eq)) (F.e21 eq) (BP.-‿cong (F.e02 eq)) (BP.-‿cong (F.e12 eq)) (F.e22 eq)

encodeCong : (k : F.Mark) {f g : H.Frame3} → F.FrameEq f g →
  F.MatrixEq (F.encode k f) (F.encode k g)
encodeCong k eq = flipCong k (rotationCong eq)

-- A constructive image witness at the target chart. Not an arbitrary
-- SO3 assertion: it identifies the actual common matrix.
record Image (k : F.Mark) (r : H.Matrix3) : Set where
  constructor image
  field
    coordinates : H.Frame3
    identifies : F.MatrixEq (F.encode k coordinates) r
open Image public

imagePositive : {k : F.Mark} {r : H.Matrix3} →
  Image k r → B._<_ B.0ℝ (H.traceDenominator (F.flipMatrix k r))
imagePositive {k} (image f e) =
  BP.<-respʳ-≃ (F.traceCong (flipCong k e)) (F.encodePositive k f)

readImage : {k : F.Mark} {r : H.Matrix3} → Image k r → H.Frame3
readImage {k} {r} i = F.decode k r (inj₂ (imagePositive i))

-- Actual decoder, independent of the stored image coordinates.
-- The image witness proves that this decoder returns the same ray.
readRecovers : {k : F.Mark} {r : H.Matrix3} (i : Image k r) →
  F.FrameEq (readImage i) (coordinates i)
readRecovers {k} {r} i@(image f e) = F.frameTrans
  (F.recoverCong (F.flipMatrix k r) (F.flipMatrix k (F.encode k f))
    (inj₂ (imagePositive i)) (inj₂ (F.encodePositive k f))
    (flipCong k (matrixSym e)))
  (F.reopens k f)

-- Native right inverse on the actual certified chart image.
readRecloses : {k : F.Mark} {r : H.Matrix3} (i : Image k r) →
  F.MatrixEq (F.encode k (readImage i)) r
readRecloses {k} i = matrixTrans
  (encodeCong k (readRecovers i)) (identifies i)

transportImage : {k : F.Mark} {r s : H.Matrix3} →
  Image k r → F.MatrixEq r s → Image k s
transportImage (image f e) eq = image f (matrixTrans e eq)

-- A transition decodes the ACTUAL input matrix, not the common stored
-- coordinates. Target positivity is transported using its image witness.
transition : (a b : F.Mark) (f : H.Frame3) →
  Image b (F.encode a f) → H.Frame3
transition a b f i = readImage i

transitionPreserves : (a b : F.Mark) (f : H.Frame3)
  (i : Image b (F.encode a f)) →
  F.MatrixEq (F.encode b (transition a b f i)) (F.encode a f)
transitionPreserves a b f i = readRecloses i

-- On three certified overlapping domains, two actual rechart operations
-- agree with the direct one, componentwise. No sign/winding is inferred
-- from the spatial matrix; those remain independently retained.
transitionCocycle : (a b c : F.Mark) (f : H.Frame3)
  (ib : Image b (F.encode a f)) (ic : Image c (F.encode a f)) →
  let g = transition a b f ib
      ic′ = transportImage ic (matrixSym (transitionPreserves a b f ib))
  in F.FrameEq (transition b c g ic′) (transition a c f ic)
transitionCocycle a b c f ib ic =
  let g = transition a b f ib
      e = transitionPreserves a b f ib
      ic′ = transportImage ic (matrixSym e)
  in F.recoverCong (F.flipMatrix c (F.encode b g))
    (F.flipMatrix c (F.encode a f))
    (inj₂ (imagePositive ic′)) (inj₂ (imagePositive ic))
    (flipCong c e)

-- All four selected native charts participate. Image membership is
-- constructive evidence, not an unproved global SO3 selector.
