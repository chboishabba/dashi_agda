module DASHI.Reasoning.H07AtlasProjectionLawsExact where

-- Attach literal H07 projection to the existing Base369 field and finite
-- linear map API. Source-written; no Agda kernel acceptance claimed.
open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)
open import Base369 using (TriTruth; tri-low; tri-mid; tri-high)
import DASHI.Foundations.Base369TriTruthField as F
import DASHI.Foundations.FiniteLinear.F3Subspace as L
import DASHI.Foundations.FiniteLinear.AntiDiagonalKernel as D
import DASHI.Codec.IndexedCubeMarkedAffine9Exact as A
import DASHI.Codec.IndexedCubeAffinePivotOverlapExact as O
import DASHI.Reasoning.H07FullAtlasSectionExact as H
import DASHI.Reasoning.H07AffinePairedSeamExact as S
import DASHI.Reasoning.TypedHyperfabricCore as Fabric

-- Arithmetic representation, NOT SSP semantic low/mid/high ordering.
toField : Trit → TriTruth
toField zer = tri-low
toField pos = tri-mid
toField neg = tri-high

fromField : TriTruth → Trit
fromField tri-low = zer
fromField tri-mid = pos
fromField tri-high = neg

fromTo : (a : Trit) → fromField (toField a) ≡ a
fromTo neg = refl
fromTo zer = refl
fromTo pos = refl

toFrom : (a : TriTruth) → toField (fromField a) ≡ a
toFrom tri-low = refl
toFrom tri-mid = refl
toFrom tri-high = refl

toInjective : {a b : Trit} → toField a ≡ toField b → a ≡ b
toInjective {a} {b} eq =
  trans (sym (fromTo a)) (trans (cong fromField eq) (fromTo b))

toAdd : (a b : Trit) → toField (A.add3 a b) ≡ F.triAdd (toField a) (toField b)
toAdd neg neg = refl
toAdd neg zer = refl
toAdd neg pos = refl
toAdd zer neg = refl
toAdd zer zer = refl
toAdd zer pos = refl
toAdd pos neg = refl
toAdd pos zer = refl
toAdd pos pos = refl

toMul : (a b : Trit) → toField (A.mul3 a b) ≡ F.triMul (toField a) (toField b)
toMul neg neg = refl
toMul neg zer = refl
toMul neg pos = refl
toMul zer neg = refl
toMul zer zer = refl
toMul zer pos = refl
toMul pos neg = refl
toMul pos zer = refl
toMul pos pos = refl

toNeg : (a : Trit) → toField (inv a) ≡ F.triNeg (toField a)
toNeg neg = refl
toNeg zer = refl
toNeg pos = refl

-- Transport established field/linear API lemmas, not a parallel field.
mulAdd : (a b c : Trit) → (A.mul3 a (A.add3 b c)) ≡ (A.add3 (A.mul3 a b) (A.mul3 a c))
mulAdd a b c = toInjective {(A.mul3 a (A.add3 b c))} {(A.add3 (A.mul3 a b) (A.mul3 a c))}
  (trans (trans (toMul a (A.add3 b c)) (cong₂ F.triMul refl (trans (toAdd b c) (cong₂ F.triAdd refl refl))))
    (trans (F.triDistribˡ (toField a) (toField b) (toField c)) (sym (trans (toAdd (A.mul3 a b) (A.mul3 a c)) (cong₂ F.triAdd (trans (toMul a b) (cong₂ F.triMul refl refl)) (trans (toMul a c) (cong₂ F.triMul refl refl)))))))

addMul : (a b c : Trit) → (A.mul3 (A.add3 a b) c) ≡ (A.add3 (A.mul3 a c) (A.mul3 b c))
addMul a b c = toInjective {(A.mul3 (A.add3 a b) c)} {(A.add3 (A.mul3 a c) (A.mul3 b c))}
  (trans (trans (toMul (A.add3 a b) c) (cong₂ F.triMul (trans (toAdd a b) (cong₂ F.triAdd refl refl)) refl))
    (trans (F.triDistribʳ (toField a) (toField b) (toField c)) (sym (trans (toAdd (A.mul3 a c) (A.mul3 b c)) (cong₂ F.triAdd (trans (toMul a c) (cong₂ F.triMul refl refl)) (trans (toMul b c) (cong₂ F.triMul refl refl)))))))

interchange : (a b c d : Trit) → (A.add3 (A.add3 a b) (A.add3 c d)) ≡ (A.add3 (A.add3 a c) (A.add3 b d))
interchange a b c d = toInjective {(A.add3 (A.add3 a b) (A.add3 c d))} {(A.add3 (A.add3 a c) (A.add3 b d))}
  (trans (trans (toAdd (A.add3 a b) (A.add3 c d)) (cong₂ F.triAdd (trans (toAdd a b) (cong₂ F.triAdd refl refl)) (trans (toAdd c d) (cong₂ F.triAdd refl refl))))
    (trans (L.addInterchange (toField a) (toField b) (toField c) (toField d)) (sym (trans (toAdd (A.add3 a c) (A.add3 b d)) (cong₂ F.triAdd (trans (toAdd a c) (cong₂ F.triAdd refl refl)) (trans (toAdd b d) (cong₂ F.triAdd refl refl)))))))

mulMove : (a b c : Trit) → (A.mul3 a (A.mul3 b c)) ≡ (A.mul3 b (A.mul3 a c))
mulMove a b c = toInjective {(A.mul3 a (A.mul3 b c))} {(A.mul3 b (A.mul3 a c))}
  (trans (trans (toMul a (A.mul3 b c)) (cong₂ F.triMul refl (trans (toMul b c) (cong₂ F.triMul refl refl))))
    (trans (L.mulReassociateRight (toField b) (toField a) (toField c)) (sym (trans (toMul b (A.mul3 a c)) (cong₂ F.triMul refl (trans (toMul a c) (cong₂ F.triMul refl refl)))))))

mulNest : (a b c : Trit) → (A.mul3 (A.mul3 a b) c) ≡ (A.mul3 a (A.mul3 b c))
mulNest a b c = toInjective {(A.mul3 (A.mul3 a b) c)} {(A.mul3 a (A.mul3 b c))}
  (trans (trans (toMul (A.mul3 a b) c) (cong₂ F.triMul (trans (toMul a b) (cong₂ F.triMul refl refl)) refl))
    (trans (sym (F.triMul-assoc (toField a) (toField b) (toField c))) (sym (trans (toMul a (A.mul3 b c)) (cong₂ F.triMul refl (trans (toMul b c) (cong₂ F.triMul refl refl)))))))

negAdd : (a b : Trit) → (inv (A.add3 a b)) ≡ (A.add3 (inv a) (inv b))
negAdd a b = toInjective {(inv (A.add3 a b))} {(A.add3 (inv a) (inv b))}
  (trans (trans (toNeg (A.add3 a b)) (cong F.triNeg (trans (toAdd a b) (cong₂ F.triAdd refl refl))))
    (trans (D.negAdd (toField a) (toField b)) (sym (trans (toAdd (inv a) (inv b)) (cong₂ F.triAdd (trans (toNeg a) (cong F.triNeg refl)) (trans (toNeg b) (cong F.triNeg refl)))))))

negScale : (a b : Trit) → (inv (A.mul3 a b)) ≡ (A.mul3 a (inv b))
negScale a b = toInjective {(inv (A.mul3 a b))} {(A.mul3 a (inv b))}
  (trans (trans (toNeg (A.mul3 a b)) (cong F.triNeg (trans (toMul a b) (cong₂ F.triMul refl refl))))
    (trans (D.negScale (toField a) (toField b)) (sym (trans (toMul a (inv b)) (cong₂ F.triMul refl (trans (toNeg b) (cong F.triNeg refl)))))))

-- Small composite identities on the literal balanced-trit operations.
subAddS : (a b c d : Trit) → A.add3 (A.add3 a b) (A.mul3 neg (A.add3 c d)) ≡ A.add3 (A.add3 a (A.mul3 neg c)) (A.add3 b (A.mul3 neg d))
subAddS neg neg neg neg = refl
subAddS neg neg neg zer = refl
subAddS neg neg neg pos = refl
subAddS neg neg zer neg = refl
subAddS neg neg zer zer = refl
subAddS neg neg zer pos = refl
subAddS neg neg pos neg = refl
subAddS neg neg pos zer = refl
subAddS neg neg pos pos = refl
subAddS neg zer neg neg = refl
subAddS neg zer neg zer = refl
subAddS neg zer neg pos = refl
subAddS neg zer zer neg = refl
subAddS neg zer zer zer = refl
subAddS neg zer zer pos = refl
subAddS neg zer pos neg = refl
subAddS neg zer pos zer = refl
subAddS neg zer pos pos = refl
subAddS neg pos neg neg = refl
subAddS neg pos neg zer = refl
subAddS neg pos neg pos = refl
subAddS neg pos zer neg = refl
subAddS neg pos zer zer = refl
subAddS neg pos zer pos = refl
subAddS neg pos pos neg = refl
subAddS neg pos pos zer = refl
subAddS neg pos pos pos = refl
subAddS zer neg neg neg = refl
subAddS zer neg neg zer = refl
subAddS zer neg neg pos = refl
subAddS zer neg zer neg = refl
subAddS zer neg zer zer = refl
subAddS zer neg zer pos = refl
subAddS zer neg pos neg = refl
subAddS zer neg pos zer = refl
subAddS zer neg pos pos = refl
subAddS zer zer neg neg = refl
subAddS zer zer neg zer = refl
subAddS zer zer neg pos = refl
subAddS zer zer zer neg = refl
subAddS zer zer zer zer = refl
subAddS zer zer zer pos = refl
subAddS zer zer pos neg = refl
subAddS zer zer pos zer = refl
subAddS zer zer pos pos = refl
subAddS zer pos neg neg = refl
subAddS zer pos neg zer = refl
subAddS zer pos neg pos = refl
subAddS zer pos zer neg = refl
subAddS zer pos zer zer = refl
subAddS zer pos zer pos = refl
subAddS zer pos pos neg = refl
subAddS zer pos pos zer = refl
subAddS zer pos pos pos = refl
subAddS pos neg neg neg = refl
subAddS pos neg neg zer = refl
subAddS pos neg neg pos = refl
subAddS pos neg zer neg = refl
subAddS pos neg zer zer = refl
subAddS pos neg zer pos = refl
subAddS pos neg pos neg = refl
subAddS pos neg pos zer = refl
subAddS pos neg pos pos = refl
subAddS pos zer neg neg = refl
subAddS pos zer neg zer = refl
subAddS pos zer neg pos = refl
subAddS pos zer zer neg = refl
subAddS pos zer zer zer = refl
subAddS pos zer zer pos = refl
subAddS pos zer pos neg = refl
subAddS pos zer pos zer = refl
subAddS pos zer pos pos = refl
subAddS pos pos neg neg = refl
subAddS pos pos neg zer = refl
subAddS pos pos neg pos = refl
subAddS pos pos zer neg = refl
subAddS pos pos zer zer = refl
subAddS pos pos zer pos = refl
subAddS pos pos pos neg = refl
subAddS pos pos pos zer = refl
subAddS pos pos pos pos = refl

subScaleS : (n a b : Trit) → A.add3 (A.mul3 n a) (A.mul3 neg (A.mul3 n b)) ≡ A.mul3 n (A.add3 a (A.mul3 neg b))
subScaleS neg neg neg = refl
subScaleS neg neg zer = refl
subScaleS neg neg pos = refl
subScaleS neg zer neg = refl
subScaleS neg zer zer = refl
subScaleS neg zer pos = refl
subScaleS neg pos neg = refl
subScaleS neg pos zer = refl
subScaleS neg pos pos = refl
subScaleS zer neg neg = refl
subScaleS zer neg zer = refl
subScaleS zer neg pos = refl
subScaleS zer zer neg = refl
subScaleS zer zer zer = refl
subScaleS zer zer pos = refl
subScaleS zer pos neg = refl
subScaleS zer pos zer = refl
subScaleS zer pos pos = refl
subScaleS pos neg neg = refl
subScaleS pos neg zer = refl
subScaleS pos neg pos = refl
subScaleS pos zer neg = refl
subScaleS pos zer zer = refl
subScaleS pos zer pos = refl
subScaleS pos pos neg = refl
subScaleS pos pos zer = refl
subScaleS pos pos pos = refl

shiftS : (n x p q : Trit) → A.add3 (A.add3 x (A.mul3 n q)) (A.mul3 n (A.add3 p (A.mul3 neg q))) ≡ A.add3 x (A.mul3 n p)
shiftS neg neg neg neg = refl
shiftS neg neg neg zer = refl
shiftS neg neg neg pos = refl
shiftS neg neg zer neg = refl
shiftS neg neg zer zer = refl
shiftS neg neg zer pos = refl
shiftS neg neg pos neg = refl
shiftS neg neg pos zer = refl
shiftS neg neg pos pos = refl
shiftS neg zer neg neg = refl
shiftS neg zer neg zer = refl
shiftS neg zer neg pos = refl
shiftS neg zer zer neg = refl
shiftS neg zer zer zer = refl
shiftS neg zer zer pos = refl
shiftS neg zer pos neg = refl
shiftS neg zer pos zer = refl
shiftS neg zer pos pos = refl
shiftS neg pos neg neg = refl
shiftS neg pos neg zer = refl
shiftS neg pos neg pos = refl
shiftS neg pos zer neg = refl
shiftS neg pos zer zer = refl
shiftS neg pos zer pos = refl
shiftS neg pos pos neg = refl
shiftS neg pos pos zer = refl
shiftS neg pos pos pos = refl
shiftS zer neg neg neg = refl
shiftS zer neg neg zer = refl
shiftS zer neg neg pos = refl
shiftS zer neg zer neg = refl
shiftS zer neg zer zer = refl
shiftS zer neg zer pos = refl
shiftS zer neg pos neg = refl
shiftS zer neg pos zer = refl
shiftS zer neg pos pos = refl
shiftS zer zer neg neg = refl
shiftS zer zer neg zer = refl
shiftS zer zer neg pos = refl
shiftS zer zer zer neg = refl
shiftS zer zer zer zer = refl
shiftS zer zer zer pos = refl
shiftS zer zer pos neg = refl
shiftS zer zer pos zer = refl
shiftS zer zer pos pos = refl
shiftS zer pos neg neg = refl
shiftS zer pos neg zer = refl
shiftS zer pos neg pos = refl
shiftS zer pos zer neg = refl
shiftS zer pos zer zer = refl
shiftS zer pos zer pos = refl
shiftS zer pos pos neg = refl
shiftS zer pos pos zer = refl
shiftS zer pos pos pos = refl
shiftS pos neg neg neg = refl
shiftS pos neg neg zer = refl
shiftS pos neg neg pos = refl
shiftS pos neg zer neg = refl
shiftS pos neg zer zer = refl
shiftS pos neg zer pos = refl
shiftS pos neg pos neg = refl
shiftS pos neg pos zer = refl
shiftS pos neg pos pos = refl
shiftS pos zer neg neg = refl
shiftS pos zer neg zer = refl
shiftS pos zer neg pos = refl
shiftS pos zer zer neg = refl
shiftS pos zer zer zer = refl
shiftS pos zer zer pos = refl
shiftS pos zer pos neg = refl
shiftS pos zer pos zer = refl
shiftS pos zer pos pos = refl
shiftS pos pos neg neg = refl
shiftS pos pos neg zer = refl
shiftS pos pos neg pos = refl
shiftS pos pos zer neg = refl
shiftS pos pos zer zer = refl
shiftS pos pos zer pos = refl
shiftS pos pos pos neg = refl
shiftS pos pos pos zer = refl
shiftS pos pos pos pos = refl

addRightS : (a : Trit) → A.add3 a zer ≡ a
addRightS neg = refl
addRightS zer = refl
addRightS pos = refl

addLeftS : (a : Trit) → A.add3 zer a ≡ a
addLeftS neg = refl
addLeftS zer = refl
addLeftS pos = refl

oneS : (a : Trit) → A.mul3 pos a ≡ a
oneS neg = refl
oneS zer = refl
oneS pos = refl

zeroS : (a : Trit) → A.mul3 zer a ≡ zer
zeroS neg = refl
zeroS zer = refl
zeroS pos = refl

selfS : (a : Trit) → A.add3 a (A.mul3 neg a) ≡ zer
selfS neg = refl
selfS zer = refl
selfS pos = refl

subZeroS : (a : Trit) → A.add3 a (A.mul3 neg zer) ≡ a
subZeroS neg = refl
subZeroS zer = refl
subZeroS pos = refl

zeroV : H.Vec5
zeroV = H.vec5 zer zer zer zer zer

vecCong : ∀ {a b c d e f g h i j : Trit} →
  a ≡ f → b ≡ g → c ≡ h → d ≡ i → e ≡ j →
  H.vec5 a b c d e ≡ H.vec5 f g h i j
vecCong refl refl refl refl refl = refl

scaleAdd : (n : Trit) (x y : H.Vec5) → H.scale n (H.add x y) ≡ H.add (H.scale n x) (H.scale n y)
scaleAdd n (H.vec5 x0 x1 x2 x3 x4) (H.vec5 y0 y1 y2 y3 y4) = vecCong
  (mulAdd n x0 y0)
  (mulAdd n x1 y1)
  (mulAdd n x2 y2)
  (mulAdd n x3 y3)
  (mulAdd n x4 y4)

scaleSum : (n m : Trit) (x : H.Vec5) → H.scale (A.add3 n m) x ≡ H.add (H.scale n x) (H.scale m x)
scaleSum n m (H.vec5 x0 x1 x2 x3 x4) = vecCong
  (addMul n m x0)
  (addMul n m x1)
  (addMul n m x2)
  (addMul n m x3)
  (addMul n m x4)

scaleNest : (n m : Trit) (x : H.Vec5) → H.scale (A.mul3 n m) x ≡ H.scale n (H.scale m x)
scaleNest n m (H.vec5 x0 x1 x2 x3 x4) = vecCong
  (mulNest n m x0)
  (mulNest n m x1)
  (mulNest n m x2)
  (mulNest n m x3)
  (mulNest n m x4)

addInterchange : (x y z w : H.Vec5) → H.add (H.add x y) (H.add z w) ≡ H.add (H.add x z) (H.add y w)
addInterchange (H.vec5 x0 x1 x2 x3 x4) (H.vec5 y0 y1 y2 y3 y4) (H.vec5 z0 z1 z2 z3 z4) (H.vec5 w0 w1 w2 w3 w4) = vecCong
  (interchange x0 y0 z0 w0)
  (interchange x1 y1 z1 w1)
  (interchange x2 y2 z2 w2)
  (interchange x3 y3 z3 w3)
  (interchange x4 y4 z4 w4)

subAdd : (x y z w : H.Vec5) → H.sub (H.add x y) (H.add z w) ≡ H.add (H.sub x z) (H.sub y w)
subAdd (H.vec5 x0 x1 x2 x3 x4) (H.vec5 y0 y1 y2 y3 y4) (H.vec5 z0 z1 z2 z3 z4) (H.vec5 w0 w1 w2 w3 w4) = vecCong
  (subAddS x0 y0 z0 w0)
  (subAddS x1 y1 z1 w1)
  (subAddS x2 y2 z2 w2)
  (subAddS x3 y3 z3 w3)
  (subAddS x4 y4 z4 w4)

subScale : (n : Trit) (x y : H.Vec5) → H.sub (H.scale n x) (H.scale n y) ≡ H.scale n (H.sub x y)
subScale n (H.vec5 x0 x1 x2 x3 x4) (H.vec5 y0 y1 y2 y3 y4) = vecCong
  (subScaleS n x0 y0)
  (subScaleS n x1 y1)
  (subScaleS n x2 y2)
  (subScaleS n x3 y3)
  (subScaleS n x4 y4)

shiftCancel : (n : Trit) (x p q : H.Vec5) → H.add (H.add x (H.scale n q)) (H.scale n (H.sub p q)) ≡ H.add x (H.scale n p)
shiftCancel n (H.vec5 x0 x1 x2 x3 x4) (H.vec5 p0 p1 p2 p3 p4) (H.vec5 q0 q1 q2 q3 q4) = vecCong
  (shiftS n x0 p0 q0)
  (shiftS n x1 p1 q1)
  (shiftS n x2 p2 q2)
  (shiftS n x3 p3 q3)
  (shiftS n x4 p4 q4)

addRight : (x : H.Vec5) → H.add x zeroV ≡ x
addRight (H.vec5 x0 x1 x2 x3 x4) = vecCong
  (addRightS x0)
  (addRightS x1)
  (addRightS x2)
  (addRightS x3)
  (addRightS x4)

addLeft : (x : H.Vec5) → H.add zeroV x ≡ x
addLeft (H.vec5 x0 x1 x2 x3 x4) = vecCong
  (addLeftS x0)
  (addLeftS x1)
  (addLeftS x2)
  (addLeftS x3)
  (addLeftS x4)

scaleOne : (x : H.Vec5) → H.scale pos x ≡ x
scaleOne (H.vec5 x0 x1 x2 x3 x4) = vecCong
  (oneS x0)
  (oneS x1)
  (oneS x2)
  (oneS x3)
  (oneS x4)

scaleZero : (x : H.Vec5) → H.scale zer x ≡ zeroV
scaleZero (H.vec5 x0 x1 x2 x3 x4) = vecCong
  (zeroS x0)
  (zeroS x1)
  (zeroS x2)
  (zeroS x3)
  (zeroS x4)

subSelf : (x : H.Vec5) → H.sub x x ≡ zeroV
subSelf (H.vec5 x0 x1 x2 x3 x4) = vecCong
  (selfS x0)
  (selfS x1)
  (selfS x2)
  (selfS x3)
  (selfS x4)

subZero : (x : H.Vec5) → H.sub x zeroV ≡ x
subZero (H.vec5 x0 x1 x2 x3 x4) = vecCong
  (subZeroS x0)
  (subZeroS x1)
  (subZeroS x2)
  (subZeroS x3)
  (subZeroS x4)

atAdd : (i : H.Axis) (x y : H.Vec5) →
  H.at i (H.add x y) ≡ A.add3 (H.at i x) (H.at i y)
atAdd H.a0 (H.vec5 a b c d e) (H.vec5 f g h j k) = refl
atAdd H.a1 (H.vec5 a b c d e) (H.vec5 f g h j k) = refl
atAdd H.a2 (H.vec5 a b c d e) (H.vec5 f g h j k) = refl
atAdd H.a3 (H.vec5 a b c d e) (H.vec5 f g h j k) = refl
atAdd H.a4 (H.vec5 a b c d e) (H.vec5 f g h j k) = refl

atScale : (i : H.Axis) (n : Trit) (x : H.Vec5) →
  H.at i (H.scale n x) ≡ A.mul3 n (H.at i x)
atScale H.a0 n (H.vec5 a b c d e) = refl
atScale H.a1 n (H.vec5 a b c d e) = refl
atScale H.a2 n (H.vec5 a b c d e) = refl
atScale H.a3 n (H.vec5 a b c d e) = refl
atScale H.a4 n (H.vec5 a b c d e) = refl

linear2Add : (d a b x y z w : Trit) →
  H.linear2 d a b (A.add3 x z) (A.add3 y w) ≡
  A.add3 (H.linear2 d a b x y) (H.linear2 d a b z w)
linear2Add d a b x y z w
  rewrite mulAdd a x z | mulAdd b y w
        | negAdd (A.mul3 b y) (A.mul3 b w)
        | interchange (A.mul3 a x) (A.mul3 a z)
            (inv (A.mul3 b y)) (inv (A.mul3 b w))
        | mulAdd d (A.add3 (A.mul3 a x) (inv (A.mul3 b y)))
                   (A.add3 (A.mul3 a z) (inv (A.mul3 b w))) = refl

linear2Scale : (d a b n x y : Trit) →
  H.linear2 d a b (A.mul3 n x) (A.mul3 n y) ≡
  A.mul3 n (H.linear2 d a b x y)
linear2Scale d a b n x y
  rewrite mulMove a n x | mulMove b n y
        | negScale n (A.mul3 b y)
        | sym (mulAdd n (A.mul3 a x) (inv (A.mul3 b y)))
        | mulMove d n (A.add3 (A.mul3 a x) (inv (A.mul3 b y))) = refl

coefficientAAdd : {V : H.Direction} (q : H.Mark V) (x y : H.Vec5) →
  H.coefficientA q (H.add x y) ≡ A.add3 (H.coefficientA q x) (H.coefficientA q y)
coefficientAAdd {H.direction u v} (H.mark p nz) x y
  rewrite atAdd (H.first p) x y | atAdd (H.second p) x y =
  linear2Add (O.reciprocal (H.determinant (H.direction u v) p) nz)
    (H.at (H.second p) v) (H.at (H.first p) v)
    (H.at (H.first p) x) (H.at (H.second p) x)
    (H.at (H.first p) y) (H.at (H.second p) y)

coefficientBAdd : {V : H.Direction} (q : H.Mark V) (x y : H.Vec5) →
  H.coefficientB q (H.add x y) ≡ A.add3 (H.coefficientB q x) (H.coefficientB q y)
coefficientBAdd {H.direction u v} (H.mark p nz) x y
  rewrite atAdd (H.first p) x y | atAdd (H.second p) x y =
  linear2Add (O.reciprocal (H.determinant (H.direction u v) p) nz)
    (H.at (H.first p) u) (H.at (H.second p) u)
    (H.at (H.second p) x) (H.at (H.first p) x)
    (H.at (H.second p) y) (H.at (H.first p) y)

coefficientAScale : {V : H.Direction} (q : H.Mark V) (n : Trit) (x : H.Vec5) →
  H.coefficientA q (H.scale n x) ≡ A.mul3 n (H.coefficientA q x)
coefficientAScale {H.direction u v} (H.mark p nz) n x
  rewrite atScale (H.first p) n x | atScale (H.second p) n x =
  linear2Scale (O.reciprocal (H.determinant (H.direction u v) p) nz)
    (H.at (H.second p) v) (H.at (H.first p) v) n
    (H.at (H.first p) x) (H.at (H.second p) x)

coefficientBScale : {V : H.Direction} (q : H.Mark V) (n : Trit) (x : H.Vec5) →
  H.coefficientB q (H.scale n x) ≡ A.mul3 n (H.coefficientB q x)
coefficientBScale {H.direction u v} (H.mark p nz) n x
  rewrite atScale (H.first p) n x | atScale (H.second p) n x =
  linear2Scale (O.reciprocal (H.determinant (H.direction u v) p) nz)
    (H.at (H.first p) u) (H.at (H.second p) u) n
    (H.at (H.second p) x) (H.at (H.first p) x)

projectAdd : {V : H.Direction} (q : H.Mark V) (x y : H.Vec5) →
  H.project q (H.add x y) ≡ H.add (H.project q x) (H.project q y)
projectAdd {H.direction u v} q x y
  rewrite coefficientAAdd q x y | coefficientBAdd q x y
        | scaleSum (H.coefficientA q x) (H.coefficientA q y) u
        | scaleSum (H.coefficientB q x) (H.coefficientB q y) v
        | addInterchange (H.scale (H.coefficientA q x) u)
            (H.scale (H.coefficientA q y) u)
            (H.scale (H.coefficientB q x) v)
            (H.scale (H.coefficientB q y) v) =
  subAdd x y
    (H.add (H.scale (H.coefficientA q x) u) (H.scale (H.coefficientB q x) v))
    (H.add (H.scale (H.coefficientA q y) u) (H.scale (H.coefficientB q y) v))

projectScale : {V : H.Direction} (q : H.Mark V) (n : Trit) (x : H.Vec5) →
  H.project q (H.scale n x) ≡ H.scale n (H.project q x)
projectScale {H.direction u v} q n x
  rewrite coefficientAScale q n x | coefficientBScale q n x
        | scaleNest n (H.coefficientA q x) u
        | scaleNest n (H.coefficientB q x) v
        | sym (scaleAdd n (H.scale (H.coefficientA q x) u)
                           (H.scale (H.coefficientB q x) v)) =
  subScale n x
    (H.add (H.scale (H.coefficientA q x) u) (H.scale (H.coefficientB q x) v))

projectZero : {V : H.Direction} (q : H.Mark V) → H.project q zeroV ≡ zeroV
projectZero q = trans (cong (H.project q) (sym (scaleZero zeroV)))
  (trans (projectScale q zer zeroV) (scaleZero (H.project q zeroV)))

scaleFieldZero : (a : TriTruth) → H.scale (fromField a) zeroV ≡ zeroV
scaleFieldZero tri-low = refl
scaleFieldZero tri-mid = refl
scaleFieldZero tri-high = refl

vecSpace : L.F3Space
vecSpace = record
  { Carrier = H.Vec5 ; zero = zeroV ; add = H.add
  ; scale = λ a → H.scale (fromField a)
  ; addZeroZero = refl ; scaleZero = scaleFieldZero }

projectionMap : {V : H.Direction} → H.Mark V → L.F3LinearMap vecSpace vecSpace
projectionMap q = record
  { apply = H.project q ; preservesZero = projectZero q
  ; preservesAdd = projectAdd q
  ; preservesScale = λ a → projectScale q (fromField a) }

-- Actual inverse-column certificate on the four pivot entries, not the
-- millions of ambient points. 48 invertible matrices, 33 singular refusals.
det2 : Trit → Trit → Trit → Trit → Trit
det2 a b c d = A.add3 (A.mul3 a d) (inv (A.mul3 c b))

record InverseColumns (a b c d : Trit) (nz : O.Nonzero (det2 a b c d)) : Set where
  field
    au : H.linear2 (O.reciprocal (det2 a b c d) nz) d b a c ≡ pos
    bu : H.linear2 (O.reciprocal (det2 a b c d) nz) a c c a ≡ zer
    av : H.linear2 (O.reciprocal (det2 a b c d) nz) d b b d ≡ zer
    bv : H.linear2 (O.reciprocal (det2 a b c d) nz) a c d b ≡ pos

inverseColumns : (a b c d : Trit) (nz : O.Nonzero (det2 a b c d)) →
  InverseColumns a b c d nz
inverseColumns neg neg neg neg ()
inverseColumns neg neg neg zer O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns neg neg neg pos O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns neg neg zer neg O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns neg neg zer zer ()
inverseColumns neg neg zer pos O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns neg neg pos neg O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns neg neg pos zer O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns neg neg pos pos ()
inverseColumns neg zer neg neg O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns neg zer neg zer ()
inverseColumns neg zer neg pos O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns neg zer zer neg O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns neg zer zer zer ()
inverseColumns neg zer zer pos O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns neg zer pos neg O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns neg zer pos zer ()
inverseColumns neg zer pos pos O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns neg pos neg neg O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns neg pos neg zer O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns neg pos neg pos ()
inverseColumns neg pos zer neg O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns neg pos zer zer ()
inverseColumns neg pos zer pos O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns neg pos pos neg ()
inverseColumns neg pos pos zer O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns neg pos pos pos O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns zer neg neg neg O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns zer neg neg zer O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns zer neg neg pos O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns zer neg zer neg ()
inverseColumns zer neg zer zer ()
inverseColumns zer neg zer pos ()
inverseColumns zer neg pos neg O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns zer neg pos zer O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns zer neg pos pos O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns zer zer neg neg ()
inverseColumns zer zer neg zer ()
inverseColumns zer zer neg pos ()
inverseColumns zer zer zer neg ()
inverseColumns zer zer zer zer ()
inverseColumns zer zer zer pos ()
inverseColumns zer zer pos neg ()
inverseColumns zer zer pos zer ()
inverseColumns zer zer pos pos ()
inverseColumns zer pos neg neg O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns zer pos neg zer O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns zer pos neg pos O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns zer pos zer neg ()
inverseColumns zer pos zer zer ()
inverseColumns zer pos zer pos ()
inverseColumns zer pos pos neg O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns zer pos pos zer O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns zer pos pos pos O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos neg neg neg O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos neg neg zer O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos neg neg pos ()
inverseColumns pos neg zer neg O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos neg zer zer ()
inverseColumns pos neg zer pos O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos neg pos neg ()
inverseColumns pos neg pos zer O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos neg pos pos O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos zer neg neg O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos zer neg zer ()
inverseColumns pos zer neg pos O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos zer zer neg O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos zer zer zer ()
inverseColumns pos zer zer pos O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos zer pos neg O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos zer pos zer ()
inverseColumns pos zer pos pos O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos pos neg neg ()
inverseColumns pos pos neg zer O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos pos neg pos O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos pos zer neg O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos pos zer zer ()
inverseColumns pos pos zer pos O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos pos pos neg O.positive = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos pos pos zer O.negative = record { au = refl ; bu = refl ; av = refl ; bv = refl }
inverseColumns pos pos pos pos ()

projectU : {V : H.Direction} (q : H.Mark V) → H.project q (H.Direction.u V) ≡ zeroV
projectU {H.direction u v} (H.mark p nz)
  rewrite InverseColumns.au proof | InverseColumns.bu proof
        | scaleOne u | scaleZero v | addRight u = subSelf u
  where
    proof = inverseColumns (H.at (H.first p) u) (H.at (H.first p) v)
      (H.at (H.second p) u) (H.at (H.second p) v) nz

projectV : {V : H.Direction} (q : H.Mark V) → H.project q (H.Direction.v V) ≡ zeroV
projectV {H.direction u v} (H.mark p nz)
  rewrite InverseColumns.av proof | InverseColumns.bv proof
        | scaleZero u | scaleOne v | addLeft v = subSelf v
  where
    proof = inverseColumns (H.at (H.first p) u) (H.at (H.first p) v)
      (H.at (H.second p) u) (H.at (H.second p) v) nz

-- Explicitly retain the direction columns: they inhabit the existing
-- linear kernel, not an erased state or a claimed missing physical mode.
directionUInKernel : {V : H.Direction} (q : H.Mark V) →
  L.Member (L.kernel (projectionMap q)) (H.Direction.u V)
directionUInKernel = projectU

directionVInKernel : {V : H.Direction} (q : H.Mark V) →
  L.Member (L.kernel (projectionMap q)) (H.Direction.v V)
directionVInKernel = projectV

projectSub : {V : H.Direction} (q : H.Mark V) (x y : H.Vec5) →
  H.project q (H.sub x y) ≡ H.sub (H.project q x) (H.project q y)
projectSub q x y = trans (projectAdd q x (H.scale neg y))
  (cong (H.add (H.project q x)) (projectScale q neg y))

scaleAtZero : (n : Trit) → H.scale n zeroV ≡ zeroV
scaleAtZero neg = refl
scaleAtZero zer = refl
scaleAtZero pos = refl

projectSpan : {V : H.Direction} (q : H.Mark V) (a b : Trit) →
  H.project q (H.add (H.scale a (H.Direction.u V)) (H.scale b (H.Direction.v V))) ≡ zeroV
projectSpan {H.direction u v} q a b =
  trans (projectAdd q (H.scale a u) (H.scale b v))
    (trans (cong₂ H.add
      (trans (projectScale q a u) (trans (cong (H.scale a) (projectU q)) (scaleAtZero a)))
      (trans (projectScale q b v) (trans (cong (H.scale b) (projectV q)) (scaleAtZero b)))) refl)

projectCompose : {V : H.Direction} (v q : H.Mark V) (x : H.Vec5) →
  H.project q (H.project v x) ≡ H.project q x
projectCompose {H.direction u w} v q x =
  trans (projectSub q x (H.add (H.scale (H.coefficientA v x) u)
                              (H.scale (H.coefficientB v x) w)))
    (trans (cong (H.sub (H.project q x))
      (projectSpan q (H.coefficientA v x) (H.coefficientB v x)))
      (subZero (H.project q x)))

projectCorrected : {V : H.Direction} (p q : H.Mark V) (x : H.Vec5) (n : Trit) →
  H.add (H.raw q x n) (H.correction p q n) ≡ H.actual p q x n
projectCorrected p q x n =
  trans (cong (H.add (H.raw q x n))
      (sym (projectScale q n (H.sub (H.w p) (H.w q)))))
    (trans (sym (projectAdd q (H.add x (H.scale n (H.w q)))
                           (H.scale n (H.sub (H.w p) (H.w q)))))
      (cong (H.project q) (shiftCancel n x (H.w p) (H.w q))))

projectionLaws : (V : H.Direction) → H.ProjectionLaws V
projectionLaws V = record { corrected = projectCorrected ; compose = projectCompose }

atlasSection : {V : H.Direction} (p : H.Mark V) → H.Vec5 → Trit → S.Context →
  Fabric.GlobalSection (H.fabric p)
atlasSection {V} = H.section (projectionLaws V)

-- This consumes the literal atlas section. Transported rotation naturality
-- and the complete original H05 dependent restriction attachment are
-- separate; no kernel run or physical interpretation is claimed.
