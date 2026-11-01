module DASHI.Physics.YangMills.BalabanSU2AdjointMatrixDeterminant where

------------------------------------------------------------------------
-- Concrete 3 x 3 matrices for the su(2) adjoint calculus.
--
-- All large coordinate and determinant identities are discharged through the
-- computable axiomatic-real polynomial socket.  No stdlib reflective alias
-- matching is used here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( module RealPolynomialSolver; zeroCoefficient; oneCoefficient )
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  ( solveComputed; computed )
open RealPolynomialSolver using
  ( Polynomial; con; _:=_; _:+_; _:*_; :-_ )
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( _+R_; _*R_; -R_; zeroR; oneR )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra; su2Lie; su2LieExt )
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using
  ( adOperator; bracket1P; bracket2P; bracket3P; dotP; twoP )
open import DASHI.Physics.YangMills.BalabanSU2AdjointCubicReduction using
  ( adCubicCoefficient; fourP )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus using
  ( ReducedAdjointOperator; reducedAd; identityCoefficient; linearCoefficient;
    quadraticCoefficient; applyReducedAdjoint; apply1P; apply2P; apply3P; kP )

record Matrix3 : Set where
  constructor matrix3
  field
    m00 m01 m02 : ℝ
    m10 m11 m12 : ℝ
    m20 m21 m22 : ℝ
open Matrix3 public

matrix3Ext :
  ∀ {A B : Matrix3} →
  m00 A ≡ m00 B → m01 A ≡ m01 B → m02 A ≡ m02 B →
  m10 A ≡ m10 B → m11 A ≡ m11 B → m12 A ≡ m12 B →
  m20 A ≡ m20 B → m21 A ≡ m21 B → m22 A ≡ m22 B → A ≡ B
matrix3Ext
  {matrix3 a00 a01 a02 a10 a11 a12 a20 a21 a22}
  {matrix3 .a00 .a01 .a02 .a10 .a11 .a12 .a20 .a21 .a22}
  refl refl refl refl refl refl refl refl refl = refl

identityMatrix3 : Matrix3
identityMatrix3 = matrix3 oneR zeroR zeroR zeroR oneR zeroR zeroR zeroR oneR

addMatrix3 : Matrix3 → Matrix3 → Matrix3
addMatrix3
  (matrix3 a00 a01 a02 a10 a11 a12 a20 a21 a22)
  (matrix3 b00 b01 b02 b10 b11 b12 b20 b21 b22) =
  matrix3
    (a00 +R b00) (a01 +R b01) (a02 +R b02)
    (a10 +R b10) (a11 +R b11) (a12 +R b12)
    (a20 +R b20) (a21 +R b21) (a22 +R b22)

scaleMatrix3 : ℝ → Matrix3 → Matrix3
scaleMatrix3 scalar (matrix3 a00 a01 a02 a10 a11 a12 a20 a21 a22) =
  matrix3
    (scalar *R a00) (scalar *R a01) (scalar *R a02)
    (scalar *R a10) (scalar *R a11) (scalar *R a12)
    (scalar *R a20) (scalar *R a21) (scalar *R a22)

multiplyMatrix3 : Matrix3 → Matrix3 → Matrix3
multiplyMatrix3
  (matrix3 a00 a01 a02 a10 a11 a12 a20 a21 a22)
  (matrix3 b00 b01 b02 b10 b11 b12 b20 b21 b22) =
  matrix3
    (((a00 *R b00) +R (a01 *R b10)) +R (a02 *R b20))
    (((a00 *R b01) +R (a01 *R b11)) +R (a02 *R b21))
    (((a00 *R b02) +R (a01 *R b12)) +R (a02 *R b22))
    (((a10 *R b00) +R (a11 *R b10)) +R (a12 *R b20))
    (((a10 *R b01) +R (a11 *R b11)) +R (a12 *R b21))
    (((a10 *R b02) +R (a11 *R b12)) +R (a12 *R b22))
    (((a20 *R b00) +R (a21 *R b10)) +R (a22 *R b20))
    (((a20 *R b01) +R (a21 *R b11)) +R (a22 *R b21))
    (((a20 *R b02) +R (a21 *R b12)) +R (a22 *R b22))

applyMatrix3 : Matrix3 → SU2LieAlgebra → SU2LieAlgebra
applyMatrix3
  (matrix3 a00 a01 a02 a10 a11 a12 a20 a21 a22)
  (su2Lie x y z) =
  su2Lie
    (((a00 *R x) +R (a01 *R y)) +R (a02 *R z))
    (((a10 *R x) +R (a11 *R y)) +R (a12 *R z))
    (((a20 *R x) +R (a21 *R y)) +R (a22 *R z))

determinantMatrix3 : Matrix3 → ℝ
determinantMatrix3 (matrix3 a b c d e f g h i) =
  (a *R ((e *R i) +R (-R (f *R h))))
  +R (-R (b *R ((d *R i) +R (-R (f *R g)))))
  +R (c *R ((d *R h) +R (-R (e *R g))))

twoR : ℝ
twoR = oneR +R oneR

adMatrix : SU2LieAlgebra → Matrix3
adMatrix (su2Lie x y z) =
  matrix3
    zeroR (-R (twoR *R z)) (twoR *R y)
    (twoR *R z) zeroR (-R (twoR *R x))
    (-R (twoR *R y)) (twoR *R x) zeroR

zeroP : ∀ {n} → Polynomial n
zeroP = con zeroCoefficient
oneP : ∀ {n} → Polynomial n
oneP = con oneCoefficient

record Matrix3P (n : _) : Set where
  constructor matrix3P
  field
    p00 p01 p02 : Polynomial n
    p10 p11 p12 : Polynomial n
    p20 p21 p22 : Polynomial n
open Matrix3P public

identityMatrix3P : ∀ {n} → Matrix3P n
identityMatrix3P = matrix3P oneP zeroP zeroP zeroP oneP zeroP zeroP zeroP oneP

addMatrix3P : ∀ {n} → Matrix3P n → Matrix3P n → Matrix3P n
addMatrix3P
  (matrix3P a00 a01 a02 a10 a11 a12 a20 a21 a22)
  (matrix3P b00 b01 b02 b10 b11 b12 b20 b21 b22) =
  matrix3P
    (a00 :+ b00) (a01 :+ b01) (a02 :+ b02)
    (a10 :+ b10) (a11 :+ b11) (a12 :+ b12)
    (a20 :+ b20) (a21 :+ b21) (a22 :+ b22)

scaleMatrix3P : ∀ {n} → Polynomial n → Matrix3P n → Matrix3P n
scaleMatrix3P scalar (matrix3P a00 a01 a02 a10 a11 a12 a20 a21 a22) =
  matrix3P
    (scalar :* a00) (scalar :* a01) (scalar :* a02)
    (scalar :* a10) (scalar :* a11) (scalar :* a12)
    (scalar :* a20) (scalar :* a21) (scalar :* a22)

multiplyMatrix3P : ∀ {n} → Matrix3P n → Matrix3P n → Matrix3P n
multiplyMatrix3P
  (matrix3P a00 a01 a02 a10 a11 a12 a20 a21 a22)
  (matrix3P b00 b01 b02 b10 b11 b12 b20 b21 b22) =
  matrix3P
    ((a00 :* b00) :+ (a01 :* b10) :+ (a02 :* b20))
    ((a00 :* b01) :+ (a01 :* b11) :+ (a02 :* b21))
    ((a00 :* b02) :+ (a01 :* b12) :+ (a02 :* b22))
    ((a10 :* b00) :+ (a11 :* b10) :+ (a12 :* b20))
    ((a10 :* b01) :+ (a11 :* b11) :+ (a12 :* b21))
    ((a10 :* b02) :+ (a11 :* b12) :+ (a12 :* b22))
    ((a20 :* b00) :+ (a21 :* b10) :+ (a22 :* b20))
    ((a20 :* b01) :+ (a21 :* b11) :+ (a22 :* b21))
    ((a20 :* b02) :+ (a21 :* b12) :+ (a22 :* b22))

apply1MatrixP : ∀ {n} → Matrix3P n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
apply1MatrixP M x y z = (p00 M :* x) :+ (p01 M :* y) :+ (p02 M :* z)
apply2MatrixP : ∀ {n} → Matrix3P n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
apply2MatrixP M x y z = (p10 M :* x) :+ (p11 M :* y) :+ (p12 M :* z)
apply3MatrixP : ∀ {n} → Matrix3P n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
apply3MatrixP M x y z = (p20 M :* x) :+ (p21 M :* y) :+ (p22 M :* z)

determinantMatrix3P : ∀ {n} → Matrix3P n → Polynomial n
determinantMatrix3P M =
  (p00 M :* ((p11 M :* p22 M) :+ (:- (p12 M :* p21 M)))) :+
  (:- (p01 M :* ((p10 M :* p22 M) :+ (:- (p12 M :* p20 M))))) :+
  (p02 M :* ((p10 M :* p21 M) :+ (:- (p11 M :* p20 M))))

adMatrixP : ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Matrix3P n
adMatrixP x y z =
  matrix3P
    zeroP (:- (twoP :* z)) (twoP :* y)
    (twoP :* z) zeroP (:- (twoP :* x))
    (:- (twoP :* y)) (twoP :* x) zeroP

reducedAdjointMatrixP : ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Matrix3P n
reducedAdjointMatrixP x y z a b c =
  addMatrix3P
    (scaleMatrix3P a identityMatrix3P)
    (addMatrix3P
      (scaleMatrix3P b (adMatrixP x y z))
      (scaleMatrix3P c (multiplyMatrix3P (adMatrixP x y z) (adMatrixP x y z))))

applyAdMatrix : ∀ Y X → applyMatrix3 (adMatrix Y) X ≡ adOperator Y X
applyAdMatrix (su2Lie y₁ y₂ y₃) (su2Lie x₁ x₂ x₃) =
  su2LieExt
    (solveComputed 6
      (λ y₁ y₂ y₃ x₁ x₂ x₃ →
        apply1MatrixP (adMatrixP y₁ y₂ y₃) x₁ x₂ x₃ := bracket1P y₂ y₃ x₂ x₃)
      computed y₁ y₂ y₃ x₁ x₂ x₃)
    (solveComputed 6
      (λ y₁ y₂ y₃ x₁ x₂ x₃ →
        apply2MatrixP (adMatrixP y₁ y₂ y₃) x₁ x₂ x₃ := bracket2P y₃ y₁ x₃ x₁)
      computed y₁ y₂ y₃ x₁ x₂ x₃)
    (solveComputed 6
      (λ y₁ y₂ y₃ x₁ x₂ x₃ →
        apply3MatrixP (adMatrixP y₁ y₂ y₃) x₁ x₂ x₃ := bracket3P y₁ y₂ x₁ x₂)
      computed y₁ y₂ y₃ x₁ x₂ x₃)

reducedAdjointMatrix : SU2LieAlgebra → ReducedAdjointOperator → Matrix3
reducedAdjointMatrix Y operator =
  addMatrix3
    (scaleMatrix3 (identityCoefficient operator) identityMatrix3)
    (addMatrix3
      (scaleMatrix3 (linearCoefficient operator) (adMatrix Y))
      (scaleMatrix3 (quadraticCoefficient operator)
        (multiplyMatrix3 (adMatrix Y) (adMatrix Y))))

applyReducedAdjointMatrix : ∀ Y operator X →
  applyMatrix3 (reducedAdjointMatrix Y operator) X ≡ applyReducedAdjoint Y operator X
applyReducedAdjointMatrix
  (su2Lie y₁ y₂ y₃) (reducedAd a b c) (su2Lie x₁ x₂ x₃) =
  su2LieExt
    (solveComputed 9
      (λ y₁ y₂ y₃ a b c x₁ x₂ x₃ →
        apply1MatrixP (reducedAdjointMatrixP y₁ y₂ y₃ a b c) x₁ x₂ x₃ :=
        apply1P y₁ y₂ y₃ a b c x₁ x₂ x₃)
      computed y₁ y₂ y₃ a b c x₁ x₂ x₃)
    (solveComputed 9
      (λ y₁ y₂ y₃ a b c x₁ x₂ x₃ →
        apply2MatrixP (reducedAdjointMatrixP y₁ y₂ y₃ a b c) x₁ x₂ x₃ :=
        apply2P y₁ y₂ y₃ a b c x₁ x₂ x₃)
      computed y₁ y₂ y₃ a b c x₁ x₂ x₃)
    (solveComputed 9
      (λ y₁ y₂ y₃ a b c x₁ x₂ x₃ →
        apply3MatrixP (reducedAdjointMatrixP y₁ y₂ y₃ a b c) x₁ x₂ x₃ :=
        apply3P y₁ y₂ y₃ a b c x₁ x₂ x₃)
      computed y₁ y₂ y₃ a b c x₁ x₂ x₃)

reducedAdjointDeterminant : ∀ Y a b c →
  determinantMatrix3 (reducedAdjointMatrix Y (reducedAd a b c)) ≡
  a *R (((a +R (c *R adCubicCoefficient Y)) *R
          (a +R (c *R adCubicCoefficient Y)))
        +R (-R (adCubicCoefficient Y *R (b *R b))))
reducedAdjointDeterminant (su2Lie y₁ y₂ y₃) a b c =
  solveComputed 6
    (λ y₁ y₂ y₃ a b c →
      determinantMatrix3P (reducedAdjointMatrixP y₁ y₂ y₃ a b c) :=
      a :* (((a :+ (c :* kP y₁ y₂ y₃)) :*
             (a :+ (c :* kP y₁ y₂ y₃))) :+
            (:- (kP y₁ y₂ y₃ :* (b :* b)))))
    computed y₁ y₂ y₃ a b c
