module DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus where

------------------------------------------------------------------------
-- Three-coefficient functional calculus for ad_y on su(2).
--
-- The cubic identity A^3 = k A reduces every polynomial in A to
-- a I + b A + c A^2.  Large composition identities use the computable
-- axiomatic-real polynomial socket rather than reflective alias matching.
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
  ( _+R_
  ; _*R_
  ; zeroR
  ; oneR
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2Lie
  ; su2LieExt
  ; lieAdd
  ; lieScale
  )
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using
  ( adOperator; dotP )
open import DASHI.Physics.YangMills.BalabanSU2AdjointCubicReduction using
  ( adCubicCoefficient
  ; fourP
  ; ad1P
  ; ad2P
  ; ad3P
  ; adSquare1P
  ; adSquare2P
  ; adSquare3P
  )

zeroP : ∀ {n} → Polynomial n
zeroP = con zeroCoefficient

oneP : ∀ {n} → Polynomial n
oneP = con oneCoefficient

record ReducedAdjointOperator : Set where
  constructor reducedAd
  field
    identityCoefficient : ℝ
    linearCoefficient : ℝ
    quadraticCoefficient : ℝ

open ReducedAdjointOperator public

reducedAdjointExt :
  ∀ {left right : ReducedAdjointOperator} →
  identityCoefficient left ≡ identityCoefficient right →
  linearCoefficient left ≡ linearCoefficient right →
  quadraticCoefficient left ≡ quadraticCoefficient right →
  left ≡ right
reducedAdjointExt
  {reducedAd a b c} {reducedAd .a .b .c}
  refl refl refl = refl

applyReducedAdjoint :
  SU2LieAlgebra →
  ReducedAdjointOperator →
  SU2LieAlgebra →
  SU2LieAlgebra
applyReducedAdjoint Y operator X =
  lieAdd
    (lieScale (identityCoefficient operator) X)
    (lieAdd
      (lieScale (linearCoefficient operator) (adOperator Y X))
      (lieScale (quadraticCoefficient operator)
        (adOperator Y (adOperator Y X))))

identityReducedAdjoint : ReducedAdjointOperator
identityReducedAdjoint = reducedAd oneR zeroR zeroR

composeReducedAdjoint :
  SU2LieAlgebra →
  ReducedAdjointOperator →
  ReducedAdjointOperator →
  ReducedAdjointOperator
composeReducedAdjoint Y
  (reducedAd a b c)
  (reducedAd d e f) =
  reducedAd
    (a *R d)
    (((a *R e) +R (b *R d))
      +R (adCubicCoefficient Y *R
        ((b *R f) +R (c *R e))))
    ((((a *R f) +R (b *R e))
      +R (c *R d))
      +R (adCubicCoefficient Y *R (c *R f)))

kP : ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
kP y₁ y₂ y₃ = :- (fourP :* (dotP y₁ y₂ y₃ y₁ y₂ y₃))

composeAP : ∀ {n} → Polynomial n → Polynomial n → Polynomial n
composeAP a d = a :* d

composeBP : ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
composeBP k a b c d e f =
  ((a :* e) :+ (b :* d)) :+ (k :* ((b :* f) :+ (c :* e)))

composeCP : ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
composeCP k a b c d e f =
  ((((a :* f) :+ (b :* e)) :+ (c :* d)) :+ (k :* (c :* f)))

apply1P : ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
apply1P y₁ y₂ y₃ a b c x₁ x₂ x₃ =
  (a :* x₁) :+
    ((b :* ad1P y₁ y₂ y₃ x₁ x₂ x₃) :+
      (c :* adSquare1P y₁ y₂ y₃ x₁ x₂ x₃))

apply2P : ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
apply2P y₁ y₂ y₃ a b c x₁ x₂ x₃ =
  (a :* x₂) :+
    ((b :* ad2P y₁ y₂ y₃ x₁ x₂ x₃) :+
      (c :* adSquare2P y₁ y₂ y₃ x₁ x₂ x₃))

apply3P : ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
apply3P y₁ y₂ y₃ a b c x₁ x₂ x₃ =
  (a :* x₃) :+
    ((b :* ad3P y₁ y₂ y₃ x₁ x₂ x₃) :+
      (c :* adSquare3P y₁ y₂ y₃ x₁ x₂ x₃))

applyIdentityReducedAdjoint :
  ∀ Y X →
  applyReducedAdjoint Y identityReducedAdjoint X ≡ X
applyIdentityReducedAdjoint
  (su2Lie y₁ y₂ y₃) (su2Lie x₁ x₂ x₃) =
  su2LieExt
    (solveComputed 6
      (λ y₁ y₂ y₃ x₁ x₂ x₃ →
        apply1P y₁ y₂ y₃ oneP zeroP zeroP x₁ x₂ x₃ := x₁)
      computed)
    (solveComputed 6
      (λ y₁ y₂ y₃ x₁ x₂ x₃ →
        apply2P y₁ y₂ y₃ oneP zeroP zeroP x₁ x₂ x₃ := x₂)
      computed)
    (solveComputed 6
      (λ y₁ y₂ y₃ x₁ x₂ x₃ →
        apply3P y₁ y₂ y₃ oneP zeroP zeroP x₁ x₂ x₃ := x₃)
      computed)

applyReducedComposition :
  ∀ Y left right X →
  applyReducedAdjoint Y left
    (applyReducedAdjoint Y right X)
  ≡
  applyReducedAdjoint Y
    (composeReducedAdjoint Y left right)
    X
applyReducedComposition
  (su2Lie y₁ y₂ y₃)
  (reducedAd a b c)
  (reducedAd d e f)
  (su2Lie x₁ x₂ x₃) =
  su2LieExt
    (solveComputed 12
      (λ y₁ y₂ y₃ a b c d e f x₁ x₂ x₃ →
        apply1P y₁ y₂ y₃ a b c
          (apply1P y₁ y₂ y₃ d e f x₁ x₂ x₃)
          (apply2P y₁ y₂ y₃ d e f x₁ x₂ x₃)
          (apply3P y₁ y₂ y₃ d e f x₁ x₂ x₃)
        :=
        apply1P y₁ y₂ y₃
          (composeAP a d)
          (composeBP (kP y₁ y₂ y₃) a b c d e f)
          (composeCP (kP y₁ y₂ y₃) a b c d e f)
          x₁ x₂ x₃)
      computed)
    (solveComputed 12
      (λ y₁ y₂ y₃ a b c d e f x₁ x₂ x₃ →
        apply2P y₁ y₂ y₃ a b c
          (apply1P y₁ y₂ y₃ d e f x₁ x₂ x₃)
          (apply2P y₁ y₂ y₃ d e f x₁ x₂ x₃)
          (apply3P y₁ y₂ y₃ d e f x₁ x₂ x₃)
        :=
        apply2P y₁ y₂ y₃
          (composeAP a d)
          (composeBP (kP y₁ y₂ y₃) a b c d e f)
          (composeCP (kP y₁ y₂ y₃) a b c d e f)
          x₁ x₂ x₃)
      computed)
    (solveComputed 12
      (λ y₁ y₂ y₃ a b c d e f x₁ x₂ x₃ →
        apply3P y₁ y₂ y₃ a b c
          (apply1P y₁ y₂ y₃ d e f x₁ x₂ x₃)
          (apply2P y₁ y₂ y₃ d e f x₁ x₂ x₃)
          (apply3P y₁ y₂ y₃ d e f x₁ x₂ x₃)
        :=
        apply3P y₁ y₂ y₃
          (composeAP a d)
          (composeBP (kP y₁ y₂ y₃) a b c d e f)
          (composeCP (kP y₁ y₂ y₃) a b c d e f)
          x₁ x₂ x₃)
      computed)

composeReducedIdentityLeft :
  ∀ Y operator →
  composeReducedAdjoint Y identityReducedAdjoint operator ≡ operator
composeReducedIdentityLeft Y (reducedAd a b c) =
  reducedAdjointExt
    (solveComputed 4
      (λ a b c k → composeAP oneP a := a)
      computed)
    (solveComputed 4
      (λ a b c k → composeBP k oneP zeroP zeroP a b c := b)
      computed)
    (solveComputed 4
      (λ a b c k → composeCP k oneP zeroP zeroP a b c := c)
      computed)

composeReducedIdentityRight :
  ∀ Y operator →
  composeReducedAdjoint Y operator identityReducedAdjoint ≡ operator
composeReducedIdentityRight Y (reducedAd a b c) =
  reducedAdjointExt
    (solveComputed 4
      (λ a b c k → composeAP a oneP := a)
      computed)
    (solveComputed 4
      (λ a b c k → composeBP k a b c oneP zeroP zeroP := b)
      computed)
    (solveComputed 4
      (λ a b c k → composeCP k a b c oneP zeroP zeroP := c)
      computed)

composeReducedCommutative :
  ∀ Y left right →
  composeReducedAdjoint Y left right
    ≡ composeReducedAdjoint Y right left
composeReducedCommutative Y
  (reducedAd a b c)
  (reducedAd d e f) =
  reducedAdjointExt
    (solveComputed 7
      (λ a b c d e f k → composeAP a d := composeAP d a)
      computed)
    (solveComputed 7
      (λ a b c d e f k →
        composeBP k a b c d e f := composeBP k d e f a b c)
      computed)
    (solveComputed 7
      (λ a b c d e f k →
        composeCP k a b c d e f := composeCP k d e f a b c)
      computed)

composeReducedAssociative :
  ∀ Y first second third →
  composeReducedAdjoint Y
    (composeReducedAdjoint Y first second)
    third
  ≡
  composeReducedAdjoint Y
    first
    (composeReducedAdjoint Y second third)
composeReducedAssociative Y
  (reducedAd a b c)
  (reducedAd d e f)
  (reducedAd g h i) =
  reducedAdjointExt
    (solveComputed 10
      (λ a b c d e f g h i k →
        composeAP (composeAP a d) g := composeAP a (composeAP d g))
      computed)
    (solveComputed 10
      (λ a b c d e f g h i k →
        composeBP k
          (composeAP a d)
          (composeBP k a b c d e f)
          (composeCP k a b c d e f)
          g h i
        :=
        composeBP k a b c
          (composeAP d g)
          (composeBP k d e f g h i)
          (composeCP k d e f g h i))
      computed)
    (solveComputed 10
      (λ a b c d e f g h i k →
        composeCP k
          (composeAP a d)
          (composeBP k a b c d e f)
          (composeCP k a b c d e f)
          g h i
        :=
        composeCP k a b c
          (composeAP d g)
          (composeBP k d e f g h i)
          (composeCP k d e f g h i))
      computed)
