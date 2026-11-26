module DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearExact where

-- SOURCE-WRITTEN, UNCOMPILED. Common positive lattice ax+by=n.
-- Classical divisor convolution identities; DASHI source-coordinate
-- shear/reindexing reduction. No modular-form or analytic premise.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_∸_; _<_)
import Data.Nat.Properties as N
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using () renaming
  (solve to nsolve; _:+_ to _⊞_; _:*_ to _⊠_; con to ncon; _:=_ to _≐_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

record Quad : Set where
  constructor quad
  field a b x y : Nat
open Quad public

grade : Quad → Nat
grade (quad a b x y) = a * x + b * y

Positive : Quad → Set
Positive (quad a b x y) = (zero < a) × (zero < b) × (zero < x) × (zero < y)

left right leftBack rightBack : Quad → Quad
left      (quad a b x y) = quad (a ∸ b) b x (x + y)
leftBack  (quad a b x y) = quad (a + b) b x (y ∸ x)
right     (quad a b x y) = quad a (b ∸ a) (x + y) y
rightBack (quad a b x y) = quad a (a + b) (x ∸ y) y

leftChartGrade : (a b x y : Nat) →
  (a + b) * x + b * y ≡ a * x + b * (x + y)
leftChartGrade a b x y =
  nsolve 4 (λ a b x y → (a ⊞ b) ⊠ x ⊞ b ⊠ y ≐
    a ⊠ x ⊞ b ⊠ (x ⊞ y)) refl a b x y

rightChartGrade : (a b x y : Nat) →
  a * x + (a + b) * y ≡ a * (x + y) + b * y
rightChartGrade a b x y =
  nsolve 4 (λ a b x y → a ⊠ x ⊞ (a ⊞ b) ⊠ y ≐
    a ⊠ (x ⊞ y) ⊞ b ⊠ y) refl a b x y

leftGrade : (q : Quad) → b q < a q → grade (left q) ≡ grade q
leftGrade (quad a b x y) h =
  trans (sym (leftChartGrade (a ∸ b) b x y))
    (cong (λ t → t * x + b * y) (N.m∸n+n≡m (N.<⇒≤ h)))

rightGrade : (q : Quad) → a q < b q → grade (right q) ≡ grade q
rightGrade (quad a b x y) h =
  trans (sym (rightChartGrade a (b ∸ a) x y))
    (cong (λ t → a * x + t * y)
      (trans (N.+-comm a (b ∸ a)) (N.m∸n+n≡m (N.<⇒≤ h))))

leftBackGrade : (q : Quad) → x q < y q → grade (leftBack q) ≡ grade q
leftBackGrade (quad a b x y) h =
  trans (leftChartGrade a b x (y ∸ x))
    (cong (λ t → a * x + b * t)
      (trans (N.+-comm x (y ∸ x)) (N.m∸n+n≡m (N.<⇒≤ h))))

rightBackGrade : (q : Quad) → y q < x q → grade (rightBack q) ≡ grade q
rightBackGrade (quad a b x y) h =
  trans (rightChartGrade a b (x ∸ y) y)
    (cong (λ t → a * t + b * y) (N.m∸n+n≡m (N.<⇒≤ h)))

leftInverse : (q : Quad) → b q < a q → leftBack (left q) ≡ q
leftInverse (quad a b x y) h
  rewrite N.m∸n+n≡m (N.<⇒≤ h) | N.m+n∸m≡n x y = refl

leftRightInverse : (q : Quad) → x q < y q → left (leftBack q) ≡ q
leftRightInverse (quad a b x y) h
  rewrite N.m+n∸n≡m a b | N.+-comm x (y ∸ x) |
    N.m∸n+n≡m (N.<⇒≤ h) = refl

rightInverse : (q : Quad) → a q < b q → rightBack (right q) ≡ q
rightInverse (quad a b x y) h
  rewrite N.+-comm a (b ∸ a) | N.m∸n+n≡m (N.<⇒≤ h) |
    N.m+n∸n≡m x y = refl

rightRightInverse : (q : Quad) → y q < x q → right (rightBack q) ≡ q
rightRightInverse (quad a b x y) h
  rewrite N.m+n∸m≡n a b | N.m∸n+n≡m (N.<⇒≤ h) = refl

leftPositive : (q : Quad) → Positive q → b q < a q → Positive (left q)
leftPositive (quad a b x y) (pa , pb , px , py) h =
  N.m<n⇒0<n∸m h , pb , px , N.m<n⇒0<n (N.m<m+n x py)

leftBackPositive : (q : Quad) → Positive q → x q < y q → Positive (leftBack q)
leftBackPositive (quad a b x y) (pa , pb , px , py) h =
  N.m<n⇒0<n (N.m<m+n a pb) , pb , px , N.m<n⇒0<n∸m h

rightPositive : (q : Quad) → Positive q → a q < b q → Positive (right q)
rightPositive (quad a b x y) (pa , pb , px , py) h =
  pa , N.m<n⇒0<n∸m h , N.m<n⇒0<n (N.m<m+n x py) , py

rightBackPositive : (q : Quad) → Positive q → y q < x q → Positive (rightBack q)
rightBackPositive (quad a b x y) (pa , pb , px , py) h =
  pa , N.m<n⇒0<n (N.m<m+n a pb) , N.m<n⇒0<n∸m h , py

leftTarget : (q : Quad) → Positive q → x (left q) < y (left q)
leftTarget (quad a b x y) (pa , pb , px , py) = N.m<m+n x py

leftSource : (q : Quad) → Positive q → b (leftBack q) < a (leftBack q)
leftSource (quad a b x y) (pa , pb , px , py) = N.m<n+m b pa

rightTarget : (q : Quad) → Positive q → y (right q) < x (right q)
rightTarget (quad a b x y) (pa , pb , px , py) = N.m<n+m y px

rightSource : (q : Quad) → Positive q → a (rightBack q) < b (rightBack q)
rightSource (quad a b x y) (pa , pb , px , py) = N.m<m+n a pb

-- Four literal signed polynomial observations. Their denominator-free
-- identities hold at every integer pair, not just enumerated examples.
import Data.Integer.Base as Z
import Data.Integer.Solver as IS
open IS.+-*-Solver using () renaming
  (solve to zsolve; _:+_ to _⊕_; _:*_ to _⊗_; con to zcon; _:=_ to _⊜_)
open Z using (ℤ; +_; -_)
infixl 6 _+z_
infixl 7 _*z_
_+z_ = Z._+_
_*z_ = Z._*_

-- The sign of a-b is kept in integer coordinates.

weight1 : ℤ → ℤ → ℤ
weight1 a b = (((a *z a) +z ((- (+ 1)) *z (a *z b))) +z (b *z b))
weight1ShearSymmetry : (a b : ℤ) → weight1 (a +z b) b ≡ weight1 a (a +z b)
weight1ShearSymmetry a b = zsolve 2 (λ a b →
  ((((a ⊕ b) ⊗ (a ⊕ b)) ⊕ (zcon (- (+ 1)) ⊗ ((a ⊕ b) ⊗ b))) ⊕ (b ⊗ b)) ⊜
  (((a ⊗ a) ⊕ (zcon (- (+ 1)) ⊗ (a ⊗ (a ⊕ b)))) ⊕ ((a ⊕ b) ⊗ (a ⊕ b)))) refl a b
difference1 : (a b : ℤ) → weight1 (a +z b) b ≡ weight1 a b +z ((+ 2) *z (a *z b))
difference1 a b = zsolve 2 (λ a b →
  ((((a ⊕ b) ⊗ (a ⊕ b)) ⊕ (zcon (- (+ 1)) ⊗ ((a ⊕ b) ⊗ b))) ⊕ (b ⊗ b)) ⊜
  ((((a ⊗ a) ⊕ (zcon (- (+ 1)) ⊗ (a ⊗ b))) ⊕ (b ⊗ b)) ⊕ (zcon (+ 2) ⊗ (a ⊗ b)))) refl a b

weight2 : ℤ → ℤ → ℤ
weight2 a b = ((((a *z a) +z ((- (+ 1)) *z (a *z b))) +z (b *z b)) *z (((a *z a) +z ((- (+ 1)) *z (a *z b))) +z (b *z b)))
weight2ShearSymmetry : (a b : ℤ) → weight2 (a +z b) b ≡ weight2 a (a +z b)
weight2ShearSymmetry a b = zsolve 2 (λ a b →
  (((((a ⊕ b) ⊗ (a ⊕ b)) ⊕ (zcon (- (+ 1)) ⊗ ((a ⊕ b) ⊗ b))) ⊕ (b ⊗ b)) ⊗ ((((a ⊕ b) ⊗ (a ⊕ b)) ⊕ (zcon (- (+ 1)) ⊗ ((a ⊕ b) ⊗ b))) ⊕ (b ⊗ b))) ⊜
  ((((a ⊗ a) ⊕ (zcon (- (+ 1)) ⊗ (a ⊗ (a ⊕ b)))) ⊕ ((a ⊕ b) ⊗ (a ⊕ b))) ⊗ (((a ⊗ a) ⊕ (zcon (- (+ 1)) ⊗ (a ⊗ (a ⊕ b)))) ⊕ ((a ⊕ b) ⊗ (a ⊕ b))))) refl a b
difference2 : (a b : ℤ) → weight2 (a +z b) b ≡ weight2 a b +z (((+ 4) *z ((a *z (a *z a)) *z b)) +z ((+ 4) *z (a *z (b *z (b *z b)))))
difference2 a b = zsolve 2 (λ a b →
  (((((a ⊕ b) ⊗ (a ⊕ b)) ⊕ (zcon (- (+ 1)) ⊗ ((a ⊕ b) ⊗ b))) ⊕ (b ⊗ b)) ⊗ ((((a ⊕ b) ⊗ (a ⊕ b)) ⊕ (zcon (- (+ 1)) ⊗ ((a ⊕ b) ⊗ b))) ⊕ (b ⊗ b))) ⊜
  (((((a ⊗ a) ⊕ (zcon (- (+ 1)) ⊗ (a ⊗ b))) ⊕ (b ⊗ b)) ⊗ (((a ⊗ a) ⊕ (zcon (- (+ 1)) ⊗ (a ⊗ b))) ⊕ (b ⊗ b))) ⊕ ((zcon (+ 4) ⊗ ((a ⊗ (a ⊗ a)) ⊗ b)) ⊕ (zcon (+ 4) ⊗ (a ⊗ (b ⊗ (b ⊗ b))))))) refl a b

weight3 : ℤ → ℤ → ℤ
weight3 a b = ((((a *z a) +z ((- (+ 1)) *z (a *z b))) +z (b *z b)) *z ((((a *z a) +z ((- (+ 1)) *z (a *z b))) +z (b *z b)) *z (((a *z a) +z ((- (+ 1)) *z (a *z b))) +z (b *z b))))
weight3ShearSymmetry : (a b : ℤ) → weight3 (a +z b) b ≡ weight3 a (a +z b)
weight3ShearSymmetry a b = zsolve 2 (λ a b →
  (((((a ⊕ b) ⊗ (a ⊕ b)) ⊕ (zcon (- (+ 1)) ⊗ ((a ⊕ b) ⊗ b))) ⊕ (b ⊗ b)) ⊗ (((((a ⊕ b) ⊗ (a ⊕ b)) ⊕ (zcon (- (+ 1)) ⊗ ((a ⊕ b) ⊗ b))) ⊕ (b ⊗ b)) ⊗ ((((a ⊕ b) ⊗ (a ⊕ b)) ⊕ (zcon (- (+ 1)) ⊗ ((a ⊕ b) ⊗ b))) ⊕ (b ⊗ b)))) ⊜
  ((((a ⊗ a) ⊕ (zcon (- (+ 1)) ⊗ (a ⊗ (a ⊕ b)))) ⊕ ((a ⊕ b) ⊗ (a ⊕ b))) ⊗ ((((a ⊗ a) ⊕ (zcon (- (+ 1)) ⊗ (a ⊗ (a ⊕ b)))) ⊕ ((a ⊕ b) ⊗ (a ⊕ b))) ⊗ (((a ⊗ a) ⊕ (zcon (- (+ 1)) ⊗ (a ⊗ (a ⊕ b)))) ⊕ ((a ⊕ b) ⊗ (a ⊕ b)))))) refl a b
difference3 : (a b : ℤ) → weight3 (a +z b) b ≡ weight3 a b +z ((((+ 6) *z ((a *z (a *z (a *z (a *z a)))) *z b)) +z ((+ 14) *z ((a *z (a *z a)) *z (b *z (b *z b))))) +z ((+ 6) *z (a *z (b *z (b *z (b *z (b *z b)))))))
difference3 a b = zsolve 2 (λ a b →
  (((((a ⊕ b) ⊗ (a ⊕ b)) ⊕ (zcon (- (+ 1)) ⊗ ((a ⊕ b) ⊗ b))) ⊕ (b ⊗ b)) ⊗ (((((a ⊕ b) ⊗ (a ⊕ b)) ⊕ (zcon (- (+ 1)) ⊗ ((a ⊕ b) ⊗ b))) ⊕ (b ⊗ b)) ⊗ ((((a ⊕ b) ⊗ (a ⊕ b)) ⊕ (zcon (- (+ 1)) ⊗ ((a ⊕ b) ⊗ b))) ⊕ (b ⊗ b)))) ⊜
  (((((a ⊗ a) ⊕ (zcon (- (+ 1)) ⊗ (a ⊗ b))) ⊕ (b ⊗ b)) ⊗ ((((a ⊗ a) ⊕ (zcon (- (+ 1)) ⊗ (a ⊗ b))) ⊕ (b ⊗ b)) ⊗ (((a ⊗ a) ⊕ (zcon (- (+ 1)) ⊗ (a ⊗ b))) ⊕ (b ⊗ b)))) ⊕ (((zcon (+ 6) ⊗ ((a ⊗ (a ⊗ (a ⊗ (a ⊗ a)))) ⊗ b)) ⊕ (zcon (+ 14) ⊗ ((a ⊗ (a ⊗ a)) ⊗ (b ⊗ (b ⊗ b))))) ⊕ (zcon (+ 6) ⊗ (a ⊗ (b ⊗ (b ⊗ (b ⊗ (b ⊗ b))))))))) refl a b

weight4 : ℤ → ℤ → ℤ
weight4 a b = (((a *z a) *z (b *z b)) *z ((a +z ((- (+ 1)) *z b)) *z (a +z ((- (+ 1)) *z b))))
weight4ShearSymmetry : (a b : ℤ) → weight4 (a +z b) b ≡ weight4 a (a +z b)
weight4ShearSymmetry a b = zsolve 2 (λ a b →
  ((((a ⊕ b) ⊗ (a ⊕ b)) ⊗ (b ⊗ b)) ⊗ (((a ⊕ b) ⊕ (zcon (- (+ 1)) ⊗ b)) ⊗ ((a ⊕ b) ⊕ (zcon (- (+ 1)) ⊗ b)))) ⊜
  (((a ⊗ a) ⊗ ((a ⊕ b) ⊗ (a ⊕ b))) ⊗ ((a ⊕ (zcon (- (+ 1)) ⊗ (a ⊕ b))) ⊗ (a ⊕ (zcon (- (+ 1)) ⊗ (a ⊕ b)))))) refl a b
difference4 : (a b : ℤ) → weight4 (a +z b) b ≡ weight4 a b +z ((+ 4) *z ((a *z (a *z a)) *z (b *z (b *z b))))
difference4 a b = zsolve 2 (λ a b →
  ((((a ⊕ b) ⊗ (a ⊕ b)) ⊗ (b ⊗ b)) ⊗ (((a ⊕ b) ⊕ (zcon (- (+ 1)) ⊗ b)) ⊗ ((a ⊕ b) ⊕ (zcon (- (+ 1)) ⊗ b)))) ⊜
  ((((a ⊗ a) ⊗ (b ⊗ b)) ⊗ ((a ⊕ (zcon (- (+ 1)) ⊗ b)) ⊗ (a ⊕ (zcon (- (+ 1)) ⊗ b)))) ⊕ (zcon (+ 4) ⊗ ((a ⊗ (a ⊗ a)) ⊗ (b ⊗ (b ⊗ b)))))) refl a b

-- The next finite attachment is the unique enumeration permutation
-- on each actual grade, followed by signed boundary folds. Do not
-- infer this permutation merely from the polynomial identity.
