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
_+z_ _*z_ : ℤ → ℤ → ℤ
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

-- Denominator-cleared boundary sums at x=y. The antidifference is
-- proved for arbitrary INTEGER d,t; the finite prefix theorem follows
-- by structural recursion. No Bernoulli-number library is assumed.
import Data.Integer.Properties as ZP

nextInteger : (n : Nat) → (+ n) +z (+ 1) ≡ + (suc n)
nextInteger n = trans (sym (ZP.pos-+ n 1)) (cong +_ (N.+-comm n 1))

scaledBoundaryPrefix : (ℤ → ℤ → ℤ) → ℤ → ℤ → Nat → ℤ
scaledBoundaryPrefix f m d zero = + 0
scaledBoundaryPrefix f m d (suc n) =
  scaledBoundaryPrefix f m d n +z (m *z f d (d +z ((- (+ 1)) *z (+ (suc n)))))

anti1 : ℤ → ℤ → ℤ
anti1 d t = (((((((+ 6) *z ((d *z d) *z t)) +z ((- (+ 3)) *z (d *z (t *z t)))) +z ((- (+ 3)) *z (d *z t))) +z ((+ 2) *z ((+ 1) *z (t *z (t *z t))))) +z ((+ 3) *z ((+ 1) *z (t *z t)))) +z ((+ 1) *z ((+ 1) *z t)))
boundary1 : ℤ → ℤ
boundary1 d = ((((+ 5) *z ((d *z (d *z d)) *z (+ 1))) +z ((- (+ 6)) *z ((d *z d) *z (+ 1)))) +z ((+ 1) *z (d *z (+ 1))))
anti1Zero : (d : ℤ) → anti1 d (+ 0) ≡ + 0
anti1Zero d = zsolve 1 (λ d → ((((((zcon (+ 6) ⊗ ((d ⊗ d) ⊗ zcon (+ 0))) ⊕ (zcon (- (+ 3)) ⊗ (d ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))) ⊕ (zcon (- (+ 3)) ⊗ (d ⊗ zcon (+ 0)))) ⊕ (zcon (+ 2) ⊗ (zcon (+ 1) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0)))))) ⊕ (zcon (+ 3) ⊗ (zcon (+ 1) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))) ⊕ (zcon (+ 1) ⊗ (zcon (+ 1) ⊗ zcon (+ 0)))) ⊜ zcon (+ 0)) refl d
anti1Step : (d t : ℤ) → anti1 d (t +z (+ 1)) ≡
  anti1 d t +z ((+ 6) *z weight1 d (d +z ((- (+ 1)) *z (t +z (+ 1)))))
anti1Step d t = zsolve 2 (λ d t →
  ((((((zcon (+ 6) ⊗ ((d ⊗ d) ⊗ (t ⊕ zcon (+ 1)))) ⊕ (zcon (- (+ 3)) ⊗ (d ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))) ⊕ (zcon (- (+ 3)) ⊗ (d ⊗ (t ⊕ zcon (+ 1))))) ⊕ (zcon (+ 2) ⊗ (zcon (+ 1) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))) ⊕ (zcon (+ 3) ⊗ (zcon (+ 1) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))) ⊕ (zcon (+ 1) ⊗ (zcon (+ 1) ⊗ (t ⊕ zcon (+ 1))))) ⊜
  (((((((zcon (+ 6) ⊗ ((d ⊗ d) ⊗ t)) ⊕ (zcon (- (+ 3)) ⊗ (d ⊗ (t ⊗ t)))) ⊕ (zcon (- (+ 3)) ⊗ (d ⊗ t))) ⊕ (zcon (+ 2) ⊗ (zcon (+ 1) ⊗ (t ⊗ (t ⊗ t))))) ⊕ (zcon (+ 3) ⊗ (zcon (+ 1) ⊗ (t ⊗ t)))) ⊕ (zcon (+ 1) ⊗ (zcon (+ 1) ⊗ t))) ⊕ (zcon (+ 6) ⊗ (((d ⊗ d) ⊕ (zcon (- (+ 1)) ⊗ (d ⊗ (d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))) ⊕ ((d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1)))) ⊗ (d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))))) refl d t
anti1AtEnd : (d : ℤ) → anti1 d (d +z (- (+ 1))) ≡ boundary1 d
anti1AtEnd d = zsolve 1 (λ d →
  ((((((zcon (+ 6) ⊗ ((d ⊗ d) ⊗ (d ⊕ zcon (- (+ 1))))) ⊕ (zcon (- (+ 3)) ⊗ (d ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))) ⊕ (zcon (- (+ 3)) ⊗ (d ⊗ (d ⊕ zcon (- (+ 1)))))) ⊕ (zcon (+ 2) ⊗ (zcon (+ 1) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1)))))))) ⊕ (zcon (+ 3) ⊗ (zcon (+ 1) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))) ⊕ (zcon (+ 1) ⊗ (zcon (+ 1) ⊗ (d ⊕ zcon (- (+ 1)))))) ⊜ (((zcon (+ 5) ⊗ ((d ⊗ (d ⊗ d)) ⊗ zcon (+ 1))) ⊕ (zcon (- (+ 6)) ⊗ ((d ⊗ d) ⊗ zcon (+ 1)))) ⊕ (zcon (+ 1) ⊗ (d ⊗ zcon (+ 1))))) refl d
prefix1 : (d : ℤ) (n : Nat) → scaledBoundaryPrefix weight1 (+ 6) d n ≡ anti1 d (+ n)
prefix1 d zero = sym (anti1Zero d)
prefix1 d (suc n) = trans
  (cong (λ v → v +z ((+ 6) *z weight1 d (d +z ((- (+ 1)) *z (+ (suc n)))))) (prefix1 d n))
  (trans (cong (λ u → anti1 d (+ n) +z ((+ 6) *z weight1 d (d +z ((- (+ 1)) *z u)))) (sym (nextInteger n)))
    (trans (sym (anti1Step d (+ n))) (cong (anti1 d) (nextInteger n))))

anti2 : ℤ → ℤ → ℤ
anti2 d t = ((((((((((((((+ 30) *z ((d *z (d *z (d *z d))) *z t)) +z ((- (+ 30)) *z ((d *z (d *z d)) *z (t *z t)))) +z ((- (+ 30)) *z ((d *z (d *z d)) *z t))) +z ((+ 30) *z ((d *z d) *z (t *z (t *z t))))) +z ((+ 45) *z ((d *z d) *z (t *z t)))) +z ((+ 15) *z ((d *z d) *z t))) +z ((- (+ 15)) *z (d *z (t *z (t *z (t *z t)))))) +z ((- (+ 30)) *z (d *z (t *z (t *z t))))) +z ((- (+ 15)) *z (d *z (t *z t)))) +z ((+ 6) *z ((+ 1) *z (t *z (t *z (t *z (t *z t))))))) +z ((+ 15) *z ((+ 1) *z (t *z (t *z (t *z t)))))) +z ((+ 10) *z ((+ 1) *z (t *z (t *z t))))) +z ((- (+ 1)) *z ((+ 1) *z t)))
boundary2 : ℤ → ℤ
boundary2 d = (((((+ 21) *z ((d *z (d *z (d *z (d *z d)))) *z (+ 1))) +z ((- (+ 30)) *z ((d *z (d *z (d *z d))) *z (+ 1)))) +z ((+ 10) *z ((d *z (d *z d)) *z (+ 1)))) +z ((- (+ 1)) *z (d *z (+ 1))))
anti2Zero : (d : ℤ) → anti2 d (+ 0) ≡ + 0
anti2Zero d = zsolve 1 (λ d → (((((((((((((zcon (+ 30) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ zcon (+ 0))) ⊕ (zcon (- (+ 30)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))) ⊕ (zcon (- (+ 30)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ zcon (+ 0)))) ⊕ (zcon (+ 30) ⊗ ((d ⊗ d) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0)))))) ⊕ (zcon (+ 45) ⊗ ((d ⊗ d) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))) ⊕ (zcon (+ 15) ⊗ ((d ⊗ d) ⊗ zcon (+ 0)))) ⊕ (zcon (- (+ 15)) ⊗ (d ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))))) ⊕ (zcon (- (+ 30)) ⊗ (d ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0)))))) ⊕ (zcon (- (+ 15)) ⊗ (d ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))) ⊕ (zcon (+ 6) ⊗ (zcon (+ 1) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0)))))))) ⊕ (zcon (+ 15) ⊗ (zcon (+ 1) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))))) ⊕ (zcon (+ 10) ⊗ (zcon (+ 1) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0)))))) ⊕ (zcon (- (+ 1)) ⊗ (zcon (+ 1) ⊗ zcon (+ 0)))) ⊜ zcon (+ 0)) refl d
anti2Step : (d t : ℤ) → anti2 d (t +z (+ 1)) ≡
  anti2 d t +z ((+ 30) *z weight2 d (d +z ((- (+ 1)) *z (t +z (+ 1)))))
anti2Step d t = zsolve 2 (λ d t →
  (((((((((((((zcon (+ 30) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ (t ⊕ zcon (+ 1)))) ⊕ (zcon (- (+ 30)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))) ⊕ (zcon (- (+ 30)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ (t ⊕ zcon (+ 1))))) ⊕ (zcon (+ 30) ⊗ ((d ⊗ d) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))) ⊕ (zcon (+ 45) ⊗ ((d ⊗ d) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))) ⊕ (zcon (+ 15) ⊗ ((d ⊗ d) ⊗ (t ⊕ zcon (+ 1))))) ⊕ (zcon (- (+ 15)) ⊗ (d ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))))) ⊕ (zcon (- (+ 30)) ⊗ (d ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))) ⊕ (zcon (- (+ 15)) ⊗ (d ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))) ⊕ (zcon (+ 6) ⊗ (zcon (+ 1) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))))) ⊕ (zcon (+ 15) ⊗ (zcon (+ 1) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))))) ⊕ (zcon (+ 10) ⊗ (zcon (+ 1) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))) ⊕ (zcon (- (+ 1)) ⊗ (zcon (+ 1) ⊗ (t ⊕ zcon (+ 1))))) ⊜
  ((((((((((((((zcon (+ 30) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ t)) ⊕ (zcon (- (+ 30)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ (t ⊗ t)))) ⊕ (zcon (- (+ 30)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ t))) ⊕ (zcon (+ 30) ⊗ ((d ⊗ d) ⊗ (t ⊗ (t ⊗ t))))) ⊕ (zcon (+ 45) ⊗ ((d ⊗ d) ⊗ (t ⊗ t)))) ⊕ (zcon (+ 15) ⊗ ((d ⊗ d) ⊗ t))) ⊕ (zcon (- (+ 15)) ⊗ (d ⊗ (t ⊗ (t ⊗ (t ⊗ t)))))) ⊕ (zcon (- (+ 30)) ⊗ (d ⊗ (t ⊗ (t ⊗ t))))) ⊕ (zcon (- (+ 15)) ⊗ (d ⊗ (t ⊗ t)))) ⊕ (zcon (+ 6) ⊗ (zcon (+ 1) ⊗ (t ⊗ (t ⊗ (t ⊗ (t ⊗ t))))))) ⊕ (zcon (+ 15) ⊗ (zcon (+ 1) ⊗ (t ⊗ (t ⊗ (t ⊗ t)))))) ⊕ (zcon (+ 10) ⊗ (zcon (+ 1) ⊗ (t ⊗ (t ⊗ t))))) ⊕ (zcon (- (+ 1)) ⊗ (zcon (+ 1) ⊗ t))) ⊕ (zcon (+ 30) ⊗ ((((d ⊗ d) ⊕ (zcon (- (+ 1)) ⊗ (d ⊗ (d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))) ⊕ ((d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1)))) ⊗ (d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))) ⊗ (((d ⊗ d) ⊕ (zcon (- (+ 1)) ⊗ (d ⊗ (d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))) ⊕ ((d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1)))) ⊗ (d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))))))) refl d t
anti2AtEnd : (d : ℤ) → anti2 d (d +z (- (+ 1))) ≡ boundary2 d
anti2AtEnd d = zsolve 1 (λ d →
  (((((((((((((zcon (+ 30) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ (d ⊕ zcon (- (+ 1))))) ⊕ (zcon (- (+ 30)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))) ⊕ (zcon (- (+ 30)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ (d ⊕ zcon (- (+ 1)))))) ⊕ (zcon (+ 30) ⊗ ((d ⊗ d) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1)))))))) ⊕ (zcon (+ 45) ⊗ ((d ⊗ d) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))) ⊕ (zcon (+ 15) ⊗ ((d ⊗ d) ⊗ (d ⊕ zcon (- (+ 1)))))) ⊕ (zcon (- (+ 15)) ⊗ (d ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))))) ⊕ (zcon (- (+ 30)) ⊗ (d ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1)))))))) ⊕ (zcon (- (+ 15)) ⊗ (d ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))) ⊕ (zcon (+ 6) ⊗ (zcon (+ 1) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1)))))))))) ⊕ (zcon (+ 15) ⊗ (zcon (+ 1) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))))) ⊕ (zcon (+ 10) ⊗ (zcon (+ 1) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1)))))))) ⊕ (zcon (- (+ 1)) ⊗ (zcon (+ 1) ⊗ (d ⊕ zcon (- (+ 1)))))) ⊜ ((((zcon (+ 21) ⊗ ((d ⊗ (d ⊗ (d ⊗ (d ⊗ d)))) ⊗ zcon (+ 1))) ⊕ (zcon (- (+ 30)) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ zcon (+ 1)))) ⊕ (zcon (+ 10) ⊗ ((d ⊗ (d ⊗ d)) ⊗ zcon (+ 1)))) ⊕ (zcon (- (+ 1)) ⊗ (d ⊗ zcon (+ 1))))) refl d
prefix2 : (d : ℤ) (n : Nat) → scaledBoundaryPrefix weight2 (+ 30) d n ≡ anti2 d (+ n)
prefix2 d zero = sym (anti2Zero d)
prefix2 d (suc n) = trans
  (cong (λ v → v +z ((+ 30) *z weight2 d (d +z ((- (+ 1)) *z (+ (suc n)))))) (prefix2 d n))
  (trans (cong (λ u → anti2 d (+ n) +z ((+ 30) *z weight2 d (d +z ((- (+ 1)) *z u)))) (sym (nextInteger n)))
    (trans (sym (anti2Step d (+ n))) (cong (anti2 d) (nextInteger n))))

anti3 : ℤ → ℤ → ℤ
anti3 d t = (((((((((((((((((((((((+ 420) *z ((d *z (d *z (d *z (d *z (d *z d))))) *z t)) +z ((- (+ 630)) *z ((d *z (d *z (d *z (d *z d)))) *z (t *z t)))) +z ((- (+ 630)) *z ((d *z (d *z (d *z (d *z d)))) *z t))) +z ((+ 840) *z ((d *z (d *z (d *z d))) *z (t *z (t *z t))))) +z ((+ 1260) *z ((d *z (d *z (d *z d))) *z (t *z t)))) +z ((+ 420) *z ((d *z (d *z (d *z d))) *z t))) +z ((- (+ 735)) *z ((d *z (d *z d)) *z (t *z (t *z (t *z t)))))) +z ((- (+ 1470)) *z ((d *z (d *z d)) *z (t *z (t *z t))))) +z ((- (+ 735)) *z ((d *z (d *z d)) *z (t *z t)))) +z ((+ 504) *z ((d *z d) *z (t *z (t *z (t *z (t *z t))))))) +z ((+ 1260) *z ((d *z d) *z (t *z (t *z (t *z t)))))) +z ((+ 840) *z ((d *z d) *z (t *z (t *z t))))) +z ((- (+ 84)) *z ((d *z d) *z t))) +z ((- (+ 210)) *z (d *z (t *z (t *z (t *z (t *z (t *z t)))))))) +z ((- (+ 630)) *z (d *z (t *z (t *z (t *z (t *z t))))))) +z ((- (+ 525)) *z (d *z (t *z (t *z (t *z t)))))) +z ((+ 105) *z (d *z (t *z t)))) +z ((+ 60) *z ((+ 1) *z (t *z (t *z (t *z (t *z (t *z (t *z t))))))))) +z ((+ 210) *z ((+ 1) *z (t *z (t *z (t *z (t *z (t *z t)))))))) +z ((+ 210) *z ((+ 1) *z (t *z (t *z (t *z (t *z t))))))) +z ((- (+ 70)) *z ((+ 1) *z (t *z (t *z t))))) +z ((+ 10) *z ((+ 1) *z t)))
boundary3 : ℤ → ℤ
boundary3 d = ((((((+ 249) *z ((d *z (d *z (d *z (d *z (d *z (d *z d)))))) *z (+ 1))) +z ((- (+ 420)) *z ((d *z (d *z (d *z (d *z (d *z d))))) *z (+ 1)))) +z ((+ 210) *z ((d *z (d *z (d *z (d *z d)))) *z (+ 1)))) +z ((- (+ 49)) *z ((d *z (d *z d)) *z (+ 1)))) +z ((+ 10) *z (d *z (+ 1))))
anti3Zero : (d : ℤ) → anti3 d (+ 0) ≡ + 0
anti3Zero d = zsolve 1 (λ d → ((((((((((((((((((((((zcon (+ 420) ⊗ ((d ⊗ (d ⊗ (d ⊗ (d ⊗ (d ⊗ d))))) ⊗ zcon (+ 0))) ⊕ (zcon (- (+ 630)) ⊗ ((d ⊗ (d ⊗ (d ⊗ (d ⊗ d)))) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))) ⊕ (zcon (- (+ 630)) ⊗ ((d ⊗ (d ⊗ (d ⊗ (d ⊗ d)))) ⊗ zcon (+ 0)))) ⊕ (zcon (+ 840) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0)))))) ⊕ (zcon (+ 1260) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))) ⊕ (zcon (+ 420) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ zcon (+ 0)))) ⊕ (zcon (- (+ 735)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))))) ⊕ (zcon (- (+ 1470)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0)))))) ⊕ (zcon (- (+ 735)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))) ⊕ (zcon (+ 504) ⊗ ((d ⊗ d) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0)))))))) ⊕ (zcon (+ 1260) ⊗ ((d ⊗ d) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))))) ⊕ (zcon (+ 840) ⊗ ((d ⊗ d) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0)))))) ⊕ (zcon (- (+ 84)) ⊗ ((d ⊗ d) ⊗ zcon (+ 0)))) ⊕ (zcon (- (+ 210)) ⊗ (d ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))))))) ⊕ (zcon (- (+ 630)) ⊗ (d ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0)))))))) ⊕ (zcon (- (+ 525)) ⊗ (d ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))))) ⊕ (zcon (+ 105) ⊗ (d ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))) ⊕ (zcon (+ 60) ⊗ (zcon (+ 1) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0)))))))))) ⊕ (zcon (+ 210) ⊗ (zcon (+ 1) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))))))) ⊕ (zcon (+ 210) ⊗ (zcon (+ 1) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0)))))))) ⊕ (zcon (- (+ 70)) ⊗ (zcon (+ 1) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0)))))) ⊕ (zcon (+ 10) ⊗ (zcon (+ 1) ⊗ zcon (+ 0)))) ⊜ zcon (+ 0)) refl d
anti3Step : (d t : ℤ) → anti3 d (t +z (+ 1)) ≡
  anti3 d t +z ((+ 420) *z weight3 d (d +z ((- (+ 1)) *z (t +z (+ 1)))))
anti3Step d t = zsolve 2 (λ d t →
  ((((((((((((((((((((((zcon (+ 420) ⊗ ((d ⊗ (d ⊗ (d ⊗ (d ⊗ (d ⊗ d))))) ⊗ (t ⊕ zcon (+ 1)))) ⊕ (zcon (- (+ 630)) ⊗ ((d ⊗ (d ⊗ (d ⊗ (d ⊗ d)))) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))) ⊕ (zcon (- (+ 630)) ⊗ ((d ⊗ (d ⊗ (d ⊗ (d ⊗ d)))) ⊗ (t ⊕ zcon (+ 1))))) ⊕ (zcon (+ 840) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))) ⊕ (zcon (+ 1260) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))) ⊕ (zcon (+ 420) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ (t ⊕ zcon (+ 1))))) ⊕ (zcon (- (+ 735)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))))) ⊕ (zcon (- (+ 1470)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))) ⊕ (zcon (- (+ 735)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))) ⊕ (zcon (+ 504) ⊗ ((d ⊗ d) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))))) ⊕ (zcon (+ 1260) ⊗ ((d ⊗ d) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))))) ⊕ (zcon (+ 840) ⊗ ((d ⊗ d) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))) ⊕ (zcon (- (+ 84)) ⊗ ((d ⊗ d) ⊗ (t ⊕ zcon (+ 1))))) ⊕ (zcon (- (+ 210)) ⊗ (d ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))))))) ⊕ (zcon (- (+ 630)) ⊗ (d ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))))) ⊕ (zcon (- (+ 525)) ⊗ (d ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))))) ⊕ (zcon (+ 105) ⊗ (d ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))) ⊕ (zcon (+ 60) ⊗ (zcon (+ 1) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))))))) ⊕ (zcon (+ 210) ⊗ (zcon (+ 1) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))))))) ⊕ (zcon (+ 210) ⊗ (zcon (+ 1) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))))) ⊕ (zcon (- (+ 70)) ⊗ (zcon (+ 1) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))) ⊕ (zcon (+ 10) ⊗ (zcon (+ 1) ⊗ (t ⊕ zcon (+ 1))))) ⊜
  (((((((((((((((((((((((zcon (+ 420) ⊗ ((d ⊗ (d ⊗ (d ⊗ (d ⊗ (d ⊗ d))))) ⊗ t)) ⊕ (zcon (- (+ 630)) ⊗ ((d ⊗ (d ⊗ (d ⊗ (d ⊗ d)))) ⊗ (t ⊗ t)))) ⊕ (zcon (- (+ 630)) ⊗ ((d ⊗ (d ⊗ (d ⊗ (d ⊗ d)))) ⊗ t))) ⊕ (zcon (+ 840) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ (t ⊗ (t ⊗ t))))) ⊕ (zcon (+ 1260) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ (t ⊗ t)))) ⊕ (zcon (+ 420) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ t))) ⊕ (zcon (- (+ 735)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ (t ⊗ (t ⊗ (t ⊗ t)))))) ⊕ (zcon (- (+ 1470)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ (t ⊗ (t ⊗ t))))) ⊕ (zcon (- (+ 735)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ (t ⊗ t)))) ⊕ (zcon (+ 504) ⊗ ((d ⊗ d) ⊗ (t ⊗ (t ⊗ (t ⊗ (t ⊗ t))))))) ⊕ (zcon (+ 1260) ⊗ ((d ⊗ d) ⊗ (t ⊗ (t ⊗ (t ⊗ t)))))) ⊕ (zcon (+ 840) ⊗ ((d ⊗ d) ⊗ (t ⊗ (t ⊗ t))))) ⊕ (zcon (- (+ 84)) ⊗ ((d ⊗ d) ⊗ t))) ⊕ (zcon (- (+ 210)) ⊗ (d ⊗ (t ⊗ (t ⊗ (t ⊗ (t ⊗ (t ⊗ t)))))))) ⊕ (zcon (- (+ 630)) ⊗ (d ⊗ (t ⊗ (t ⊗ (t ⊗ (t ⊗ t))))))) ⊕ (zcon (- (+ 525)) ⊗ (d ⊗ (t ⊗ (t ⊗ (t ⊗ t)))))) ⊕ (zcon (+ 105) ⊗ (d ⊗ (t ⊗ t)))) ⊕ (zcon (+ 60) ⊗ (zcon (+ 1) ⊗ (t ⊗ (t ⊗ (t ⊗ (t ⊗ (t ⊗ (t ⊗ t))))))))) ⊕ (zcon (+ 210) ⊗ (zcon (+ 1) ⊗ (t ⊗ (t ⊗ (t ⊗ (t ⊗ (t ⊗ t)))))))) ⊕ (zcon (+ 210) ⊗ (zcon (+ 1) ⊗ (t ⊗ (t ⊗ (t ⊗ (t ⊗ t))))))) ⊕ (zcon (- (+ 70)) ⊗ (zcon (+ 1) ⊗ (t ⊗ (t ⊗ t))))) ⊕ (zcon (+ 10) ⊗ (zcon (+ 1) ⊗ t))) ⊕ (zcon (+ 420) ⊗ ((((d ⊗ d) ⊕ (zcon (- (+ 1)) ⊗ (d ⊗ (d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))) ⊕ ((d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1)))) ⊗ (d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))) ⊗ ((((d ⊗ d) ⊕ (zcon (- (+ 1)) ⊗ (d ⊗ (d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))) ⊕ ((d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1)))) ⊗ (d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))) ⊗ (((d ⊗ d) ⊕ (zcon (- (+ 1)) ⊗ (d ⊗ (d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))) ⊕ ((d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1)))) ⊗ (d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))))))) refl d t
anti3AtEnd : (d : ℤ) → anti3 d (d +z (- (+ 1))) ≡ boundary3 d
anti3AtEnd d = zsolve 1 (λ d →
  ((((((((((((((((((((((zcon (+ 420) ⊗ ((d ⊗ (d ⊗ (d ⊗ (d ⊗ (d ⊗ d))))) ⊗ (d ⊕ zcon (- (+ 1))))) ⊕ (zcon (- (+ 630)) ⊗ ((d ⊗ (d ⊗ (d ⊗ (d ⊗ d)))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))) ⊕ (zcon (- (+ 630)) ⊗ ((d ⊗ (d ⊗ (d ⊗ (d ⊗ d)))) ⊗ (d ⊕ zcon (- (+ 1)))))) ⊕ (zcon (+ 840) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1)))))))) ⊕ (zcon (+ 1260) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))) ⊕ (zcon (+ 420) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ (d ⊕ zcon (- (+ 1)))))) ⊕ (zcon (- (+ 735)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))))) ⊕ (zcon (- (+ 1470)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1)))))))) ⊕ (zcon (- (+ 735)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))) ⊕ (zcon (+ 504) ⊗ ((d ⊗ d) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1)))))))))) ⊕ (zcon (+ 1260) ⊗ ((d ⊗ d) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))))) ⊕ (zcon (+ 840) ⊗ ((d ⊗ d) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1)))))))) ⊕ (zcon (- (+ 84)) ⊗ ((d ⊗ d) ⊗ (d ⊕ zcon (- (+ 1)))))) ⊕ (zcon (- (+ 210)) ⊗ (d ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))))))) ⊕ (zcon (- (+ 630)) ⊗ (d ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1)))))))))) ⊕ (zcon (- (+ 525)) ⊗ (d ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))))) ⊕ (zcon (+ 105) ⊗ (d ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))) ⊕ (zcon (+ 60) ⊗ (zcon (+ 1) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1)))))))))))) ⊕ (zcon (+ 210) ⊗ (zcon (+ 1) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))))))) ⊕ (zcon (+ 210) ⊗ (zcon (+ 1) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1)))))))))) ⊕ (zcon (- (+ 70)) ⊗ (zcon (+ 1) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1)))))))) ⊕ (zcon (+ 10) ⊗ (zcon (+ 1) ⊗ (d ⊕ zcon (- (+ 1)))))) ⊜ (((((zcon (+ 249) ⊗ ((d ⊗ (d ⊗ (d ⊗ (d ⊗ (d ⊗ (d ⊗ d)))))) ⊗ zcon (+ 1))) ⊕ (zcon (- (+ 420)) ⊗ ((d ⊗ (d ⊗ (d ⊗ (d ⊗ (d ⊗ d))))) ⊗ zcon (+ 1)))) ⊕ (zcon (+ 210) ⊗ ((d ⊗ (d ⊗ (d ⊗ (d ⊗ d)))) ⊗ zcon (+ 1)))) ⊕ (zcon (- (+ 49)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ zcon (+ 1)))) ⊕ (zcon (+ 10) ⊗ (d ⊗ zcon (+ 1))))) refl d
prefix3 : (d : ℤ) (n : Nat) → scaledBoundaryPrefix weight3 (+ 420) d n ≡ anti3 d (+ n)
prefix3 d zero = sym (anti3Zero d)
prefix3 d (suc n) = trans
  (cong (λ v → v +z ((+ 420) *z weight3 d (d +z ((- (+ 1)) *z (+ (suc n)))))) (prefix3 d n))
  (trans (cong (λ u → anti3 d (+ n) +z ((+ 420) *z weight3 d (d +z ((- (+ 1)) *z u)))) (sym (nextInteger n)))
    (trans (sym (anti3Step d (+ n))) (cong (anti3 d) (nextInteger n))))

anti4 : ℤ → ℤ → ℤ
anti4 d t = (((((((((((+ 10) *z ((d *z (d *z (d *z d))) *z (t *z (t *z t)))) +z ((+ 15) *z ((d *z (d *z (d *z d))) *z (t *z t)))) +z ((+ 5) *z ((d *z (d *z (d *z d))) *z t))) +z ((- (+ 15)) *z ((d *z (d *z d)) *z (t *z (t *z (t *z t)))))) +z ((- (+ 30)) *z ((d *z (d *z d)) *z (t *z (t *z t))))) +z ((- (+ 15)) *z ((d *z (d *z d)) *z (t *z t)))) +z ((+ 6) *z ((d *z d) *z (t *z (t *z (t *z (t *z t))))))) +z ((+ 15) *z ((d *z d) *z (t *z (t *z (t *z t)))))) +z ((+ 10) *z ((d *z d) *z (t *z (t *z t))))) +z ((- (+ 1)) *z ((d *z d) *z t)))
boundary4 : ℤ → ℤ
boundary4 d = (((+ 1) *z ((d *z (d *z (d *z (d *z (d *z (d *z d)))))) *z (+ 1))) +z ((- (+ 1)) *z ((d *z (d *z d)) *z (+ 1))))
anti4Zero : (d : ℤ) → anti4 d (+ 0) ≡ + 0
anti4Zero d = zsolve 1 (λ d → ((((((((((zcon (+ 10) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))) ⊕ (zcon (+ 15) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))) ⊕ (zcon (+ 5) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ zcon (+ 0)))) ⊕ (zcon (- (+ 15)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))))) ⊕ (zcon (- (+ 30)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0)))))) ⊕ (zcon (- (+ 15)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))) ⊕ (zcon (+ 6) ⊗ ((d ⊗ d) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0)))))))) ⊕ (zcon (+ 15) ⊗ ((d ⊗ d) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0))))))) ⊕ (zcon (+ 10) ⊗ ((d ⊗ d) ⊗ (zcon (+ 0) ⊗ (zcon (+ 0) ⊗ zcon (+ 0)))))) ⊕ (zcon (- (+ 1)) ⊗ ((d ⊗ d) ⊗ zcon (+ 0)))) ⊜ zcon (+ 0)) refl d
anti4Step : (d t : ℤ) → anti4 d (t +z (+ 1)) ≡
  anti4 d t +z ((+ 30) *z weight4 d (d +z ((- (+ 1)) *z (t +z (+ 1)))))
anti4Step d t = zsolve 2 (λ d t →
  ((((((((((zcon (+ 10) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))) ⊕ (zcon (+ 15) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))) ⊕ (zcon (+ 5) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ (t ⊕ zcon (+ 1))))) ⊕ (zcon (- (+ 15)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))))) ⊕ (zcon (- (+ 30)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))) ⊕ (zcon (- (+ 15)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))) ⊕ (zcon (+ 6) ⊗ ((d ⊗ d) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))))) ⊕ (zcon (+ 15) ⊗ ((d ⊗ d) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))))) ⊕ (zcon (+ 10) ⊗ ((d ⊗ d) ⊗ ((t ⊕ zcon (+ 1)) ⊗ ((t ⊕ zcon (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))) ⊕ (zcon (- (+ 1)) ⊗ ((d ⊗ d) ⊗ (t ⊕ zcon (+ 1))))) ⊜
  (((((((((((zcon (+ 10) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ (t ⊗ (t ⊗ t)))) ⊕ (zcon (+ 15) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ (t ⊗ t)))) ⊕ (zcon (+ 5) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ t))) ⊕ (zcon (- (+ 15)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ (t ⊗ (t ⊗ (t ⊗ t)))))) ⊕ (zcon (- (+ 30)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ (t ⊗ (t ⊗ t))))) ⊕ (zcon (- (+ 15)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ (t ⊗ t)))) ⊕ (zcon (+ 6) ⊗ ((d ⊗ d) ⊗ (t ⊗ (t ⊗ (t ⊗ (t ⊗ t))))))) ⊕ (zcon (+ 15) ⊗ ((d ⊗ d) ⊗ (t ⊗ (t ⊗ (t ⊗ t)))))) ⊕ (zcon (+ 10) ⊗ ((d ⊗ d) ⊗ (t ⊗ (t ⊗ t))))) ⊕ (zcon (- (+ 1)) ⊗ ((d ⊗ d) ⊗ t))) ⊕ (zcon (+ 30) ⊗ (((d ⊗ d) ⊗ ((d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1)))) ⊗ (d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))) ⊗ ((d ⊕ (zcon (- (+ 1)) ⊗ (d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1)))))) ⊗ (d ⊕ (zcon (- (+ 1)) ⊗ (d ⊕ (zcon (- (+ 1)) ⊗ (t ⊕ zcon (+ 1))))))))))) refl d t
anti4AtEnd : (d : ℤ) → anti4 d (d +z (- (+ 1))) ≡ boundary4 d
anti4AtEnd d = zsolve 1 (λ d →
  ((((((((((zcon (+ 10) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))) ⊕ (zcon (+ 15) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))) ⊕ (zcon (+ 5) ⊗ ((d ⊗ (d ⊗ (d ⊗ d))) ⊗ (d ⊕ zcon (- (+ 1)))))) ⊕ (zcon (- (+ 15)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))))) ⊕ (zcon (- (+ 30)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1)))))))) ⊕ (zcon (- (+ 15)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))) ⊕ (zcon (+ 6) ⊗ ((d ⊗ d) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1)))))))))) ⊕ (zcon (+ 15) ⊗ ((d ⊗ d) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1))))))))) ⊕ (zcon (+ 10) ⊗ ((d ⊗ d) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ ((d ⊕ zcon (- (+ 1))) ⊗ (d ⊕ zcon (- (+ 1)))))))) ⊕ (zcon (- (+ 1)) ⊗ ((d ⊗ d) ⊗ (d ⊕ zcon (- (+ 1)))))) ⊜ ((zcon (+ 1) ⊗ ((d ⊗ (d ⊗ (d ⊗ (d ⊗ (d ⊗ (d ⊗ d)))))) ⊗ zcon (+ 1))) ⊕ (zcon (- (+ 1)) ⊗ ((d ⊗ (d ⊗ d)) ⊗ zcon (+ 1))))) refl d
prefix4 : (d : ℤ) (n : Nat) → scaledBoundaryPrefix weight4 (+ 30) d n ≡ anti4 d (+ n)
prefix4 d zero = sym (anti4Zero d)
prefix4 d (suc n) = trans
  (cong (λ v → v +z ((+ 30) *z weight4 d (d +z ((- (+ 1)) *z (+ (suc n)))))) (prefix4 d n))
  (trans (cong (λ u → anti4 d (+ n) +z ((+ 30) *z weight4 d (d +z ((- (+ 1)) *z u)))) (sym (nextInteger n)))
    (trans (sym (anti4Step d (+ n))) (cong (anti4 d) (nextInteger n))))

previousInteger : (n : Nat) → (+ n) ≡ ((+ (suc n)) +z (- (+ 1)))
previousInteger n = trans
  (zsolve 1 (λ t → t ⊜ (t ⊕ zcon (+ 1)) ⊕ zcon (- (+ 1))) refl (+ n))
  (cong (λ t → t +z (- (+ 1))) (nextInteger n))

boundaryClosed1 : (n : Nat) →
  scaledBoundaryPrefix weight1 (+ 6) (+ (suc n)) n ≡ boundary1 (+ (suc n))
boundaryClosed1 n = trans (prefix1 (+ (suc n)) n)
  (trans (cong (anti1 (+ (suc n))) (previousInteger n)) (anti1AtEnd (+ (suc n))))

boundaryClosed2 : (n : Nat) →
  scaledBoundaryPrefix weight2 (+ 30) (+ (suc n)) n ≡ boundary2 (+ (suc n))
boundaryClosed2 n = trans (prefix2 (+ (suc n)) n)
  (trans (cong (anti2 (+ (suc n))) (previousInteger n)) (anti2AtEnd (+ (suc n))))

boundaryClosed3 : (n : Nat) →
  scaledBoundaryPrefix weight3 (+ 420) (+ (suc n)) n ≡ boundary3 (+ (suc n))
boundaryClosed3 n = trans (prefix3 (+ (suc n)) n)
  (trans (cong (anti3 (+ (suc n))) (previousInteger n)) (anti3AtEnd (+ (suc n))))

boundaryClosed4 : (n : Nat) →
  scaledBoundaryPrefix weight4 (+ 30) (+ (suc n)) n ≡ boundary4 (+ (suc n))
boundaryClosed4 n = trans (prefix4 (+ (suc n)) n)
  (trans (cong (anti4 (+ (suc n))) (previousInteger n)) (anti4AtEnd (+ (suc n))))
