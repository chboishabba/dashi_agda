module DASHI.Moonshine.JInvariantThetaLegendreSignedGeometryExact where

-- Classical Jacobi theta and Legendre invariants. DASHI contribution:
-- use the existing homogeneous integer kernel and its actual E8
-- coefficient consumer. Keep the sign of E6, and the orientation of V.
-- Source-written, local kernel pending.
open import Agda.Builtin.Nat using (Nat; zero; suc) renaming (_+_ to _+N_; _*_ to _*N_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
import DASHI.Moonshine.JInvariantLambdaOrbitIntegerKernelExact as L
import DASHI.Moonshine.AbelE8RootE4FirstCoefficientExact as Roots
import DASHI.Moonshine.JInvariantEisensteinCoefficientTowerExact as Tower
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Algebra.Trit.E8RootEnumeration as E8
open L using (Homogeneous; pair; quadratic)

v : Homogeneous → ℤ
v (pair a b) = a * b * (b - a)

-- IMPORTANT: W=(a+b)(2a-b)(a-2b) has W(0,1)=+2.
-- This W equals 2E6 for the theta coordinates a=A,b=B.
w : Homogeneous → ℤ
w (pair a b) = (a + b) * ((+ 2) * a - b) * (a - (+ 2) * b)

denomRead : ∀ x → L.denominator x ≡ v x * v x
denomRead (pair a b) = refl

discriminant : ∀ x → (+ 4) * quadratic x * quadratic x * quadratic x
  ≡ w x * w x + (+ 27) * v x * v x
discriminant (pair a b) = solve 2
  (λ a b → con (+ 4) :* (a :* a :- a :* b :+ b :* b)
    :* (a :* a :- a :* b :+ b :* b) :* (a :* a :- a :* b :+ b :* b)
    := ((a :+ b) :* (con (+ 2) :* a :- b) :* (a :- con (+ 2) :* b))
    :* ((a :+ b) :* (con (+ 2) :* a :- b) :* (a :- con (+ 2) :* b))
    :+ con (+ 27) :* (a :* b :* (b :- a)) :* (a :* b :* (b :- a)))
  refl a b

-- t ↦ -t exchanges B,C and negates A, rather than forgetting the
-- sign of the half-period. Both modular observations are unchanged.
sheet : Homogeneous → Homogeneous
sheet (pair a b) = pair (- a) (b - a)

sheetQ : ∀ x → quadratic (sheet x) ≡ quadratic x
sheetQ (pair a b) = solve 2
  (λ a b → (con (+ 0) :- a) :* (con (+ 0) :- a)
    :- (con (+ 0) :- a) :* (b :- a) :+ (b :- a) :* (b :- a)
    := a :* a :- a :* b :+ b :* b) refl a b

sheetV : ∀ x → v (sheet x) ≡ - v x
sheetV (pair a b) = solve 2
  (λ a b → (con (+ 0) :- a) :* (b :- a) :* ((b :- a) :- (con (+ 0) :- a))
    := con (+ 0) :- (a :* b :* (b :- a))) refl a b

sheetW : ∀ x → w (sheet x) ≡ w x
sheetW (pair a b) = solve 2
  (λ a b → ((con (+ 0) :- a) :+ (b :- a))
    :* (con (+ 2) :* (con (+ 0) :- a) :- (b :- a))
    :* ((con (+ 0) :- a) :- con (+ 2) :* (b :- a))
    := (a :+ b) :* (con (+ 2) :* a :- b) :* (a :- con (+ 2) :* b))
  refl a b

-- Literal coefficient histories from signed square and triangular
-- exponent fibres. The finite scan includes index 0; no oracle for
-- square roots or for Jacobi's identity.
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (yes; no)

count : (Nat → Nat) → Nat → Nat → Nat
count f n zero with f zero ≟ n
... | yes _ = 1
... | no _ = 0
count f n (suc k) with f (suc k) ≟ n
... | yes _ = suc (count f n k)
... | no _ = count f n k

sqN : Nat → Nat
sqN k = k *N k
triN : Nat → Nat
triN k = k *N suc k

theta3 : I.SeriesZ
theta3 zero = + 1
theta3 (suc n) = + (2 *N count sqN (suc n) (suc n))

sign : Nat → ℤ
sign zero = + 1
sign (suc n) = - sign n

theta4 : I.SeriesZ
theta4 n = sign n * theta3 n

halfTheta : I.SeriesZ
halfTheta n = + count triN n n

fourth : I.SeriesZ → I.SeriesZ
fourth f = I.rowZ (I.rowZ f f) (I.rowZ f f)

A B C : I.SeriesZ
A zero = + 0
A (suc n) = (+ 16) * fourth halfTheta n
B = fourth theta3
C = fourth theta4

add sub : I.SeriesZ → I.SeriesZ → I.SeriesZ
add f g n = f n + g n
sub f g n = f n - g n
mul = I.rowZ

-- Cleared theta polynomial expressions. No division on the integer
-- coefficient carrier; only the final even coefficient is divided.
qTheta : I.SeriesZ
qTheta = add (sub (mul A A) (mul A B)) (mul B B)

wTheta : I.SeriesZ
wTheta = mul (mul (add A B) (sub (add A A) B)) (sub A (add B B))

vTheta : I.SeriesZ
vTheta = mul (mul A B) (sub B A)

a0 : A 0 ≡ + 0
a0 = refl
a1 : A 1 ≡ + 16
a1 = refl
a2 : A 2 ≡ + 0
a2 = refl
b0 : B 0 ≡ + 1
b0 = refl
b1 : B 1 ≡ + 8
b1 = refl
b2 : B 2 ≡ + 24
b2 = refl
c0 : C 0 ≡ + 1
c0 = refl
c1 : C 1 ≡ - (+ 8)
c1 = refl
c2 : C 2 ≡ + 24
c2 = refl

theta4Unit : qTheta 0 ≡ + 1
theta4Unit = refl
theta4Odd : qTheta 1 ≡ + 0
theta4Odd = refl
theta6Unit : wTheta 0 ≡ + 2
theta6Unit = refl
theta6Odd : wTheta 1 ≡ + 0
theta6Odd = refl

theta4First : qTheta 2 ≡ + 240
theta4First = refl
theta6FirstCleared : wTheta 2 ≡ - (+ 1008)
theta6FirstCleared = refl

theta4Original : qTheta 2 ≡ Tower.e4Coefficient 1
theta4Original = refl
theta6OriginalCleared : wTheta 2 ≡ (+ 2) * Tower.e6Coefficient 1
theta6OriginalCleared = refl

-- Independently computed theta first-shell, not the E4 recurrence.
theta4RootRead : qTheta 2 ≡ + (E8.indexedRootListLength
  E8.combinedIndexedRoots)
theta4RootRead = trans theta4First (cong +_ (sym Roots.originalE8GeneratedRootCount))

-- Delta first coefficient in t²: V=16t+..., V²=256t²+...
discFirst : mul vTheta vTheta 2 ≡ + 256
discFirst = refl

-- B=A+C checked only at these explicit source coefficients. Global
-- Jacobi identity, absolute evaluation and modular uniqueness remain
-- separate producer obligations.
jacobi0 : B 0 ≡ A 0 + C 0
jacobi0 = refl
jacobi1 : B 1 ≡ A 1 + C 1
jacobi1 = refl
jacobi2 : B 2 ≡ A 2 + C 2
jacobi2 = refl
