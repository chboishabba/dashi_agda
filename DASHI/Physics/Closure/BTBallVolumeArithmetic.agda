module DASHI.Physics.Closure.BTBallVolumeArithmetic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

------------------------------------------------------------------------
-- Concrete Bruhat-Tits regular-tree ball/sphere arithmetic.
--
-- For the (q + 1)-regular tree rooted at a vertex:
--
--   sphere(0)     = 1
--   sphere(n + 1) = (q + 1) * q^n
--   ball(r)       = sum_{0 <= n <= r} sphere(n)
--
-- This is finite Nat-level bookkeeping only.  It does not promote any
-- continuum, analytic, Yang-Mills, Navier-Stokes, Perelman, or Clay claim.

pow : Nat → Nat → Nat
pow base zero =
  1
pow base (suc exponent) =
  base * pow base exponent

sphereCount : Nat → Nat → Nat
sphereCount q zero =
  1
sphereCount q (suc radius) =
  suc q * pow q radius

ballCount : Nat → Nat → Nat
ballCount q zero =
  1
ballCount q (suc radius) =
  ballCount q radius + sphereCount q (suc radius)

T2Branching : Nat
T2Branching =
  2

T3Branching : Nat
T3Branching =
  3

T7Branching : Nat
T7Branching =
  7

T2Valency : Nat
T2Valency =
  suc T2Branching

T3Valency : Nat
T3Valency =
  suc T3Branching

T7Valency : Nat
T7Valency =
  suc T7Branching

T2SphereCount : Nat → Nat
T2SphereCount =
  sphereCount T2Branching

T3SphereCount : Nat → Nat
T3SphereCount =
  sphereCount T3Branching

T7SphereCount : Nat → Nat
T7SphereCount =
  sphereCount T7Branching

T2BallCount : Nat → Nat
T2BallCount =
  ballCount T2Branching

T3BallCount : Nat → Nat
T3BallCount =
  ballCount T3Branching

T7BallCount : Nat → Nat
T7BallCount =
  ballCount T7Branching

productSphereCount :
  Nat → Nat → Nat →
  Nat → Nat → Nat →
  Nat
productSphereCount qA qB qC rA rB rC =
  sphereCount qA rA * sphereCount qB rB * sphereCount qC rC

productBallCount :
  Nat → Nat → Nat →
  Nat → Nat → Nat →
  Nat
productBallCount qA qB qC rA rB rC =
  ballCount qA rA * ballCount qB rB * ballCount qC rC

T3xT2xT7SphereCount :
  Nat → Nat → Nat →
  Nat
T3xT2xT7SphereCount =
  productSphereCount T3Branching T2Branching T7Branching

T3xT2xT7BallCount :
  Nat → Nat → Nat →
  Nat
T3xT2xT7BallCount =
  productBallCount T3Branching T2Branching T7Branching

T3xT2xT7PositiveSphereLeadingFactor : Nat
T3xT2xT7PositiveSphereLeadingFactor =
  T3Valency * T2Valency * T7Valency

T3xT2xT7PositiveSphereLeadingFactorIs96 :
  T3xT2xT7PositiveSphereLeadingFactor ≡ 96
T3xT2xT7PositiveSphereLeadingFactorIs96 =
  refl

T3xT2xT7AsymptoticBallPrefactorNumerator : Nat
T3xT2xT7AsymptoticBallPrefactorNumerator =
  T3Valency * T2Valency * T7Valency

T3AsymptoticBallDenominatorFactor : Nat
T3AsymptoticBallDenominatorFactor =
  2

T2AsymptoticBallDenominatorFactor : Nat
T2AsymptoticBallDenominatorFactor =
  1

T7AsymptoticBallDenominatorFactor : Nat
T7AsymptoticBallDenominatorFactor =
  6

T3xT2xT7AsymptoticBallPrefactorDenominator : Nat
T3xT2xT7AsymptoticBallPrefactorDenominator =
  T3AsymptoticBallDenominatorFactor
  *
  T2AsymptoticBallDenominatorFactor
  *
  T7AsymptoticBallDenominatorFactor

T3xT2xT7AsymptoticBallPrefactorNumeratorIs96 :
  T3xT2xT7AsymptoticBallPrefactorNumerator ≡ 96
T3xT2xT7AsymptoticBallPrefactorNumeratorIs96 =
  refl

T3xT2xT7AsymptoticBallPrefactorDenominatorIs12 :
  T3xT2xT7AsymptoticBallPrefactorDenominator ≡ 12
T3xT2xT7AsymptoticBallPrefactorDenominatorIs12 =
  refl

T3xT2xT7AsymptoticBallPrefactorQuotient : Nat
T3xT2xT7AsymptoticBallPrefactorQuotient =
  8

T3xT2xT7AsymptoticBallPrefactorCheck :
  T3xT2xT7AsymptoticBallPrefactorDenominator
  *
  T3xT2xT7AsymptoticBallPrefactorQuotient
  ≡
  T3xT2xT7AsymptoticBallPrefactorNumerator
T3xT2xT7AsymptoticBallPrefactorCheck =
  refl

T3xT2xT7PositiveSphereMonomial :
  Nat → Nat → Nat →
  Nat
T3xT2xT7PositiveSphereMonomial a b c =
  T3Valency * pow T3Branching a
  * (T2Valency * pow T2Branching b)
  * (T7Valency * pow T7Branching c)

T3xT2xT7PositiveSphereMonomialMatchesProduct :
  (a b c : Nat) →
  T3xT2xT7PositiveSphereMonomial a b c
  ≡
  T3xT2xT7SphereCount (suc a) (suc b) (suc c)
T3xT2xT7PositiveSphereMonomialMatchesProduct a b c =
  refl

T2SphereR0Is1 : T2SphereCount 0 ≡ 1
T2SphereR0Is1 =
  refl

T2SphereR1Is3 : T2SphereCount 1 ≡ 3
T2SphereR1Is3 =
  refl

T2SphereR2Is6 : T2SphereCount 2 ≡ 6
T2SphereR2Is6 =
  refl

T2BallR2Is10 : T2BallCount 2 ≡ 10
T2BallR2Is10 =
  refl

T2BallR4Is46 : T2BallCount 4 ≡ 46
T2BallR4Is46 =
  refl

T3SphereR0Is1 : T3SphereCount 0 ≡ 1
T3SphereR0Is1 =
  refl

T3SphereR1Is4 : T3SphereCount 1 ≡ 4
T3SphereR1Is4 =
  refl

T3SphereR2Is12 : T3SphereCount 2 ≡ 12
T3SphereR2Is12 =
  refl

T3BallR2Is17 : T3BallCount 2 ≡ 17
T3BallR2Is17 =
  refl

T3BallR4Is161 : T3BallCount 4 ≡ 161
T3BallR4Is161 =
  refl

T7SphereR0Is1 : T7SphereCount 0 ≡ 1
T7SphereR0Is1 =
  refl

T7SphereR1Is8 : T7SphereCount 1 ≡ 8
T7SphereR1Is8 =
  refl

T7SphereR2Is56 : T7SphereCount 2 ≡ 56
T7SphereR2Is56 =
  refl

T7BallR2Is65 : T7BallCount 2 ≡ 65
T7BallR2Is65 =
  refl

T7BallR4Is3201 : T7BallCount 4 ≡ 3201
T7BallR4Is3201 =
  refl

T3xT2xT7Sphere111Is96 :
  T3xT2xT7SphereCount 1 1 1 ≡ 96
T3xT2xT7Sphere111Is96 =
  refl

T3xT2xT7Sphere211Is288 :
  T3xT2xT7SphereCount 2 1 1 ≡ 288
T3xT2xT7Sphere211Is288 =
  refl

T3xT2xT7Sphere121Is192 :
  T3xT2xT7SphereCount 1 2 1 ≡ 192
T3xT2xT7Sphere121Is192 =
  refl

T3xT2xT7Sphere112Is672 :
  T3xT2xT7SphereCount 1 1 2 ≡ 672
T3xT2xT7Sphere112Is672 =
  refl

T3xT2xT7Sphere222Is4032 :
  T3xT2xT7SphereCount 2 2 2 ≡ 4032
T3xT2xT7Sphere222Is4032 =
  refl

T3xT2xT7Ball000Is1 :
  T3xT2xT7BallCount 0 0 0 ≡ 1
T3xT2xT7Ball000Is1 =
  refl

T3xT2xT7Ball111Is180 :
  T3xT2xT7BallCount 1 1 1 ≡ 180
T3xT2xT7Ball111Is180 =
  refl

T3xT2xT7Ball222Is11050 :
  T3xT2xT7BallCount 2 2 2 ≡ 11050
T3xT2xT7Ball222Is11050 =
  refl
