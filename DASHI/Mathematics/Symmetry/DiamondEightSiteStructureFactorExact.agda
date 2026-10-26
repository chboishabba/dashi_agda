module DASHI.Mathematics.Symmetry.DiamondEightSiteStructureFactorExact where

-- Classical diamond diffraction: source IUCr #227, equal-atom basis.
-- The eight sites share the native DiamondFccPrimitiveGlideExact
-- quarter conventional-cell coordinates. Fourth-root phase arithmetic
-- is Gaussian integer arithmetic, not a quantum or measured signal.
-- Finite 64-case proof source; Agda compiler acceptance unverified.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Integer using (ℤ; +_; -_; _+_; _-_; _*_)
import DASHI.Mathematics.Symmetry.TetragonalD4hNormalFormExact as D

data QPoint : Set where
  p000 p022 p202 p220 p111 p133 p313 p331 : QPoint

data Gaussian : Set where
  gaussian : ℤ → ℤ → Gaussian

gzero : Gaussian
gzero = gaussian (+ 0) (+ 0)
gone : Gaussian
gone = gaussian (+ 1) (+ 0)

gadd : Gaussian → Gaussian → Gaussian
gadd (gaussian a b) (gaussian c d) = gaussian (a + c) (b + d)

gmul : Gaussian → Gaussian → Gaussian
gmul (gaussian a b) (gaussian c d) =
  gaussian (a * c - b * d) (a * d + b * c)

norm2 : Gaussian → ℤ
norm2 (gaussian a b) = a * a + b * b

phase : D.Quarter → Gaussian
phase D.q0 = gaussian (+ 1) (+ 0)
phase D.q1 = gaussian (+ 0) (+ 1)
phase D.q2 = gaussian (- (+ 1)) (+ 0)
phase D.q3 = gaussian (+ 0) (- (+ 1))

mul4 : D.Quarter → D.Quarter → D.Quarter
mul4 D.q0 b = D.q0
mul4 D.q1 b = b
mul4 D.q2 b = D.add b b
mul4 D.q3 b = D.add b (D.add b b)

coordPhase : QPoint → D.Quarter → D.Quarter → D.Quarter → D.Quarter
coordPhase p000 h k l = D.q0
coordPhase p022 h k l = D.add (mul4 D.q2 k) (mul4 D.q2 l)
coordPhase p202 h k l = D.add (mul4 D.q2 h) (mul4 D.q2 l)
coordPhase p220 h k l = D.add (mul4 D.q2 h) (mul4 D.q2 k)
coordPhase p111 h k l = D.add h (D.add k l)
coordPhase p133 h k l = D.add h (D.add (mul4 D.q3 k) (mul4 D.q3 l))
coordPhase p313 h k l = D.add (mul4 D.q3 h) (D.add k (mul4 D.q3 l))
coordPhase p331 h k l = D.add (mul4 D.q3 h) (D.add (mul4 D.q3 k) l)

sitePhase : QPoint → D.Quarter → D.Quarter → D.Quarter → Gaussian
sitePhase p h k l = phase (coordPhase p h k l)

fccFactor : D.Quarter → D.Quarter → D.Quarter → Gaussian
fccFactor h k l =
  gadd (gadd (sitePhase p000 h k l) (sitePhase p022 h k l))
       (gadd (sitePhase p202 h k l) (sitePhase p220 h k l))

eightSiteAmplitude : D.Quarter → D.Quarter → D.Quarter → Gaussian
eightSiteAmplitude h k l =
  gadd (fccFactor h k l)
       (gadd (gadd (sitePhase p111 h k l) (sitePhase p133 h k l))
             (gadd (sitePhase p313 h k l) (sitePhase p331 h k l)))

sum3 : D.Quarter → D.Quarter → D.Quarter → D.Quarter
sum3 h k l = D.add h (D.add k l)

factorizedAmplitude : D.Quarter → D.Quarter → D.Quarter → Gaussian
factorizedAmplitude h k l =
  gmul (fccFactor h k l)
       (gadd gone (phase (sum3 h k l)))

odd : D.Quarter → Bool
odd D.q0 = false
odd D.q1 = true
odd D.q2 = false
odd D.q3 = true

same : Bool → Bool → Bool
same false false = true
same true true = true
same false true = false
same true false = false

and : Bool → Bool → Bool
and true true = true
and _ _ = false

choose : Bool → ℤ → ℤ → ℤ
choose true x y = x
choose false x y = y

unmixed : D.Quarter → D.Quarter → D.Quarter → Bool
unmixed h k l =
  and (same (odd h) (odd k)) (same (odd k) (odd l))

unmixedIntensity : D.Quarter → ℤ
unmixedIntensity D.q0 = + 64
unmixedIntensity D.q1 = + 32
unmixedIntensity D.q2 = + 0
unmixedIntensity D.q3 = + 32

expectedIntensity : D.Quarter → D.Quarter → D.Quarter → ℤ
expectedIntensity h k l =
  choose (unmixed h k l) (unmixedIntensity (sum3 h k l)) (+ 0)

eightSiteFactorization : (h k l : D.Quarter) →
  eightSiteAmplitude h k l ≡ factorizedAmplitude h k l
eightSiteFactorization D.q0 D.q0 D.q0 = refl
eightSiteFactorization D.q0 D.q0 D.q1 = refl
eightSiteFactorization D.q0 D.q0 D.q2 = refl
eightSiteFactorization D.q0 D.q0 D.q3 = refl
eightSiteFactorization D.q0 D.q1 D.q0 = refl
eightSiteFactorization D.q0 D.q1 D.q1 = refl
eightSiteFactorization D.q0 D.q1 D.q2 = refl
eightSiteFactorization D.q0 D.q1 D.q3 = refl
eightSiteFactorization D.q0 D.q2 D.q0 = refl
eightSiteFactorization D.q0 D.q2 D.q1 = refl
eightSiteFactorization D.q0 D.q2 D.q2 = refl
eightSiteFactorization D.q0 D.q2 D.q3 = refl
eightSiteFactorization D.q0 D.q3 D.q0 = refl
eightSiteFactorization D.q0 D.q3 D.q1 = refl
eightSiteFactorization D.q0 D.q3 D.q2 = refl
eightSiteFactorization D.q0 D.q3 D.q3 = refl
eightSiteFactorization D.q1 D.q0 D.q0 = refl
eightSiteFactorization D.q1 D.q0 D.q1 = refl
eightSiteFactorization D.q1 D.q0 D.q2 = refl
eightSiteFactorization D.q1 D.q0 D.q3 = refl
eightSiteFactorization D.q1 D.q1 D.q0 = refl
eightSiteFactorization D.q1 D.q1 D.q1 = refl
eightSiteFactorization D.q1 D.q1 D.q2 = refl
eightSiteFactorization D.q1 D.q1 D.q3 = refl
eightSiteFactorization D.q1 D.q2 D.q0 = refl
eightSiteFactorization D.q1 D.q2 D.q1 = refl
eightSiteFactorization D.q1 D.q2 D.q2 = refl
eightSiteFactorization D.q1 D.q2 D.q3 = refl
eightSiteFactorization D.q1 D.q3 D.q0 = refl
eightSiteFactorization D.q1 D.q3 D.q1 = refl
eightSiteFactorization D.q1 D.q3 D.q2 = refl
eightSiteFactorization D.q1 D.q3 D.q3 = refl
eightSiteFactorization D.q2 D.q0 D.q0 = refl
eightSiteFactorization D.q2 D.q0 D.q1 = refl
eightSiteFactorization D.q2 D.q0 D.q2 = refl
eightSiteFactorization D.q2 D.q0 D.q3 = refl
eightSiteFactorization D.q2 D.q1 D.q0 = refl
eightSiteFactorization D.q2 D.q1 D.q1 = refl
eightSiteFactorization D.q2 D.q1 D.q2 = refl
eightSiteFactorization D.q2 D.q1 D.q3 = refl
eightSiteFactorization D.q2 D.q2 D.q0 = refl
eightSiteFactorization D.q2 D.q2 D.q1 = refl
eightSiteFactorization D.q2 D.q2 D.q2 = refl
eightSiteFactorization D.q2 D.q2 D.q3 = refl
eightSiteFactorization D.q2 D.q3 D.q0 = refl
eightSiteFactorization D.q2 D.q3 D.q1 = refl
eightSiteFactorization D.q2 D.q3 D.q2 = refl
eightSiteFactorization D.q2 D.q3 D.q3 = refl
eightSiteFactorization D.q3 D.q0 D.q0 = refl
eightSiteFactorization D.q3 D.q0 D.q1 = refl
eightSiteFactorization D.q3 D.q0 D.q2 = refl
eightSiteFactorization D.q3 D.q0 D.q3 = refl
eightSiteFactorization D.q3 D.q1 D.q0 = refl
eightSiteFactorization D.q3 D.q1 D.q1 = refl
eightSiteFactorization D.q3 D.q1 D.q2 = refl
eightSiteFactorization D.q3 D.q1 D.q3 = refl
eightSiteFactorization D.q3 D.q2 D.q0 = refl
eightSiteFactorization D.q3 D.q2 D.q1 = refl
eightSiteFactorization D.q3 D.q2 D.q2 = refl
eightSiteFactorization D.q3 D.q2 D.q3 = refl
eightSiteFactorization D.q3 D.q3 D.q0 = refl
eightSiteFactorization D.q3 D.q3 D.q1 = refl
eightSiteFactorization D.q3 D.q3 D.q2 = refl
eightSiteFactorization D.q3 D.q3 D.q3 = refl

-- All 64 residue classes are discharged by closed integer computation.
exactIntensity : (h k l : D.Quarter) →
  norm2 (eightSiteAmplitude h k l) ≡ expectedIntensity h k l
exactIntensity D.q0 D.q0 D.q0 = refl
exactIntensity D.q0 D.q0 D.q1 = refl
exactIntensity D.q0 D.q0 D.q2 = refl
exactIntensity D.q0 D.q0 D.q3 = refl
exactIntensity D.q0 D.q1 D.q0 = refl
exactIntensity D.q0 D.q1 D.q1 = refl
exactIntensity D.q0 D.q1 D.q2 = refl
exactIntensity D.q0 D.q1 D.q3 = refl
exactIntensity D.q0 D.q2 D.q0 = refl
exactIntensity D.q0 D.q2 D.q1 = refl
exactIntensity D.q0 D.q2 D.q2 = refl
exactIntensity D.q0 D.q2 D.q3 = refl
exactIntensity D.q0 D.q3 D.q0 = refl
exactIntensity D.q0 D.q3 D.q1 = refl
exactIntensity D.q0 D.q3 D.q2 = refl
exactIntensity D.q0 D.q3 D.q3 = refl
exactIntensity D.q1 D.q0 D.q0 = refl
exactIntensity D.q1 D.q0 D.q1 = refl
exactIntensity D.q1 D.q0 D.q2 = refl
exactIntensity D.q1 D.q0 D.q3 = refl
exactIntensity D.q1 D.q1 D.q0 = refl
exactIntensity D.q1 D.q1 D.q1 = refl
exactIntensity D.q1 D.q1 D.q2 = refl
exactIntensity D.q1 D.q1 D.q3 = refl
exactIntensity D.q1 D.q2 D.q0 = refl
exactIntensity D.q1 D.q2 D.q1 = refl
exactIntensity D.q1 D.q2 D.q2 = refl
exactIntensity D.q1 D.q2 D.q3 = refl
exactIntensity D.q1 D.q3 D.q0 = refl
exactIntensity D.q1 D.q3 D.q1 = refl
exactIntensity D.q1 D.q3 D.q2 = refl
exactIntensity D.q1 D.q3 D.q3 = refl
exactIntensity D.q2 D.q0 D.q0 = refl
exactIntensity D.q2 D.q0 D.q1 = refl
exactIntensity D.q2 D.q0 D.q2 = refl
exactIntensity D.q2 D.q0 D.q3 = refl
exactIntensity D.q2 D.q1 D.q0 = refl
exactIntensity D.q2 D.q1 D.q1 = refl
exactIntensity D.q2 D.q1 D.q2 = refl
exactIntensity D.q2 D.q1 D.q3 = refl
exactIntensity D.q2 D.q2 D.q0 = refl
exactIntensity D.q2 D.q2 D.q1 = refl
exactIntensity D.q2 D.q2 D.q2 = refl
exactIntensity D.q2 D.q2 D.q3 = refl
exactIntensity D.q2 D.q3 D.q0 = refl
exactIntensity D.q2 D.q3 D.q1 = refl
exactIntensity D.q2 D.q3 D.q2 = refl
exactIntensity D.q2 D.q3 D.q3 = refl
exactIntensity D.q3 D.q0 D.q0 = refl
exactIntensity D.q3 D.q0 D.q1 = refl
exactIntensity D.q3 D.q0 D.q2 = refl
exactIntensity D.q3 D.q0 D.q3 = refl
exactIntensity D.q3 D.q1 D.q0 = refl
exactIntensity D.q3 D.q1 D.q1 = refl
exactIntensity D.q3 D.q1 D.q2 = refl
exactIntensity D.q3 D.q1 D.q3 = refl
exactIntensity D.q3 D.q2 D.q0 = refl
exactIntensity D.q3 D.q2 D.q1 = refl
exactIntensity D.q3 D.q2 D.q2 = refl
exactIntensity D.q3 D.q2 D.q3 = refl
exactIntensity D.q3 D.q3 D.q0 = refl
exactIntensity D.q3 D.q3 D.q1 = refl
exactIntensity D.q3 D.q3 D.q2 = refl
exactIntensity D.q3 D.q3 D.q3 = refl

reflection111 : norm2 (eightSiteAmplitude D.q1 D.q1 D.q1) ≡ + 32
reflection111 = refl
reflection222 : norm2 (eightSiteAmplitude D.q2 D.q2 D.q2) ≡ + 0
reflection222 = refl
reflection400 : norm2 (eightSiteAmplitude D.q0 D.q0 D.q0) ≡ + 64
reflection400 = refl

-- The source is ideal equal-scattering-length diamond structure.
-- Mixed occupancies / vacancies and element-dependent atomic form
-- factors need separate site-decorated scattering models.
