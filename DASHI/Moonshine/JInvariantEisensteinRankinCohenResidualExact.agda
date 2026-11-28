module DASHI.Moonshine.JInvariantEisensteinRankinCohenResidualExact where

-- Source-written integer polynomial identities. The same identities
-- hold over the actual complex field by ring interpretation; that
-- interpretation and modular cusp-form packaging are separate welds.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -_; _+_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver

-- x=E4, y=E6, u=3 DE4, v=2 DE6, e=E2.
-- d is the unnormalised discriminant; no divisions.
disc : ℤ → ℤ → ℤ
disc x y = x * x * x + (- (+ 1)) * (y * y)

bracket : ℤ → ℤ → ℤ → ℤ → ℤ
bracket x y u v = y * u + (- (+ 1)) * (x * v)

discDerivative : ℤ → ℤ → ℤ → ℤ → ℤ
discDerivative x y u v = x * x * u + (- (+ 1)) * (y * v)

-- Two residuals retain their signs rather than identifying zero
-- corrected bracket with zero source derivative.
rDisc : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
rDisc x y u v e = discDerivative x y u v + (- (+ 1)) * (e * disc x y)
rBracket : ℤ → ℤ → ℤ → ℤ → ℤ
rBracket x y u v = bracket x y u v + (- (+ 1)) * disc x y

r4 : ℤ → ℤ → ℤ → ℤ → ℤ
r4 x y u e = u + (- (+ 1)) * (e * x) + y
r6 : ℤ → ℤ → ℤ → ℤ → ℤ
r6 x y v e = v + (- (+ 1)) * (e * y) + x * x

-- Adjugate of the original two-coordinate system. Its determinant is
-- minus the original discriminant; the kernel is zero only off Delta=0.
recoverE4 : (x y u v e : ℤ) →
  x * rDisc x y u v e + (- (+ 1)) * (y * rBracket x y u v)
    ≡ disc x y * r4 x y u e
recoverE4 x y u v e =
  solve 5
    (λ x y u v e →
      let d = x :* x :* x :+ con (- (+ 1)) :* (y :* y)
          p = x :* x :* u :+ con (- (+ 1)) :* (y :* v)
            :+ con (- (+ 1)) :* (e :* d)
          q = y :* u :+ con (- (+ 1)) :* (x :* v) :+ con (- (+ 1)) :* d
      in x :* p :+ con (- (+ 1)) :* (y :* q)
        := d :* (u :+ con (- (+ 1)) :* (e :* x) :+ y))
    refl x y u v e

recoverE6 : (x y u v e : ℤ) →
  y * rDisc x y u v e + (- (+ 1)) * (x * x * rBracket x y u v)
    ≡ disc x y * r6 x y v e
recoverE6 x y u v e =
  solve 5
    (λ x y u v e →
      let d = x :* x :* x :+ con (- (+ 1)) :* (y :* y)
          p = x :* x :* u :+ con (- (+ 1)) :* (y :* v)
            :+ con (- (+ 1)) :* (e :* d)
          q = y :* u :+ con (- (+ 1)) :* (x :* v) :+ con (- (+ 1)) :* d
      in y :* p :+ con (- (+ 1)) :* (x :* x :* q)
        := d :* (v :+ con (- (+ 1)) :* (e :* y) :+ x :* x))
    refl x y u v e

-- Under modular transport, u and v have the same signed anomaly
-- 12 a times x,y respectively after the relevant weight is stripped.
bracketAnomalyCancels : (x y u v a : ℤ) →
  bracket x y (u + (+ 12) * a * x) (v + (+ 12) * a * y)
    ≡ bracket x y u v
bracketAnomalyCancels x y u v a =
  solve 5
    (λ x y u v a →
      y :* (u :+ con (+ 12) :* a :* x)
      :+ con (- (+ 1)) :* (x :* (v :+ con (+ 12) :* a :* y))
      := y :* u :+ con (- (+ 1)) :* (x :* v))
    refl x y u v a

firstFourierCoefficient : (+ 3) * (+ 240) + (- (+ 2)) * (- (+ 504)) ≡ + 1728
firstFourierCoefficient = refl
