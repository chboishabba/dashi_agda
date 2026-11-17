module DASHI.Physics.Motors.SmithFilsingerLocalCayleyMidpointExact where

-- Actual rational two-coordinate Cayley midpoint equations.
-- Reuses original CertifiedCayley, its two output functions, and its
-- source-aware dynamic reach owner. No fresh Green/signal operator.
--
-- A = [[0,a],[b,0]] and p=h*a/2, r=h*b/2.
-- For (u,v)=sameCayley(x,y), prove
--     u - p*v = x + p*y
--     v - r*u = y + r*x
-- using the SAME inverse-denominator certificate, not a stipulated
-- matrix equation. This is the original implicit-midpoint system.
--
-- Actual 3D Maxwell material/time calibration and D1 kernel are OPEN.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)
import Data.Rational.Tactic.RingSolver as ℚRing
import DASHI.Physics.Motors.SmithFilsingerLocalCayleyZeroWeldExact as Cayley

-- Proof-carrying half-step coefficients, never guessed from an
-- arbitrary pair of untyped field values. Each equality constrains
-- exactly the existing source-owned Cayley coefficients.
record CertifiedHalfStep : Set where
  field
    cayley : Cayley.CertifiedCayley
    p r : ℚ
    firstDoubled :
      p + p ≡ Cayley.step cayley * Cayley.firstCoupling cayley
    secondDoubled :
      r + r ≡ Cayley.step cayley * Cayley.secondCoupling cayley
    productIsQuarter :
      p * r ≡ Cayley.quarter cayley *
        (Cayley.step cayley * Cayley.step cayley) *
        (Cayley.firstCoupling cayley * Cayley.secondCoupling cayley)

open CertifiedHalfStep

-- Normal form convenient for polynomial ring reasoning. It is the
-- EXACT existing original Cayley map, not a second simulator.
reducedFirst : CertifiedHalfStep → ℚ → ℚ → ℚ
reducedFirst d x y =
  Cayley.inverseDenominator (cayley d) *
    (((1ℚ + p d * r d) * x) + ((p d + p d) * y))

reducedSecond : CertifiedHalfStep → ℚ → ℚ → ℚ
reducedSecond d x y =
  Cayley.inverseDenominator (cayley d) *
    (((r d + r d) * x) + ((1ℚ + p d * r d) * y))

-- Rewriting the certified double-half and product equalities makes
-- the normal form definitionally the same as the old actual formulas.
sameFirstIsReduced :
  (d : CertifiedHalfStep) (x y : ℚ) →
  reducedFirst d x y ≡ Cayley.sameCayleyFirst (cayley d) x y
sameFirstIsReduced d x y
  rewrite firstDoubled d | productIsQuarter d = refl

sameSecondIsReduced :
  (d : CertifiedHalfStep) (x y : ℚ) →
  reducedSecond d x y ≡ Cayley.sameCayleySecond (cayley d) x y
sameSecondIsReduced d x y
  rewrite secondDoubled d | productIsQuarter d = refl

-- Critical: inverseLaw of the original CertifiedCayley is the
-- denominator law for p*r, not a second unverified assumption.
halfStepInverseLaw :
  (d : CertifiedHalfStep) →
  (1ℚ - p d * r d) *
    Cayley.inverseDenominator (cayley d) ≡ 1ℚ
halfStepInverseLaw d rewrite productIsQuarter d =
  Cayley.inverseLaw (cayley d)

-- First polynomial identity BEFORE using invertibility:
-- (reducedFirst - p*reducedSecond)
--    = ((1-p*r)*q)*(x+p*y).
-- It is valid in any commutative ring, not merely for test samples.
firstMidpointPolynomial :
  (d : CertifiedHalfStep) (x y : ℚ) →
  reducedFirst d x y - p d * reducedSecond d x y
    ≡ ((1ℚ - p d * r d) *
         Cayley.inverseDenominator (cayley d)) *
        (x + p d * y)
firstMidpointPolynomial d x y =
  ℚRing.solve-∀ (p d) (r d)
    (Cayley.inverseDenominator (cayley d)) x y

secondMidpointPolynomial :
  (d : CertifiedHalfStep) (x y : ℚ) →
  reducedSecond d x y - r d * reducedFirst d x y
    ≡ ((1ℚ - p d * r d) *
         Cayley.inverseDenominator (cayley d)) *
        (y + r d * x)
secondMidpointPolynomial d x y =
  ℚRing.solve-∀ (p d) (r d)
    (Cayley.inverseDenominator (cayley d)) x y

firstReducedMidpoint :
  (d : CertifiedHalfStep) (x y : ℚ) →
  reducedFirst d x y - p d * reducedSecond d x y
    ≡ x + p d * y
firstReducedMidpoint d x y =
  trans (firstMidpointPolynomial d x y)
    (trans
      (cong (λ factor → factor * (x + p d * y))
        (halfStepInverseLaw d))
      (ℚRing.solve-∀ (p d) x y))

secondReducedMidpoint :
  (d : CertifiedHalfStep) (x y : ℚ) →
  reducedSecond d x y - r d * reducedFirst d x y
    ≡ y + r d * x
secondReducedMidpoint d x y =
  trans (secondMidpointPolynomial d x y)
    (trans
      (cong (λ factor → factor * (y + r d * x))
        (halfStepInverseLaw d))
      (ℚRing.solve-∀ (r d) x y))

-- THE ORIGINAL 2x2 COEFFICIENTS satisfy BOTH implicit midpoint
-- equations. No direct invocation of a hypothetical Maxwell result.
sameCayleyFirstMidpoint :
  (d : CertifiedHalfStep) (x y : ℚ) →
  Cayley.sameCayleyFirst (cayley d) x y
    - p d * Cayley.sameCayleySecond (cayley d) x y
      ≡ x + p d * y
sameCayleyFirstMidpoint d x y =
  trans
    (cong₂ _-_
      (symFirst d x y)
      (cong (λ v → p d * v) (symSecond d x y)))
    (firstReducedMidpoint d x y)
  where
    symFirst : (d : CertifiedHalfStep) (x y : ℚ) →
      Cayley.sameCayleyFirst (cayley d) x y ≡ reducedFirst d x y
    symFirst d x y = sym (sameFirstIsReduced d x y)
    symSecond : (d : CertifiedHalfStep) (x y : ℚ) →
      Cayley.sameCayleySecond (cayley d) x y ≡ reducedSecond d x y
    symSecond d x y = sym (sameSecondIsReduced d x y)

sameCayleySecondMidpoint :
  (d : CertifiedHalfStep) (x y : ℚ) →
  Cayley.sameCayleySecond (cayley d) x y
    - r d * Cayley.sameCayleyFirst (cayley d) x y
      ≡ y + r d * x
sameCayleySecondMidpoint d x y =
  trans
    (cong₂ _-_
      (sym (sameSecondIsReduced d x y))
      (cong (λ u → r d * u) (sym (sameFirstIsReduced d x y))))
    (secondReducedMidpoint d x y)
