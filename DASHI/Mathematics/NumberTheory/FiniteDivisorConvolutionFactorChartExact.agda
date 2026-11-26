module DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionFactorChartExact where

-- SOURCE-WRITTEN, UNCOMPILED. Exact forward/backward coordinate
-- attachments between the existing positive grade lattice and the
-- existing positive factor-pair scan. No new divisor enumeration and
-- no equality of proof fields.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; _<_; _∸_; s≤s; z≤n)
import Data.Nat.Properties as N
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as F
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearExact as Q
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearPermutationExact as G
open Q using (Quad; quad; a; b; x; y; grade; Positive)

productPositive : (d k : Nat) → zero < d → zero < k → zero < d * k
productPositive d k pd pk = N.*-mono-≤ pd pk

positiveSum : (d k : Nat) → zero < d → zero < d + k
positiveSum d k h = N.≤-trans h (N.m≤m+n d k)

productPair : (r d k : Nat) → (pr : zero < r) → zero < d →
  r ≡ suc k * d →
  Σ (F.PositiveFactorPair r) λ p →
    (p ∈ F.positiveFactorPairs r pr) × ((F.divisor p ≡ d) × (F.predecessor p ≡ k))
productPair r zero k pr () e
productPair r (suc d) k pr pd e =
  F.positiveFactorPairCoordinatesComplete r pr pd
    (subst (suc d ≤_) (sym e) (N.m≤n*m (suc d) (suc k))) e

-- Original grade is read as two positive products, both strict.
i j : Quad → Nat
i q = a q * x q
j q = b q * y q

iPositive : (q : Quad) → Positive q → zero < i q
iPositive q (pa , pb , px , py) = productPositive (a q) (x q) pa px

jPositive : (q : Quad) → Positive q → zero < j q
jPositive q (pa , pb , px , py) = productPositive (b q) (y q) pb py

iStrict : (q : Quad) → Positive q → i q < grade q
iStrict q h = N.m<m+n (i q) (jPositive q h)

jStrict : (q : Quad) → Positive q → j q < grade q
jStrict q h = N.m<n+m (j q) (iPositive q h)

complement : (q : Quad) → grade q ∸ i q ≡ j q
complement q = N.m+n∸m≡n (i q) (j q)

leftPair : (q : Quad) → (h : Positive q) →
  Σ (F.PositiveFactorPair (i q)) λ p →
    (p ∈ F.positiveFactorPairs (i q) (iPositive q h)) ×
    ((F.divisor p ≡ a q) × (suc (F.predecessor p) ≡ x q))
leftPair (quad a b zero y) (pa , pb , () , py)
leftPair (quad a b (suc k) y) h@(pa , pb , px , py) =
  let p , m , d , k′ = productPair (a * suc k) a k (iPositive (quad a b (suc k) y) h)
        pa (N.*-comm a (suc k))
  in p , m , d , cong suc k′

rightPair : (q : Quad) → (h : Positive q) →
  Σ (F.PositiveFactorPair (j q)) λ p →
    (p ∈ F.positiveFactorPairs (j q) (jPositive q h)) ×
    ((F.divisor p ≡ b q) × (suc (F.predecessor p) ≡ y q))
rightPair (quad a b x zero) (pa , pb , px , ())
rightPair (quad a b x (suc k)) h@(pa , pb , px , py) =
  let p , m , d , k′ = productPair (b * suc k) b k (jPositive (quad a b x (suc k)) h)
        pb (N.*-comm b (suc k))
  in p , m , d , cong suc k′

fromFactors : ∀ {u v} → F.PositiveFactorPair u → F.PositiveFactorPair v → Quad
fromFactors p t = quad (F.divisor p) (F.divisor t) (suc (F.predecessor p)) (suc (F.predecessor t))

fromFactorsPositive : ∀ {u v} (p : F.PositiveFactorPair u) (t : F.PositiveFactorPair v) →
  Positive (fromFactors p t)
fromFactorsPositive p t = F.divisorPositive p , F.divisorPositive t , s≤s z≤n , s≤s z≤n

fromFactorsGrade : ∀ {u v} (p : F.PositiveFactorPair u) (t : F.PositiveFactorPair v) →
  grade (fromFactors p t) ≡ u + v
fromFactorsGrade {u} {v} p t =
  trans (cong (λ m → m + F.divisor t * suc (F.predecessor t))
    (trans (N.*-comm (F.divisor p) (suc (F.predecessor p))) (sym (F.productExact p))))
    (cong (u +_) (trans (N.*-comm (F.divisor t) (suc (F.predecessor t))) (sym (F.productExact t))))

fromFactorsOmega : ∀ {u v} (p : F.PositiveFactorPair u) (t : F.PositiveFactorPair v) →
  fromFactors p t ∈ G.omega (u + v)
fromFactorsOmega p t = G.omegaWrite (fromFactorsPositive p t) (fromFactorsGrade p t)

quadCoordinates : ∀ {a b x y a′ b′ x′ y′} →
  a ≡ a′ → b ≡ b′ → x ≡ x′ → y ≡ y′ →
  quad a b x y ≡ quad a′ b′ x′ y′
quadCoordinates refl refl refl refl = refl

recoverQuad : (q : Quad) → (h : Positive q) →
  fromFactors (proj₁ (leftPair q h)) (proj₁ (rightPair q h)) ≡ q
recoverQuad q h =
  let _ , _ , da , dx = leftPair q h
      _ , _ , db , dy = rightPair q h
  in quadCoordinates da db dx dy

-- Equality x=y is the original divisor d=a+b and a strict split.
xyGrade : (q : Quad) → x q ≡ y q → grade q ≡ (a q + b q) * x q
xyGrade (quad a b x y) refl = sym (N.*-distribʳ-+ x a b)

xySplitStrict : (q : Quad) → Positive q → a q < a q + b q
xySplitStrict q (pa , pb , px , py) = N.m<m+n (a q) pb

xySplitComplement : (q : Quad) → (a q + b q) ∸ a q ≡ b q
xySplitComplement q = N.m+n∸m≡n (a q) (b q)

xyPair : (q : Quad) → (h : Positive q) → x q ≡ y q →
  (pr : zero < grade q) →
  Σ (F.PositiveFactorPair (grade q)) λ p →
    (p ∈ F.positiveFactorPairs (grade q) pr) ×
    ((F.divisor p ≡ a q + b q) × (suc (F.predecessor p) ≡ x q))
xyPair (quad a b zero y) (pa , pb , () , py) e pr
xyPair (quad a b (suc k) y) h@(pa , pb , px , py) e pr =
  let p , m , d , k′ = productPair (grade (quad a b (suc k) y)) (a + b) k pr
        (positiveSum a b pa)
        (trans (xyGrade (quad a b (suc k) y) e) (N.*-comm (a + b) (suc k)))
  in p , m , d , cong suc k′

-- Equality a=b is the original divisor a and strict split of x+y.
abGrade : (q : Quad) → a q ≡ b q → grade q ≡ (x q + y q) * a q
abGrade (quad a b x y) refl =
  trans (sym (N.*-distribˡ-+ a x y)) (N.*-comm a (x + y))

abSplitStrict : (q : Quad) → Positive q → x q < x q + y q
abSplitStrict q (pa , pb , px , py) = N.m<m+n (x q) py

abSplitComplement : (q : Quad) → (x q + y q) ∸ x q ≡ y q
abSplitComplement q = N.m+n∸m≡n (x q) (y q)

abPair : (q : Quad) → (h : Positive q) → a q ≡ b q →
  (pr : zero < grade q) →
  Σ (F.PositiveFactorPair (grade q)) λ p →
    (p ∈ F.positiveFactorPairs (grade q) pr) ×
    ((F.divisor p ≡ a q) × (suc (F.predecessor p) ≡ x q + y q))
abPair (quad a b x y) (pa , pb , px , py) e pr with x + y | abGrade (quad a b x y) e | positiveSum x y px
... | zero | gr | ()
... | suc k | gr | positive =
  let p , m , d , k′ = productPair (grade (quad a b x y)) a k pr pa gr
  in p , m , d , cong suc k′
