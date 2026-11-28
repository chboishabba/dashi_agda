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


-- Reverse equality-stratum charts. The split index is strictly interior,
-- so both sides of each split are positive; the double diagonal remains.
-- Proof fields are never used as coordinate identity.
splitPositive : (d t : Nat) → t < d → zero < d ∸ t
splitPositive zero t ()
splitPositive (suc d) zero h = s≤s z≤n
splitPositive (suc d) (suc t) (s≤s h) = splitPositive d t h

splitSum : (d t : Nat) → t < d → t + (d ∸ t) ≡ d
splitSum zero t ()
splitSum (suc d) zero h = refl
splitSum (suc d) (suc t) (s≤s h) = cong suc (splitSum d t h)

fromXY : ∀ {n} → F.PositiveFactorPair n → Nat → Quad
fromXY p t = quad t (F.divisor p ∸ t)
  (suc (F.predecessor p)) (suc (F.predecessor p))

fromXYPositive : ∀ {n} (p : F.PositiveFactorPair n) (t : Nat) →
  zero < t → t < F.divisor p → Positive (fromXY p t)
fromXYPositive p t ht hs = ht , splitPositive (F.divisor p) t hs ,
  s≤s z≤n , s≤s z≤n

fromXYGrade : ∀ {n} (p : F.PositiveFactorPair n) (t : Nat) →
  t < F.divisor p → grade (fromXY p t) ≡ n
fromXYGrade p t hs =
  trans (xyGrade (fromXY p t) refl)
    (trans (cong (λ d → d * suc (F.predecessor p)) (splitSum (F.divisor p) t hs))
      (trans (N.*-comm (F.divisor p) (suc (F.predecessor p))) (sym (F.productExact p))))

fromXYOmega : ∀ {n} (p : F.PositiveFactorPair n) (t : Nat) →
  zero < t → t < F.divisor p → fromXY p t ∈ G.omega n
fromXYOmega p t ht hs = G.omegaWrite (fromXYPositive p t ht hs) (fromXYGrade p t hs)

fromAB : ∀ {n} → F.PositiveFactorPair n → Nat → Quad
fromAB p t = quad (F.divisor p) (F.divisor p) t (suc (F.predecessor p) ∸ t)

fromABPositive : ∀ {n} (p : F.PositiveFactorPair n) (t : Nat) →
  zero < t → t < suc (F.predecessor p) → Positive (fromAB p t)
fromABPositive p t ht hs = F.divisorPositive p , F.divisorPositive p , ht ,
  splitPositive (suc (F.predecessor p)) t hs

fromABGrade : ∀ {n} (p : F.PositiveFactorPair n) (t : Nat) →
  t < suc (F.predecessor p) → grade (fromAB p t) ≡ n
fromABGrade p t hs =
  trans (abGrade (fromAB p t) refl)
    (trans (cong (λ k → k * F.divisor p) (splitSum (suc (F.predecessor p)) t hs))
      (sym (F.productExact p)))

fromABOmega : ∀ {n} (p : F.PositiveFactorPair n) (t : Nat) →
  zero < t → t < suc (F.predecessor p) → fromAB p t ∈ G.omega n
fromABOmega p t ht hs = G.omegaWrite (fromABPositive p t ht hs) (fromABGrade p t hs)

recoverXY : (q : Quad) → x q ≡ y q →
  (p : F.PositiveFactorPair (grade q)) →
  F.divisor p ≡ a q + b q → suc (F.predecessor p) ≡ x q →
  fromXY p (a q) ≡ q
recoverXY q e p d k = quadCoordinates refl
  (trans (cong (λ z → z ∸ a q) d) (xySplitComplement q)) k (trans k e)

recoverAB : (q : Quad) → a q ≡ b q →
  (p : F.PositiveFactorPair (grade q)) →
  F.divisor p ≡ a q → suc (F.predecessor p) ≡ x q + y q →
  fromAB p (x q) ≡ q
recoverAB q e p d k = quadCoordinates d (trans d e) refl
  (trans (cong (λ z → z ∸ x q) k) (abSplitComplement q))

-- Coordinate readbacks of the reverse charts, not proof-record equality.
xyReadDivisor : ∀ {n} (p : F.PositiveFactorPair n) (t : Nat) →
  t < F.divisor p → a (fromXY p t) + b (fromXY p t) ≡ F.divisor p
xyReadDivisor p t = splitSum (F.divisor p) t

abReadQuotient : ∀ {n} (p : F.PositiveFactorPair n) (t : Nat) →
  t < suc (F.predecessor p) → x (fromAB p t) + y (fromAB p t) ≡ suc (F.predecessor p)
abReadQuotient p t = splitSum (suc (F.predecessor p)) t
