module DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionRamanujanIntegerExact where

-- Source-written, uncompiled: original finite signed divisor identities.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Integer.Base using (ℤ; +_; _+_; _*_; -_)
import Data.Integer.Properties as Z
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionSignedBoundaryExact as B
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionClosedBoundaryExact as L
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionInteriorFoldExact as I
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionSigmaFoldExact as V
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearExact as S
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearPermutationExact as G
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as P
import DASHI.Mathematics.NumberTheory.FiniteFactorPairPowerReadoutExact as Read
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Pow
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as W
open V using (sigma; conv)

zpow : ℤ → Nat → ℤ
zpow x zero = + 1
zpow x (suc k) = x * zpow x k

powEmbed : (a k : Nat) → (+ Pow.powNat a k) ≡ zpow (+ a) k
powEmbed a zero = refl
powEmbed a (suc k) = trans (Z.pos-* a (Pow.powNat a k)) (cong ((+ a) *_) (powEmbed a k))

Terms : Set
Terms = List (ℤ × Nat)

lin : Terms → (Nat → ℤ) → ℤ
lin [] f = + 0
lin ((c , k) ∷ ts) f = c * f k + lin ts f

linFold : ∀ {A : Set} (ts : Terms) (f : A → Nat → ℤ) (xs : List A) →
  B.foldZ (λ x → lin ts (f x)) xs ≡ lin ts (λ k → B.foldZ (λ x → f x k) xs)
linFold [] f xs = V.foldZero xs
linFold ((c , k) ∷ ts) f xs =
  trans (I.foldAdd (λ x → c * f x k) (λ x → lin ts (f x)) xs)
    (trans (cong (_+ B.foldZ (λ x → lin ts (f x)) xs) (sym (L.scaleFold c (λ x → f x k) xs)))
      (cong (c * B.foldZ (λ x → f x k) xs +_) (linFold ts f xs)))

linCong : (ts : Terms) (f g : Nat → ℤ) →
  (∀ k → f k ≡ g k) → lin ts f ≡ lin ts g
linCong [] f g h = refl
linCong ((c , k) ∷ ts) f g h =
  trans (cong (λ v → c * v + lin ts f) (h k))
    (cong (c * g k +_) (linCong ts f g h))

factorPower : (k n : Nat) (pn : zero < n) →
  B.foldZ (λ p → zpow (+ P.divisor p) k) (P.positiveFactorPairs n pn) ≡ sigma k n
factorPower k n pn =
  let ps = P.positiveFactorPairs n pn
      f = λ p → Pow.powNat (P.divisor p) k
  in trans (B.foldCongOn (λ p → zpow (+ P.divisor p) k) (λ p → + f p) ps
       (λ {p} _ → sym (powEmbed (P.divisor p) k)))
       (trans (sym (V.embedFold f ps)) (cong +_ (Read.positivePowerReadout k n pn)))

factorGrade : ∀ {n} (p : P.PositiveFactorPair n) →
  (+ n) ≡ ((+ P.predecessor p) + (+ 1)) * (+ P.divisor p)
factorGrade p =
  trans (cong +_ (P.productExact p))
    (trans (Z.pos-* (suc (P.predecessor p)) (P.divisor p))
      (cong (_* (+ P.divisor p)) (sym (S.nextInteger (P.predecessor p)))))

netBoundary : (f : B.Weight) (h : B.ShearSymmetry f) (m : ℤ) (bd : ℤ → ℤ) →
  ((r : Nat) → S.scaledBoundaryPrefix f m (+ (suc r)) r ≡ bd (+ (suc r))) →
  (n : Nat) (pn : zero < suc n) → (ts : Terms) →
  ((p : P.PositiveFactorPair (suc n)) →
    bd (+ P.divisor p) ≡ (+ P.predecessor p) * (m * f (+ P.divisor p) (+ P.divisor p)) +
      lin ts (zpow (+ P.divisor p))) →
  m * B.foldZ (I.delta f) (G.omega (suc n)) ≡ lin ts (λ k → sigma k (suc n))
netBoundary f h m bd closed n pn ts point =
  let ps = P.positiveFactorPairs (suc n) pn
      ab = λ p → (+ P.predecessor p) * (m * f (+ P.divisor p) (+ P.divisor p))
      poly = λ p → lin ts (zpow (+ P.divisor p))
      a = m * B.foldZ (I.delta f) (G.omega (suc n))
      b = B.foldZ ab ps
      e = trans (L.scaledInterior f h m bd closed n pn)
        (trans (B.foldCongOn (λ p → bd (+ P.divisor p)) (λ p → ab p + poly p) ps
          (λ {p} _ → point p)) (I.foldAdd ab poly ps))
  in trans (Z.+-cancelˡ-≡ b (trans (Z.+-comm b a) e))
      (trans (linFold ts (λ p → zpow (+ P.divisor p)) ps)
        (linCong ts (λ k → B.foldZ (λ p → zpow (+ P.divisor p) k) ps)
          (λ k → sigma k (suc n)) (λ k → factorPower k (suc n) pn)))

Monomials : Set
Monomials = List (ℤ × (Nat × Nat))

poly2 : Monomials → (Nat → Nat → ℤ) → ℤ
poly2 [] f = + 0
poly2 ((c , (k , l)) ∷ ts) f = c * f k l + poly2 ts f

polyFold : (ts : Monomials) (n : Nat) →
  B.foldZ (λ q → poly2 ts (λ k l → V.weight k l q)) (G.omega n) ≡
  poly2 ts (λ k l → conv k l n)
polyFold [] n = V.foldZero (G.omega n)
polyFold ((c , (k , l)) ∷ ts) n =
  let o = G.omega n
      f = V.weight k l
      g = λ q → poly2 ts (λ k l → V.weight k l q)
  in trans (I.foldAdd (λ q → c * f q) g o)
      (trans (cong (_+ B.foldZ g o) (sym (L.scaleFold c f o)))
        (trans (cong (λ v → c * v + B.foldZ g o) (V.omegaPower k l n))
          (cong (c * conv k l n +_) (polyFold ts n))))

polyCong : (ts : Monomials) (f g : Nat → Nat → ℤ) →
  (∀ k l → f k l ≡ g k l) → poly2 ts f ≡ poly2 ts g
polyCong [] f g h = refl
polyCong ((c , (k , l)) ∷ ts) f g h =
  trans (cong (λ v → c * v + poly2 ts f) (h k l))
    (cong (c * g k l +_) (polyCong ts f g h))

deltaFrom : (g f d : ℤ) → g ≡ f + d → g + (- f) ≡ d
deltaFrom g f d h =
  trans (cong (_+ (- f)) h)
    (trans (Z.+-comm (f + d) (- f))
      (trans (sym (Z.+-assoc (- f) f d))
        (trans (cong (_+ d) (Z.+-inverseˡ f)) (Z.+-identityˡ d))))

scaledPoly : (f : B.Weight) (m : ℤ) (ts : Monomials) →
  ((q : S.Quad) → m * I.delta f q ≡ poly2 ts (λ k l → V.weight k l q)) →
  (n : Nat) → m * B.foldZ (I.delta f) (G.omega n) ≡ poly2 ts (λ k l → conv k l n)
scaledPoly f m ts point n =
  trans (L.scaleFold m (I.delta f) (G.omega n))
    (trans (B.foldCongOn (λ q → m * I.delta f q) (λ q → poly2 ts (λ k l → V.weight k l q))
      (G.omega n) (λ {q} _ → point q)) (polyFold ts n))

terms1 : ℤ → Terms
terms1 n = ((+ 5) , 3) ∷ (((+ 1) + ((- (+ 6)) * n)) , 1) ∷ []

monomials1 : Monomials
monomials1 = ((+ 12) , (1 , 1)) ∷ []

boundaryPoint1 : ∀ {n} (p : P.PositiveFactorPair n) →
  S.boundary1 (+ P.divisor p) ≡ (+ P.predecessor p) * ((+ 6) * S.weight1 (+ P.divisor p) (+ P.divisor p)) +
    lin (terms1 (+ n)) (zpow (+ P.divisor p))
boundaryPoint1 {n} p =
  let d = + P.divisor p
      k = + P.predecessor p
  in trans (solve 2 (λ d p → (((con (+ 5) :* ((d :* (d :* d)) :* con (+ 1))) :+ (con (- (+ 6)) :* ((d :* d) :* con (+ 1)))) :+ (con (+ 1) :* (d :* con (+ 1)))) := ((p :* (con (+ 6) :* (((d :* d) :+ (con (- (+ 1)) :* (d :* d))) :+ (d :* d)))) :+ ((con (+ 5) :* (d :* (d :* (d :* con (+ 1))))) :+ (((con (+ 1) :+ (con (- (+ 6)) :* ((p :+ con (+ 1)) :* d))) :* (d :* con (+ 1))) :+ con (+ 0))))) refl d k)
    (cong (λ v → k * ((+ 6) * S.weight1 d d) + lin (terms1 v) (zpow d)) (sym (factorGrade p)))

point1 : (q : S.Quad) → (+ 6) * I.delta S.weight1 q ≡ poly2 monomials1 (λ k l → V.weight k l q)
point1 q =
  let a = + S.a q
      b = + S.b q
      d = ((+ 2) * (zpow a 1 * zpow b 1))
  in trans (cong ((+ 6) *_) (deltaFrom (S.weight1 (a + b) b) (S.weight1 a b) d
       (trans (S.difference1 a b) (cong (S.weight1 a b +_) (solve 2 (λ a b → (con (+ 2) :* (a :* b)) := (con (+ 2) :* ((a :* con (+ 1)) :* (b :* con (+ 1))))) refl a b)))))
    (trans (solve 2 (λ a b → (con (+ 6) :* (con (+ 2) :* ((a :* con (+ 1)) :* (b :* con (+ 1))))) := ((con (+ 12) :* ((a :* con (+ 1)) :* (b :* con (+ 1)))) :+ con (+ 0))) refl a b)
      (polyCong monomials1 (λ k l → zpow a k * zpow b l) (λ k l → V.weight k l q)
        (λ k l → trans (cong (_* zpow b l) (sym (powEmbed (S.a q) k)))
          (cong ((+ Pow.powNat (S.a q) k) *_) (sym (powEmbed (S.b q) l))))))

identity1 : (n : Nat) (pn : zero < suc n) →
  poly2 monomials1 (λ k l → conv k l (suc n)) ≡ lin (terms1 (+ (suc n))) (λ k → sigma k (suc n))
identity1 n pn = trans (sym (scaledPoly S.weight1 (+ 6) monomials1 point1 (suc n)))
  (netBoundary S.weight1 S.weight1ShearSymmetry (+ 6) S.boundary1 S.boundaryClosed1 n pn (terms1 (+ (suc n))) boundaryPoint1)

terms2 : ℤ → Terms
terms2 n = ((+ 21) , 5) ∷ (((+ 10) + ((- (+ 30)) * n)) , 3) ∷ ((- (+ 1)) , 1) ∷ []

monomials2 : Monomials
monomials2 = ((+ 120) , (3 , 1)) ∷ ((+ 120) , (1 , 3)) ∷ []

boundaryPoint2 : ∀ {n} (p : P.PositiveFactorPair n) →
  S.boundary2 (+ P.divisor p) ≡ (+ P.predecessor p) * ((+ 30) * S.weight2 (+ P.divisor p) (+ P.divisor p)) +
    lin (terms2 (+ n)) (zpow (+ P.divisor p))
boundaryPoint2 {n} p =
  let d = + P.divisor p
      k = + P.predecessor p
  in trans (solve 2 (λ d p → ((((con (+ 21) :* ((d :* (d :* (d :* (d :* d)))) :* con (+ 1))) :+ (con (- (+ 30)) :* ((d :* (d :* (d :* d))) :* con (+ 1)))) :+ (con (+ 10) :* ((d :* (d :* d)) :* con (+ 1)))) :+ (con (- (+ 1)) :* (d :* con (+ 1)))) := ((p :* (con (+ 30) :* ((((d :* d) :+ (con (- (+ 1)) :* (d :* d))) :+ (d :* d)) :* (((d :* d) :+ (con (- (+ 1)) :* (d :* d))) :+ (d :* d))))) :+ ((con (+ 21) :* (d :* (d :* (d :* (d :* (d :* con (+ 1))))))) :+ (((con (+ 10) :+ (con (- (+ 30)) :* ((p :+ con (+ 1)) :* d))) :* (d :* (d :* (d :* con (+ 1))))) :+ ((con (- (+ 1)) :* (d :* con (+ 1))) :+ con (+ 0)))))) refl d k)
    (cong (λ v → k * ((+ 30) * S.weight2 d d) + lin (terms2 v) (zpow d)) (sym (factorGrade p)))

point2 : (q : S.Quad) → (+ 30) * I.delta S.weight2 q ≡ poly2 monomials2 (λ k l → V.weight k l q)
point2 q =
  let a = + S.a q
      b = + S.b q
      d = (((+ 4) * (zpow a 3 * zpow b 1)) + ((+ 4) * (zpow a 1 * zpow b 3)))
  in trans (cong ((+ 30) *_) (deltaFrom (S.weight2 (a + b) b) (S.weight2 a b) d
       (trans (S.difference2 a b) (cong (S.weight2 a b +_) (solve 2 (λ a b → ((con (+ 4) :* ((a :* (a :* a)) :* b)) :+ (con (+ 4) :* (a :* (b :* (b :* b))))) := ((con (+ 4) :* ((a :* (a :* (a :* con (+ 1)))) :* (b :* con (+ 1)))) :+ (con (+ 4) :* ((a :* con (+ 1)) :* (b :* (b :* (b :* con (+ 1)))))))) refl a b)))))
    (trans (solve 2 (λ a b → (con (+ 30) :* ((con (+ 4) :* ((a :* (a :* (a :* con (+ 1)))) :* (b :* con (+ 1)))) :+ (con (+ 4) :* ((a :* con (+ 1)) :* (b :* (b :* (b :* con (+ 1)))))))) := ((con (+ 120) :* ((a :* (a :* (a :* con (+ 1)))) :* (b :* con (+ 1)))) :+ ((con (+ 120) :* ((a :* con (+ 1)) :* (b :* (b :* (b :* con (+ 1)))))) :+ con (+ 0)))) refl a b)
      (polyCong monomials2 (λ k l → zpow a k * zpow b l) (λ k l → V.weight k l q)
        (λ k l → trans (cong (_* zpow b l) (sym (powEmbed (S.a q) k)))
          (cong ((+ Pow.powNat (S.a q) k) *_) (sym (powEmbed (S.b q) l))))))

identity2 : (n : Nat) (pn : zero < suc n) →
  poly2 monomials2 (λ k l → conv k l (suc n)) ≡ lin (terms2 (+ (suc n))) (λ k → sigma k (suc n))
identity2 n pn = trans (sym (scaledPoly S.weight2 (+ 30) monomials2 point2 (suc n)))
  (netBoundary S.weight2 S.weight2ShearSymmetry (+ 30) S.boundary2 S.boundaryClosed2 n pn (terms2 (+ (suc n))) boundaryPoint2)

terms3 : ℤ → Terms
terms3 n = ((+ 249) , 7) ∷ (((+ 210) + ((- (+ 420)) * n)) , 5) ∷ ((- (+ 49)) , 3) ∷ ((+ 10) , 1) ∷ []

monomials3 : Monomials
monomials3 = ((+ 2520) , (5 , 1)) ∷ ((+ 5880) , (3 , 3)) ∷ ((+ 2520) , (1 , 5)) ∷ []

boundaryPoint3 : ∀ {n} (p : P.PositiveFactorPair n) →
  S.boundary3 (+ P.divisor p) ≡ (+ P.predecessor p) * ((+ 420) * S.weight3 (+ P.divisor p) (+ P.divisor p)) +
    lin (terms3 (+ n)) (zpow (+ P.divisor p))
boundaryPoint3 {n} p =
  let d = + P.divisor p
      k = + P.predecessor p
  in trans (solve 2 (λ d p → (((((con (+ 249) :* ((d :* (d :* (d :* (d :* (d :* (d :* d)))))) :* con (+ 1))) :+ (con (- (+ 420)) :* ((d :* (d :* (d :* (d :* (d :* d))))) :* con (+ 1)))) :+ (con (+ 210) :* ((d :* (d :* (d :* (d :* d)))) :* con (+ 1)))) :+ (con (- (+ 49)) :* ((d :* (d :* d)) :* con (+ 1)))) :+ (con (+ 10) :* (d :* con (+ 1)))) := ((p :* (con (+ 420) :* ((((d :* d) :+ (con (- (+ 1)) :* (d :* d))) :+ (d :* d)) :* ((((d :* d) :+ (con (- (+ 1)) :* (d :* d))) :+ (d :* d)) :* (((d :* d) :+ (con (- (+ 1)) :* (d :* d))) :+ (d :* d)))))) :+ ((con (+ 249) :* (d :* (d :* (d :* (d :* (d :* (d :* (d :* con (+ 1))))))))) :+ (((con (+ 210) :+ (con (- (+ 420)) :* ((p :+ con (+ 1)) :* d))) :* (d :* (d :* (d :* (d :* (d :* con (+ 1))))))) :+ ((con (- (+ 49)) :* (d :* (d :* (d :* con (+ 1))))) :+ ((con (+ 10) :* (d :* con (+ 1))) :+ con (+ 0))))))) refl d k)
    (cong (λ v → k * ((+ 420) * S.weight3 d d) + lin (terms3 v) (zpow d)) (sym (factorGrade p)))

point3 : (q : S.Quad) → (+ 420) * I.delta S.weight3 q ≡ poly2 monomials3 (λ k l → V.weight k l q)
point3 q =
  let a = + S.a q
      b = + S.b q
      d = ((((+ 6) * (zpow a 5 * zpow b 1)) + ((+ 14) * (zpow a 3 * zpow b 3))) + ((+ 6) * (zpow a 1 * zpow b 5)))
  in trans (cong ((+ 420) *_) (deltaFrom (S.weight3 (a + b) b) (S.weight3 a b) d
       (trans (S.difference3 a b) (cong (S.weight3 a b +_) (solve 2 (λ a b → (((con (+ 6) :* ((a :* (a :* (a :* (a :* a)))) :* b)) :+ (con (+ 14) :* ((a :* (a :* a)) :* (b :* (b :* b))))) :+ (con (+ 6) :* (a :* (b :* (b :* (b :* (b :* b))))))) := (((con (+ 6) :* ((a :* (a :* (a :* (a :* (a :* con (+ 1)))))) :* (b :* con (+ 1)))) :+ (con (+ 14) :* ((a :* (a :* (a :* con (+ 1)))) :* (b :* (b :* (b :* con (+ 1))))))) :+ (con (+ 6) :* ((a :* con (+ 1)) :* (b :* (b :* (b :* (b :* (b :* con (+ 1)))))))))) refl a b)))))
    (trans (solve 2 (λ a b → (con (+ 420) :* (((con (+ 6) :* ((a :* (a :* (a :* (a :* (a :* con (+ 1)))))) :* (b :* con (+ 1)))) :+ (con (+ 14) :* ((a :* (a :* (a :* con (+ 1)))) :* (b :* (b :* (b :* con (+ 1))))))) :+ (con (+ 6) :* ((a :* con (+ 1)) :* (b :* (b :* (b :* (b :* (b :* con (+ 1)))))))))) := ((con (+ 2520) :* ((a :* (a :* (a :* (a :* (a :* con (+ 1)))))) :* (b :* con (+ 1)))) :+ ((con (+ 5880) :* ((a :* (a :* (a :* con (+ 1)))) :* (b :* (b :* (b :* con (+ 1)))))) :+ ((con (+ 2520) :* ((a :* con (+ 1)) :* (b :* (b :* (b :* (b :* (b :* con (+ 1)))))))) :+ con (+ 0))))) refl a b)
      (polyCong monomials3 (λ k l → zpow a k * zpow b l) (λ k l → V.weight k l q)
        (λ k l → trans (cong (_* zpow b l) (sym (powEmbed (S.a q) k)))
          (cong ((+ Pow.powNat (S.a q) k) *_) (sym (powEmbed (S.b q) l))))))

identity3 : (n : Nat) (pn : zero < suc n) →
  poly2 monomials3 (λ k l → conv k l (suc n)) ≡ lin (terms3 (+ (suc n))) (λ k → sigma k (suc n))
identity3 n pn = trans (sym (scaledPoly S.weight3 (+ 420) monomials3 point3 (suc n)))
  (netBoundary S.weight3 S.weight3ShearSymmetry (+ 420) S.boundary3 S.boundaryClosed3 n pn (terms3 (+ (suc n))) boundaryPoint3)

terms4 : ℤ → Terms
terms4 n = ((+ 1) , 7) ∷ ((- (+ 1)) , 3) ∷ []

monomials4 : Monomials
monomials4 = ((+ 120) , (3 , 3)) ∷ []

boundaryPoint4 : ∀ {n} (p : P.PositiveFactorPair n) →
  S.boundary4 (+ P.divisor p) ≡ (+ P.predecessor p) * ((+ 30) * S.weight4 (+ P.divisor p) (+ P.divisor p)) +
    lin (terms4 (+ n)) (zpow (+ P.divisor p))
boundaryPoint4 {n} p =
  let d = + P.divisor p
      k = + P.predecessor p
  in trans (solve 2 (λ d p → ((con (+ 1) :* ((d :* (d :* (d :* (d :* (d :* (d :* d)))))) :* con (+ 1))) :+ (con (- (+ 1)) :* ((d :* (d :* d)) :* con (+ 1)))) := ((p :* (con (+ 30) :* (((d :* d) :* (d :* d)) :* ((d :+ (con (- (+ 1)) :* d)) :* (d :+ (con (- (+ 1)) :* d)))))) :+ ((con (+ 1) :* (d :* (d :* (d :* (d :* (d :* (d :* (d :* con (+ 1))))))))) :+ ((con (- (+ 1)) :* (d :* (d :* (d :* con (+ 1))))) :+ con (+ 0))))) refl d k)
    (cong (λ v → k * ((+ 30) * S.weight4 d d) + lin (terms4 v) (zpow d)) (sym (factorGrade p)))

point4 : (q : S.Quad) → (+ 30) * I.delta S.weight4 q ≡ poly2 monomials4 (λ k l → V.weight k l q)
point4 q =
  let a = + S.a q
      b = + S.b q
      d = ((+ 4) * (zpow a 3 * zpow b 3))
  in trans (cong ((+ 30) *_) (deltaFrom (S.weight4 (a + b) b) (S.weight4 a b) d
       (trans (S.difference4 a b) (cong (S.weight4 a b +_) (solve 2 (λ a b → (con (+ 4) :* ((a :* (a :* a)) :* (b :* (b :* b)))) := (con (+ 4) :* ((a :* (a :* (a :* con (+ 1)))) :* (b :* (b :* (b :* con (+ 1))))))) refl a b)))))
    (trans (solve 2 (λ a b → (con (+ 30) :* (con (+ 4) :* ((a :* (a :* (a :* con (+ 1)))) :* (b :* (b :* (b :* con (+ 1))))))) := ((con (+ 120) :* ((a :* (a :* (a :* con (+ 1)))) :* (b :* (b :* (b :* con (+ 1)))))) :+ con (+ 0))) refl a b)
      (polyCong monomials4 (λ k l → zpow a k * zpow b l) (λ k l → V.weight k l q)
        (λ k l → trans (cong (_* zpow b l) (sym (powEmbed (S.a q) k)))
          (cong ((+ Pow.powNat (S.a q) k) *_) (sym (powEmbed (S.b q) l))))))

identity4 : (n : Nat) (pn : zero < suc n) →
  poly2 monomials4 (λ k l → conv k l (suc n)) ≡ lin (terms4 (+ (suc n))) (λ k → sigma k (suc n))
identity4 n pn = trans (sym (scaledPoly S.weight4 (+ 30) monomials4 point4 (suc n)))
  (netBoundary S.weight4 S.weight4ShearSymmetry (+ 30) S.boundary4 S.boundaryClosed4 n pn (terms4 (+ (suc n))) boundaryPoint4)
