module DASHI.Moonshine.JInvariantThetaIntegralParityExact where

-- SOURCE-WRITTEN, kernel pending. Construct the parity witnesses used
-- by the existing affine Hadamard chart from arbitrary signed integers.
-- No modulus oracle, no assumption about a source norm-shell count.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_; -_)
import Data.Integer.Properties as ZP
import Data.Nat.Properties as NP
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import DASHI.Moonshine.JInvariantThetaHadamardIntegralChartExact as H

Even : ℤ → Set
Even z = Σ ℤ (λ k → z ≡ (+ 2) * k)

Odd : ℤ → Set
Odd z = Σ ℤ (λ k → z ≡ (+ 2) * k + (+ 1))

Parity : ℤ → Set
Parity z = Even z ⊎ Odd z

step : ∀ z → Parity z → Parity (z + (+ 1))
step z (inj₁ (k , h)) =
  inj₂ (k , cong (_+ (+ 1)) h)
step z (inj₂ (k , h)) =
  inj₁ (k + (+ 1) , trans (cong (_+ (+ 1)) h)
    (solve 1 (λ k → (con (+ 2) :* k :+ con (+ 1)) :+ con (+ 1)
      := con (+ 2) :* (k :+ con (+ 1))) refl k))

negateParity : ∀ z → Parity z → Parity (- z)
negateParity z (inj₁ (k , h)) =
  inj₁ ((+ 0) - k , trans (cong -_ h)
    (solve 1 (λ k → con (+ 0) :- (con (+ 2) :* k)
      := con (+ 2) :* (con (+ 0) :- k)) refl k))
negateParity z (inj₂ (k , h)) =
  inj₂ ((+ 0) - k - (+ 1) , trans (cong -_ h)
    (solve 1 (λ k → con (+ 0) :- (con (+ 2) :* k :+ con (+ 1))
      := con (+ 2) :* ((con (+ 0) :- k) :- con (+ 1)) :+ con (+ 1))
      refl k))

natParity : ∀ n → Parity (+ n)
natParity zero = inj₁ ((+ 0) , refl)
natParity (suc n) = subst Parity (cong +_ (NP.+-comm n 1))
  (step (+ n) (natParity n))

parity : ∀ z → Parity z
parity (+ n) = natParity n
parity -[1+ n ] = negateParity (+ suc n) (natParity (suc n))

-- x²-x is even on both explicit parity sheets, so the square norm and
-- the coordinate sum always have the same parity.
squareDifference : ∀ z → Even (z * z - z)
squareDifference z with parity z
... | inj₁ (k , h) =
  ((+ 2) * k * k - k) ,
  trans (cong (λ x → x * x - x) h)
    (solve 1 (λ k → (con (+ 2) :* k) :* (con (+ 2) :* k) :- (con (+ 2) :* k)
      := con (+ 2) :* (con (+ 2) :* k :* k :- k)) refl k)
... | inj₂ (k , h) =
  ((+ 2) * k * k + k) ,
  trans (cong (λ x → x * x - x) h)
    (solve 1 (λ k → (con (+ 2) :* k :+ con (+ 1)) :* (con (+ 2) :* k :+ con (+ 1))
      :- (con (+ 2) :* k :+ con (+ 1))
      := con (+ 2) :* (con (+ 2) :* k :* k :+ k)) refl k)

addEven : ∀ x y → Even x → Even y → Even (x + y)
addEven x y (k , h) (l , j) =
  (k + l) , trans (cong (_+ y) h)
    (trans (cong (((+ 2) * k) +_) j)
      (solve 2 (λ k l → con (+ 2) :* k :+ con (+ 2) :* l
        := con (+ 2) :* (k :+ l)) refl k l))

normTotalDifference : ∀ x → Even (H.normSq x - H.total x)
normTotalDifference (H.quad a b c d) =
  let x = a * a - a
      y = b * b - b
      z = c * c - c
      w = d * d - d
      h = addEven ((x + y) + z) w
        (addEven (x + y) z (addEven x y (squareDifference a) (squareDifference b))
          (squareDifference c)) (squareDifference d)
  in subst Even
    (solve 4 (λ a b c d →
      (((a :* a :- a) :+ (b :* b :- b)) :+ (c :* c :- c)) :+ (d :* d :- d)
      := (a :* a :+ b :* b :+ c :* c :+ d :* d) :- (a :+ b :+ c :+ d))
      refl a b c d) h

totalOddFromNormOdd : ∀ x → Odd (H.normSq x) → Odd (H.total x)
totalOddFromNormOdd x (k , hn) with normTotalDifference x
... | l , hd =
  (k - l) ,
  trans (solve 2 (λ n s → s := n :- (n :- s)) refl (H.normSq x) (H.total x))
    (trans (cong (_- (H.normSq x - H.total x)) hn)
      (trans (cong (((+ 2) * k + (+ 1)) -_) hd)
        (solve 2 (λ k l → con (+ 2) :* k :+ con (+ 1) :- con (+ 2) :* l
          := con (+ 2) :* (k :- l) :+ con (+ 1)) refl k l)))

normOddFromTotalOdd : ∀ x → Odd (H.total x) → Odd (H.normSq x)
normOddFromTotalOdd x (k , hs) with normTotalDifference x
... | l , hd =
  (k + l) ,
  trans (solve 2 (λ n s → n := s :+ (n :- s)) refl (H.normSq x) (H.total x))
    (trans (cong (_+ (H.normSq x - H.total x)) hs)
      (trans (cong (((+ 2) * k + (+ 1)) +_) hd)
        (solve 2 (λ k l → con (+ 2) :* k :+ con (+ 1) :+ con (+ 2) :* l
          := con (+ 2) :* (k :+ l) :+ con (+ 1)) refl k l)))

-- Odd coordinate labels are retained; the total is divisible by two,
-- and the parity of its half selects exactly one of the two mod-4 charts.
FourOdd : H.Quad → Set
FourOdd x = Odd (H.a x) × Odd (H.b x) × Odd (H.c x) × Odd (H.d x)

halfTotal : ∀ x → FourOdd x → Even (H.total x)
halfTotal (H.quad a b c d) ((u , ha) , (v , hb) , (w , hc) , (r , hd)) =
  (u + v + w + r + (+ 2)) ,
  trans (cong (λ z → ((z + b) + c) + d) ha)
    (trans (cong (λ z → (((+ 2) * u + (+ 1)) + z + c) + d) hb)
      (trans (cong (λ z → (((+ 2) * u + (+ 1)) + ((+ 2) * v + (+ 1)) + z) + d) hc)
        (trans (cong (λ z → (((+ 2) * u + (+ 1)) + ((+ 2) * v + (+ 1)) + ((+ 2) * w + (+ 1))) + z) hd)
          (solve 4 (λ u v w r →
            (con (+ 2) :* u :+ con (+ 1)) :+ (con (+ 2) :* v :+ con (+ 1)) :+
              (con (+ 2) :* w :+ con (+ 1)) :+ (con (+ 2) :* r :+ con (+ 1))
            := con (+ 2) :* (u :+ v :+ w :+ r :+ con (+ 2))) refl u v w r))))

data HalfChart (x : H.Quad) : Set where
  sheet0 : (q : H.Quad) → H.halfEven q ≡ x → HalfChart x
  sheet2 : (q : H.Quad) → H.halfOdd q ≡ x → HalfChart x

halfChart : ∀ x → FourOdd x → HalfChart x
halfChart x odds@((u , ha) , (v , hb) , (w , hc) , (r , hd))
  with halfTotal x odds
... | k , ht with parity k
...   | inj₁ (j , hj) =
  sheet0 (H.quad j u v w)
    (H.halfEvenChartRead x j u v w
      (trans ht (trans (cong ((+ 2) *_) hj)
        (solve 1 (λ j → con (+ 2) :* (con (+ 2) :* j) := con (+ 4) :* j) refl j)))
      ha hb hc)
...   | inj₂ (j , hj) =
  sheet2 (H.quad j u v w)
    (H.halfOddChartRead x j u v w
      (trans ht (trans (cong ((+ 2) *_) hj)
        (solve 1 (λ j → con (+ 2) :* (con (+ 2) :* j :+ con (+ 1))
          := con (+ 4) :* j :+ con (+ 2)) refl j)))
      ha hb hc)


-- Exclusivity and uniqueness of the affine parity witness.
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Nat.Base using (_≤_)

plusInject : ∀ {m n : Nat} → (+ m) ≡ (+ n) → m ≡ n
plusInject refl = refl

doubleNotOne : ∀ z → (+ 2) * z ≢ (+ 1)
doubleNotOne (+ zero) ()
doubleNotOne (+ suc n) h =
  NP.1+n≰n (subst (2 ≤_) (plusInject h) (NP.m≤m*n 2 (suc n)))
doubleNotOne -[1+ n ] ()

evenNotOdd : ∀ z → Even z → Odd z → ⊥
evenNotOdd z (k , he) (l , ho) = doubleNotOne (k - l)
  (trans (solve 2 (λ k l → con (+ 2) :* (k :- l)
    := con (+ 2) :* k :- con (+ 2) :* l) refl k l)
    (trans (cong (_- ((+ 2) * l)) (trans (sym he) ho))
      (solve 1 (λ l → con (+ 2) :* l :+ con (+ 1) :- con (+ 2) :* l
        := con (+ 1)) refl l)))

cancelScale : ∀ (c : Nat) x y → (+ suc c) * x ≡ (+ suc c) * y → x ≡ y
cancelScale c x y h = ZP.*-cancelʳ-≡ x y (+ suc c)
  (trans (ZP.*-comm x (+ suc c)) (trans h (ZP.*-comm (+ suc c) y)))

oddWitnessUnique : ∀ k l → (+ 2) * k + (+ 1) ≡ (+ 2) * l + (+ 1) → k ≡ l
oddWitnessUnique k l h = cancelScale 1 k l
  (trans (solve 1 (λ k → con (+ 2) :* k := con (+ 2) :* k :+ con (+ 1) :- con (+ 1)) refl k)
    (trans (cong (_- (+ 1)) h)
      (solve 1 (λ l → con (+ 2) :* l :+ con (+ 1) :- con (+ 1) := con (+ 2) :* l) refl l)))

oddParam : ℤ → ℤ
oddParam z with parity z
... | inj₁ _ = + 0
... | inj₂ (k , _) = k

oddParamRead : ∀ z → Odd z → (+ 2) * oddParam z + (+ 1) ≡ z
oddParamRead z odd with parity z
... | inj₁ even = ⊥-elim (evenNotOdd z even odd)
... | inj₂ (k , e) = sym e

oddParamExact : ∀ k → oddParam ((+ 2) * k + (+ 1)) ≡ k
oddParamExact k = oddWitnessUnique _ k
  (oddParamRead ((+ 2) * k + (+ 1)) (k , refl))

-- The sign history is exactly the parity of the degree, including zero.
import DASHI.Moonshine.JInvariantThetaLegendreSignedGeometryExact as T

signByParity : ∀ n →
  (Even (+ n) × (T.sign n ≡ + 1)) ⊎
  (Odd (+ n) × (T.sign n ≡ -[1+ 0 ]))
signByParity zero = inj₁ (((+ 0) , refl) , refl)
signByParity (suc n) with signByParity n
... | inj₁ ((k , h) , hs) = inj₂
  ((k , trans (sym (cong +_ (NP.+-comm n 1))) (cong (_+ (+ 1)) h)) , cong -_ hs)
... | inj₂ ((k , h) , hs) = inj₁
  ((k + (+ 1) ,
    trans (sym (cong +_ (NP.+-comm n 1)))
      (trans (cong (_+ (+ 1)) h)
        (solve 1 (λ k → con (+ 2) :* k :+ con (+ 1) :+ con (+ 1)
          := con (+ 2) :* (k :+ con (+ 1))) refl k))) , cong -_ hs)
