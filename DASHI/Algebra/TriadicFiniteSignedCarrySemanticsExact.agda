module DASHI.Algebra.TriadicFiniteSignedCarrySemanticsExact where

-- Exact integer excess of the ORIGINAL finite carry transducer.
-- The discarded carry is retained as a signed multiple of the modulus.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ; +_; _+_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Relation.Binary.PropositionalEquality.≡-Reasoning
import Data.Integer.Properties as ZP
import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope as E
import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteArithmetic as A
import DASHI.Algebra.TriadicFiniteSignedIntegerWeldExact as W
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as P

digit : E.Trit → ℤ
digit t = P.digitInteger (W.toTrit t)

modulus : Nat → ℤ
modulus zero = + 1
modulus (suc n) = (+ 3) * modulus n

-- A constructive certificate of congruence, not a Boolean check.
Congruent : Nat → ℤ → ℤ → Set
Congruent n x y = Σ ℤ (λ k → x ≡ y + modulus n * k)

pairValue : A.Pair E.Trit E.Trit → ℤ
pairValue (A._,_ d k) = digit d + (+ 3) * digit k

-- This checks the ACTUAL fullAdd, not a separately defined normalizer.
fullAddSound : ∀ c x y →
  (digit x + digit y) + digit c ≡ pairValue (A.fullAdd c x y)
fullAddSound E.neg E.neg E.neg = refl
fullAddSound E.neg E.neg E.zer = refl
fullAddSound E.neg E.neg E.pos = refl
fullAddSound E.neg E.zer E.neg = refl
fullAddSound E.neg E.zer E.zer = refl
fullAddSound E.neg E.zer E.pos = refl
fullAddSound E.neg E.pos E.neg = refl
fullAddSound E.neg E.pos E.zer = refl
fullAddSound E.neg E.pos E.pos = refl
fullAddSound E.zer E.neg E.neg = refl
fullAddSound E.zer E.neg E.zer = refl
fullAddSound E.zer E.neg E.pos = refl
fullAddSound E.zer E.zer E.neg = refl
fullAddSound E.zer E.zer E.zer = refl
fullAddSound E.zer E.zer E.pos = refl
fullAddSound E.zer E.pos E.neg = refl
fullAddSound E.zer E.pos E.zer = refl
fullAddSound E.zer E.pos E.pos = refl
fullAddSound E.pos E.neg E.neg = refl
fullAddSound E.pos E.neg E.zer = refl
fullAddSound E.pos E.neg E.pos = refl
fullAddSound E.pos E.zer E.neg = refl
fullAddSound E.pos E.zer E.zer = refl
fullAddSound E.pos E.zer E.pos = refl
fullAddSound E.pos E.pos E.neg = refl
fullAddSound E.pos E.pos E.zer = refl
fullAddSound E.pos E.pos E.pos = refl

-- The induction is independent of the local carry table.
composeCarry : ∀ (x y c d k u v w p q : ℤ) →
  (x + y) + c ≡ d + (+ 3) * k →
  (u + v) + k ≡ w + p * q →
  ((x + (+ 3) * u) + (y + (+ 3) * v)) + c
    ≡ (d + (+ 3) * w) + ((+ 3) * p) * q
composeCarry x y c d k u v w p q local tail =
  begin
    ((x + (+ 3) * u) + (y + (+ 3) * v)) + c
  ≡⟨ solve 5 (λ a b c′ u′ v′ →
      ((a :+ con (+ 3) :* u′) :+ (b :+ con (+ 3) :* v′)) :+ c′
      := ((a :+ b) :+ c′) :+ con (+ 3) :* (u′ :+ v′))
      refl x y c u v ⟩
    ((x + y) + c) + (+ 3) * (u + v)
  ≡⟨ cong (λ t → t + (+ 3) * (u + v)) local ⟩
    (d + (+ 3) * k) + (+ 3) * (u + v)
  ≡⟨ solve 4 (λ d′ k′ u′ v′ →
      (d′ :+ con (+ 3) :* k′) :+ con (+ 3) :* (u′ :+ v′)
      := d′ :+ con (+ 3) :* ((u′ :+ v′) :+ k′))
      refl d k u v ⟩
    d + (+ 3) * ((u + v) + k)
  ≡⟨ cong (λ t → d + (+ 3) * t) tail ⟩
    d + (+ 3) * (w + p * q)
  ≡⟨ solve 4 (λ d′ w′ p′ q′ →
      d′ :+ con (+ 3) :* (w′ :+ p′ :* q′)
      := (d′ :+ con (+ 3) :* w′) :+ (con (+ 3) :* p′) :* q′)
      refl d w p q ⟩
    (d + (+ 3) * w) + ((+ 3) * p) * q
  ∎

carrySound : ∀ {n} (c : E.Trit) (x y : Q.Residue3Pow n) →
  Congruent n ((W.signedValue x + W.signedValue y) + digit c)
    (W.signedValue (A.addWithCarry c x y))
carrySound c E.[] E.[] =
  digit c , solve 1 (λ t → (con (+ 0) :+ con (+ 0)) :+ t
    := con (+ 0) :+ con (+ 1) :* t) refl (digit c)
carrySound {suc n} c (x E.∷ xs) (y E.∷ ys)
  with A.fullAdd c x y | fullAddSound c x y
... | A._,_ d k | local with carrySound k xs ys
...   | q , tail
  rewrite W.signedCons x xs | W.signedCons y ys
        | W.signedCons d (A.addWithCarry k xs ys) =
  q , composeCarry (digit x) (digit y) (digit c) (digit d) (digit k)
        (W.signedValue xs) (W.signedValue ys)
        (W.signedValue (A.addWithCarry k xs ys))
        (modulus n) q local tail

addSound : ∀ {n} (x y : Q.Residue3Pow n) →
  Congruent n (W.signedValue x + W.signedValue y)
    (W.signedValue (A.addResidue x y))
addSound x y with carrySound E.zer x y
... | q , h = q , trans (sym (ZP.+-identityʳ (W.signedValue x + W.signedValue y))) h

-- Only these actual signed congruences, not the unsigned address labels,
-- may feed a ring hom into ZMod (3^n).
