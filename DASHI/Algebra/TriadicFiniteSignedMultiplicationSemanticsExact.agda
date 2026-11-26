module DASHI.Algebra.TriadicFiniteSignedMultiplicationSemanticsExact where

-- Exact integer witnesses for reduction, signed scale and Horner product.
-- Reuse the original prefix/evaluator and the carry congruence.
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
import DASHI.Algebra.TriadicFiniteMultiplicationCompatibleExact as M
import DASHI.Algebra.TriadicFiniteSignedIntegerWeldExact as W
open import DASHI.Algebra.TriadicFiniteSignedCarrySemanticsExact using
  (digit; modulus; Congruent; addSound)

zeroSound : ∀ n → W.signedValue (A.zeroResidue n) ≡ + 0
zeroSound zero = refl
zeroSound (suc n)
  rewrite W.signedCons E.zer (A.zeroResidue n) | zeroSound n = refl

digitNeg : ∀ t → digit (E.involution t) ≡ digit E.neg * digit t
digitNeg E.neg = refl
digitNeg E.zer = refl
digitNeg E.pos = refl

negSound : ∀ {n} (x : Q.Residue3Pow n) →
  W.signedValue (A.negateResidue x) ≡ digit E.neg * W.signedValue x
negSound E.[] = refl
negSound (t E.∷ ts)
  rewrite W.signedCons (E.involution t) (A.negateResidue ts)
        | W.signedCons t ts | digitNeg t | negSound ts =
  solve 3 (λ s d v →
    (s :* d) :+ con (+ 3) :* (s :* v)
      := s :* (d :+ con (+ 3) :* v))
    refl (digit E.neg) (digit t) (W.signedValue ts)

scaleSound : ∀ {n} (d : E.Trit) (x : Q.Residue3Pow n) →
  W.signedValue (M.scaleTrit d x) ≡ digit d * W.signedValue x
scaleSound E.neg x = negSound x
scaleSound {n} E.zer x =
  trans (zeroSound n) (sym (ZP.*-zeroˡ (W.signedValue x)))
scaleSound E.pos x = sym (ZP.*-identityˡ (W.signedValue x))

zeroPrepend : ∀ {n} (x : Q.Residue3Pow n) →
  W.signedValue (E.zer E.∷ x) ≡ (+ 3) * W.signedValue x
zeroPrepend x = trans (W.signedCons E.zer x) (ZP.+-identityˡ _)

dropSound : ∀ {n} (x : Q.Residue3Pow (suc n)) →
  Congruent n (W.signedValue x) (W.signedValue (Q.reduce x))
dropSound {zero} (t E.∷ E.[])
  rewrite W.signedCons t E.[] =
  digit t , solve 1 (λ a → a :+ con (+ 3) :* con (+ 0)
    := con (+ 0) :+ con (+ 1) :* a) refl (digit t)
dropSound {suc n} (t E.∷ ts) with dropSound {n} ts
... | k , h
  rewrite W.signedCons t ts | W.signedCons t (Q.reduce ts) =
  k , trans (cong (λ z → digit t + (+ 3) * z) h)
    (solve 4 (λ a v p k′ → a :+ con (+ 3) :* (v :+ p :* k′)
      := (a :+ con (+ 3) :* v) :+ (con (+ 3) :* p) :* k′)
      refl (digit t) (W.signedValue (Q.reduce ts)) (modulus n) k)

-- Horner product lifts all discarded multiples to the next depth.
composeMul : ∀ (a u y y0 r s o p k l m : ℤ) →
  y ≡ y0 + p * k →
  u * y0 ≡ r + p * l →
  s ≡ a * y →
  s + (+ 3) * r ≡ o + ((+ 3) * p) * m →
  (a + (+ 3) * u) * y ≡ o + ((+ 3) * p) * (m + (l + u * k))
composeMul a u y y0 r s o p k l m hy hr hs ho =
  begin
    (a + (+ 3) * u) * y
  ≡⟨ solve 3 (λ a′ u′ y′ →
      (a′ :+ con (+ 3) :* u′) :* y′
      := a′ :* y′ :+ con (+ 3) :* (u′ :* y′)) refl a u y ⟩
    a * y + (+ 3) * (u * y)
  ≡⟨ cong (λ z → z + (+ 3) * (u * y)) (sym hs) ⟩
    s + (+ 3) * (u * y)
  ≡⟨ cong (λ z → s + (+ 3) * (u * z)) hy ⟩
    s + (+ 3) * (u * (y0 + p * k))
  ≡⟨ solve 5 (λ s′ u′ y′ p′ k′ →
      s′ :+ con (+ 3) :* (u′ :* (y′ :+ p′ :* k′))
      := (s′ :+ con (+ 3) :* (u′ :* y′)) :+ (con (+ 3) :* p′) :* (u′ :* k′))
      refl s u y0 p k ⟩
    (s + (+ 3) * (u * y0)) + ((+ 3) * p) * (u * k)
  ≡⟨ cong (λ z → (s + (+ 3) * z) + ((+ 3) * p) * (u * k)) hr ⟩
    (s + (+ 3) * (r + p * l)) + ((+ 3) * p) * (u * k)
  ≡⟨ solve 6 (λ s′ r′ p′ l′ u′ k′ →
      (s′ :+ con (+ 3) :* (r′ :+ p′ :* l′)) :+ (con (+ 3) :* p′) :* (u′ :* k′)
      := (s′ :+ con (+ 3) :* r′) :+ (con (+ 3) :* p′) :* (l′ :+ u′ :* k′))
      refl s r p l u k ⟩
    (s + (+ 3) * r) + ((+ 3) * p) * (l + u * k)
  ≡⟨ cong (λ z → z + ((+ 3) * p) * (l + u * k)) ho ⟩
    (o + ((+ 3) * p) * m) + ((+ 3) * p) * (l + u * k)
  ≡⟨ solve 5 (λ o′ p′ m′ l′ t′ →
      (o′ :+ (con (+ 3) :* p′) :* m′) :+ (con (+ 3) :* p′) :* (l′ :+ t′)
      := o′ :+ (con (+ 3) :* p′) :* (m′ :+ (l′ :+ t′)))
      refl o p m l (u * k) ⟩
    o + ((+ 3) * p) * (m + (l + u * k))
  ∎

multiplySound : ∀ {n} (x y : Q.Residue3Pow n) →
  Congruent n (W.signedValue x * W.signedValue y)
    (W.signedValue (M.multiply x y))
multiplySound E.[] E.[] = (+ 0) , refl
multiplySound {suc n} (a E.∷ xs) (b E.∷ ys)
  with dropSound {n} (b E.∷ ys)
     | multiplySound xs (Q.reduce (b E.∷ ys))
     | addSound (M.scaleTrit a (b E.∷ ys))
         (E.zer E.∷ M.multiply xs (Q.reduce (b E.∷ ys)))
... | k , hy | l , hr | m , ho =
  (m + (l + W.signedValue xs * k)) ,
  trans (cong (λ z → z * W.signedValue (b E.∷ ys)) (W.signedCons a xs))
    (composeMul (digit a) (W.signedValue xs) (W.signedValue (b E.∷ ys))
      (W.signedValue (Q.reduce (b E.∷ ys)))
      (W.signedValue (M.multiply xs (Q.reduce (b E.∷ ys))))
      (W.signedValue (M.scaleTrit a (b E.∷ ys)))
      (W.signedValue (M.multiply (a E.∷ xs) (b E.∷ ys)))
      (modulus n) k l m hy hr (scaleSound a (b E.∷ ys))
      (trans (cong (λ z → W.signedValue (M.scaleTrit a (b E.∷ ys)) + z)
        (sym (zeroPrepend (M.multiply xs (Q.reduce (b E.∷ ys)))))) ho))

oneResidue : (n : Nat) → Q.Residue3Pow n
oneResidue zero = E.[]
oneResidue (suc n) = E.pos E.∷ A.zeroResidue n

oneSound : ∀ n → Congruent n (+ 1) (W.signedValue (oneResidue n))
oneSound zero = (+ 1) , refl
oneSound (suc n) rewrite W.signedCons E.pos (A.zeroResidue n) | zeroSound n =
  (+ 0) , sym (trans (cong ((+ 1) +_) (ZP.*-zeroʳ ((+ 3) * modulus n))) (ZP.+-identityʳ (+ 1)))

-- Congruences are source-written all-depth statements. Kernel acceptance,
-- modulus/cast bridge and residue isomorphism are still distinct.
