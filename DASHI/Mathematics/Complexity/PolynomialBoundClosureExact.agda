module DASHI.Mathematics.Complexity.PolynomialBoundClosureExact where

------------------------------------------------------------------------
-- CLOSURE LAWS FOR THE REPOSITORY'S NATIVE PolynomialBound
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Properties as NatP
  using (*-assoc; *-comm; *-identityˡ; *-identityʳ; *-mono-≤; ≤-refl)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Core.EfficientRecoverableQuotientExact as ERQ

powAdd :
  ∀ base left right →
  ERQ.pow base (left + right)
  ≡ ERQ.pow base left * ERQ.pow base right
powAdd base zero right =
  sym (NatP.*-identityˡ (ERQ.pow base right))
powAdd base (suc left) right =
  trans
    (cong
      (λ value → base * value)
      (powAdd base left right))
    (sym
      (NatP.*-assoc
        base
        (ERQ.pow base left)
        (ERQ.pow base right)))

fourFactorExchange :
  ∀ a b c d →
  (a * b) * (c * d)
  ≡ (a * c) * (b * d)
fourFactorExchange a b c d =
  trans
    (NatP.*-assoc a b (c * d))
    (trans
      (cong
        (λ value → a * value)
        (trans
          (sym (NatP.*-assoc b c d))
          (trans
            (cong
              (λ value → value * d)
              (NatP.*-comm b c))
            (NatP.*-assoc c b d))))
      (sym
        (NatP.*-assoc
          a c (b * d))))

productPolynomialBound :
  ∀ {first second : Nat → Nat} →
  ERQ.PolynomialBound first →
  ERQ.PolynomialBound second →
  ERQ.PolynomialBound (λ n → first n * second n)
productPolynomialBound {first} {second} firstBound secondBound =
  ERQ.polynomialBound
    (ERQ.coefficient firstBound * ERQ.coefficient secondBound)
    (ERQ.exponent firstBound + ERQ.exponent secondBound)
    boundedProduct
  where
    boundedProduct :
      ∀ n →
      first n * second n
      ≤
      (ERQ.coefficient firstBound * ERQ.coefficient secondBound)
      * ERQ.pow
          (suc n)
          (ERQ.exponent firstBound + ERQ.exponent secondBound)
    boundedProduct n =
      subst
        (λ upper → first n * second n ≤ upper)
        exactUpper
        (NatP.*-mono-≤
          (ERQ.bounded firstBound n)
          (ERQ.bounded secondBound n))
      where
        exactUpper :
          (ERQ.coefficient firstBound
            * ERQ.pow (suc n) (ERQ.exponent firstBound))
          *
          (ERQ.coefficient secondBound
            * ERQ.pow (suc n) (ERQ.exponent secondBound))
          ≡
          (ERQ.coefficient firstBound * ERQ.coefficient secondBound)
          * ERQ.pow
              (suc n)
              (ERQ.exponent firstBound + ERQ.exponent secondBound)
        exactUpper =
          trans
            (fourFactorExchange
              (ERQ.coefficient firstBound)
              (ERQ.pow (suc n) (ERQ.exponent firstBound))
              (ERQ.coefficient secondBound)
              (ERQ.pow (suc n) (ERQ.exponent secondBound)))
            (cong
              (λ power →
                (ERQ.coefficient firstBound
                  * ERQ.coefficient secondBound)
                * power)
              (sym
                (powAdd
                  (suc n)
                  (ERQ.exponent firstBound)
                  (ERQ.exponent secondBound))))

constantMultiplePolynomialBound :
  ∀ constant {cost : Nat → Nat} →
  ERQ.PolynomialBound cost →
  ERQ.PolynomialBound (λ n → constant * cost n)
constantMultiplePolynomialBound constant {cost} bound =
  ERQ.polynomialBound
    (constant * ERQ.coefficient bound)
    (ERQ.exponent bound)
    boundedConstant
  where
    boundedConstant :
      ∀ n →
      constant * cost n
      ≤
      (constant * ERQ.coefficient bound)
      * ERQ.pow (suc n) (ERQ.exponent bound)
    boundedConstant n =
      subst
        (λ upper → constant * cost n ≤ upper)
        (sym
          (NatP.*-assoc
            constant
            (ERQ.coefficient bound)
            (ERQ.pow (suc n) (ERQ.exponent bound))))
        (NatP.*-mono-≤
          NatP.≤-refl
          (ERQ.bounded bound n))
