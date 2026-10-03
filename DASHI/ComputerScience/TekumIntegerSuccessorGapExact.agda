module DASHI.ComputerScience.TekumIntegerSuccessorGapExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; _<_; +<+; -<+; -<-)
open import Data.Nat.Base using (_<_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.ComputerScience.TekumTriadicScaleExact as Scale
import DASHI.ComputerScience.TekumExponentBandExact as Band

------------------------------------------------------------------------
-- INTEGER STRICT ORDER AS A POSITIVE NUMBER OF SOURCE SUCCESSOR STEPS
--
-- The band owner is phrased in repeated Scale.integerSucc steps.  This file
-- proves that ordinary integer strict order has exactly that shape, without
-- enumerating the bounded Tekum exponent table.
------------------------------------------------------------------------

natStrictGap :
  ∀ {m n : Nat} →
  m < n →
  Σ Nat (λ k → m + suc k ≡ n)
natStrictGap {zero} {suc n} p = n , refl
natStrictGap {suc m} {suc n} (s≤s p) with natStrictGap p
... | k , eq = k , cong suc eq

advancePositive :
  (k m : Nat) →
  Band.advanceExponent k (+ m) ≡ + (m + k)
advancePositive zero m = cong +_ (sym (NatP.+-identityʳ m))
advancePositive (suc k) m =
  trans
    (cong Scale.integerSucc (advancePositive k m))
    (cong +_ (sym (NatP.+-suc m k)))

advanceCommuteSucc :
  (k : Nat) (e : ℤ) →
  Band.advanceExponent (suc k) e
  ≡ Band.advanceExponent k (Scale.integerSucc e)
advanceCommuteSucc zero e = refl
advanceCommuteSucc (suc k) e =
  cong Scale.integerSucc (advanceCommuteSucc k e)

advanceAdd :
  (a b : Nat) (e : ℤ) →
  Band.advanceExponent (a + b) e
  ≡ Band.advanceExponent b (Band.advanceExponent a e)
advanceAdd a zero e
  rewrite NatP.+-identityʳ a = refl
advanceAdd a (suc b) e
  rewrite NatP.+-suc a b =
  cong Scale.integerSucc (advanceAdd a b e)

advanceNegativeToZero :
  (m : Nat) →
  Band.advanceExponent (suc m) -[1+ m ] ≡ + zero
advanceNegativeToZero zero = refl
advanceNegativeToZero (suc m) =
  trans
    (advanceCommuteSucc (suc m) -[1+ suc m ])
    (advanceNegativeToZero m)

advanceNegativeToPositive :
  (m n : Nat) →
  Band.advanceExponent ((suc m) + n) -[1+ m ] ≡ + n
advanceNegativeToPositive m n =
  trans
    (advanceAdd (suc m) n -[1+ m ])
    (trans
      (cong (Band.advanceExponent n) (advanceNegativeToZero m))
      (trans
        (advancePositive n zero)
        refl))

advanceNegativeGap :
  (n k : Nat) →
  Band.advanceExponent k -[1+ (n + k) ] ≡ -[1+ n ]
advanceNegativeGap n zero =
  cong -[1+_] (NatP.+-identityʳ n)
advanceNegativeGap n (suc k)
  rewrite NatP.+-suc n k =
  trans
    (advanceCommuteSucc k -[1+ suc (n + k) ])
    (advanceNegativeGap n k)

integerLessHasPositiveAdvance :
  ∀ {e e' : ℤ} →
  e ℤ.< e' →
  Σ Nat (λ k → Band.advanceExponent (suc k) e ≡ e')
integerLessHasPositiveAdvance {+ m} {+ n} (+<+ m<n) with natStrictGap m<n
... | k , eq =
  k , trans (advancePositive (suc k) m) (cong +_ eq)
integerLessHasPositiveAdvance {+ m} { -[1+ n ]} ()
integerLessHasPositiveAdvance { -[1+ m ]} {+ n} -<+ =
  (m + n) , advanceNegativeToPositive m n
integerLessHasPositiveAdvance { -[1+ m ]} { -[1+ n ]} (-<- n<m)
  with natStrictGap n<m
... | k , eq =
  k ,
  trans
    (cong
      (λ q → Band.advanceExponent (suc k) -[1+ q ])
      (sym eq))
    (advanceNegativeGap n (suc k))
