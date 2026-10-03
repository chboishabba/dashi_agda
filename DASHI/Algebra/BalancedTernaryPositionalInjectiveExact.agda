module DASHI.Algebra.BalancedTernaryPositionalInjectiveExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; _+_; _-_; _*_; ∣_∣)
import Data.Integer.Properties as ℤP
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:-_; _:*_; con; _:=_)
open import Data.Nat.Base using (_<_; z≤n; s≤s)
import Data.Nat.Properties as ℕP
import Data.Nat.DivMod as ℕDiv
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryA003462BridgeExact as A003462

------------------------------------------------------------------------
-- Unsigned normal form for the same trit word.
--
--   neg ↦ 0, zer ↦ 1, pos ↦ 2
--
-- This is not a second Tekum integer semantics.  It is the canonical shifted
-- base-three rank used only to prove that the existing centered evaluator is
-- injective.  The shift is exactly A003462(n).
------------------------------------------------------------------------

digitNat : Trit.Trit → Nat
digitNat Trit.neg = 0
digitNat Trit.zer = 1
digitNat Trit.pos = 2

digitInteger : Trit.Trit → ℤ
digitInteger Trit.neg = -[1+ 0 ]
digitInteger Trit.zer = + 0
digitInteger Trit.pos = + 1

natCode : ∀ {n} → Vec Trit.Trit n → Nat
natCode [] = 0
natCode (t ∷ ts) = digitNat t + 3 * natCode ts

center : Nat → Nat
center = A003462.maxMagnitude

------------------------------------------------------------------------
-- Integer interpretation of the existing signed-weight evaluator.
------------------------------------------------------------------------

toIntegerTritWeight :
  (t : Trit.Trit) →
  BT.toInteger (BT.tritWeight t) ≡ digitInteger t
toIntegerTritWeight Trit.neg = refl
toIntegerTritWeight Trit.zer = refl
toIntegerTritWeight Trit.pos = refl

toIntegerAddWeight :
  (x y : BT.SignedWeight) →
  BT.toInteger (BT.addWeight x y)
  ≡ BT.toInteger x ℤ.+ BT.toInteger y
toIntegerAddWeight (BT.signedWeight p n) (BT.signedWeight q m)
  rewrite ℤP.pos-+ p q | ℤP.pos-+ n m =
  solve 4
    (λ p′ q′ n′ m′ →
      (p′ :+ q′) :- (n′ :+ m′)
      := (p′ :- n′) :+ (q′ :- m′))
    refl (+ p) (+ q) (+ n) (+ m)

toIntegerScaleThree :
  (x : BT.SignedWeight) →
  BT.toInteger (BT.scaleThree x)
  ≡ (+ 3) ℤ.* BT.toInteger x
toIntegerScaleThree (BT.signedWeight p n)
  rewrite ℤP.pos-* 3 p | ℤP.pos-* 3 n =
  solve 2
    (λ p′ n′ →
      (con (+ 3) :* p′) :- (con (+ 3) :* n′)
      := con (+ 3) :* (p′ :- n′))
    refl (+ p) (+ n)

evalIntegerCons :
  ∀ {n} (t : Trit.Trit) (ts : Vec Trit.Trit n) →
  BT.toInteger (BT.eval (t ∷ ts))
  ≡ digitInteger t ℤ.+ ((+ 3) ℤ.* BT.toInteger (BT.eval ts))
evalIntegerCons t ts =
  trans
    (toIntegerAddWeight (BT.tritWeight t) (BT.scaleThree (BT.eval ts)))
    (trans
      (cong₂ ℤ._+_
        (toIntegerTritWeight t)
        (toIntegerScaleThree (BT.eval ts)))
      refl)
  where
  cong₂ : ∀ {A B C : Set} (f : A → B → C)
    {x x′ : A} {y y′ : B} →
    x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
  cong₂ f refl refl = refl

------------------------------------------------------------------------
-- Shifted base-three rank equals centered integer value plus A003462(n).
------------------------------------------------------------------------

digitShift :
  (t : Trit.Trit) →
  (+ (digitNat t)) ≡ digitInteger t ℤ.+ (+ 1)
digitShift Trit.neg = refl
digitShift Trit.zer = refl
digitShift Trit.pos = refl

natCodeIntegerCons :
  ∀ {n} (t : Trit.Trit) (ts : Vec Trit.Trit n) →
  (+ (natCode (t ∷ ts)))
  ≡ (+ (digitNat t)) ℤ.+ ((+ 3) ℤ.* (+ (natCode ts)))
natCodeIntegerCons t ts
  rewrite ℤP.pos-+ (digitNat t) (3 * natCode ts)
        | ℤP.pos-* 3 (natCode ts) = refl

centerIntegerSucc :
  (n : Nat) →
  (+ (center (suc n)))
  ≡ (+ 1) ℤ.+ ((+ 3) ℤ.* (+ (center n)))
centerIntegerSucc n
  rewrite ℤP.pos-+ 1 (3 * center n)
        | ℤP.pos-* 3 (center n) = refl

natCodeShift :
  ∀ {n} (ts : Vec Trit.Trit n) →
  (+ (natCode ts))
  ≡ BT.toInteger (BT.eval ts) ℤ.+ (+ (center n))
natCodeShift [] = refl
natCodeShift {suc n} (t ∷ ts) =
  trans
    (natCodeIntegerCons t ts)
    (trans
      (cong₂ ℤ._+_
        (digitShift t)
        (cong ((+ 3) ℤ.*_) (natCodeShift ts)))
      (trans
        (solve 3
          (λ d′ tail′ c′ →
            (d′ :+ con (+ 1)) :+ (con (+ 3) :* (tail′ :+ c′))
            := (d′ :+ (con (+ 3) :* tail′))
               :+ (con (+ 1) :+ (con (+ 3) :* c′)))
          refl
          (digitInteger t)
          (BT.toInteger (BT.eval ts))
          (+ (center n)))
        (cong₂ ℤ._+_
          (sym (evalIntegerCons t ts))
          (sym (centerIntegerSucc n)))))
  where
  cong₂ : ∀ {A B C : Set} (f : A → B → C)
    {x x′ : A} {y y′ : B} →
    x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
  cong₂ f refl refl = refl

------------------------------------------------------------------------
-- Base-three rank is injective by its least-significant remainder.
------------------------------------------------------------------------

digitNatLessThree : (t : Trit.Trit) → digitNat t < 3
digitNatLessThree Trit.neg = s≤s z≤n
digitNatLessThree Trit.zer = s≤s (s≤s z≤n)
digitNatLessThree Trit.pos = s≤s (s≤s (s≤s z≤n))

natCodeModThree :
  ∀ {n} (t : Trit.Trit) (ts : Vec Trit.Trit n) →
  natCode (t ∷ ts) mod 3 ≡ digitNat t
natCodeModThree t ts =
  trans
    (cong (λ k → (digitNat t + k) mod 3)
      (ℕP.*-comm 3 (natCode ts)))
    (trans
      (ℕDiv.[m+kn]%n≡m%n (digitNat t) (natCode ts) 3)
      (ℕDiv.m<n⇒m%n≡m (digitNatLessThree t)))
  where
  infixl 7 _mod_
  _mod_ = Agda.Builtin.Nat.mod-helper 0 2

-- Constructor-level statement used by the recursive proof.  This is the
-- exact finite remainder separation {-1,0,+1} mod 3, expressed through the
-- shifted digits {0,1,2}.
balancedRemainderDistinct :
  ∀ {t u : Trit.Trit} → digitNat t ≡ digitNat u → t ≡ u
balancedRemainderDistinct {Trit.neg} {Trit.neg} refl = refl
balancedRemainderDistinct {Trit.neg} {Trit.zer} ()
balancedRemainderDistinct {Trit.neg} {Trit.pos} ()
balancedRemainderDistinct {Trit.zer} {Trit.neg} ()
balancedRemainderDistinct {Trit.zer} {Trit.zer} refl = refl
balancedRemainderDistinct {Trit.zer} {Trit.pos} ()
balancedRemainderDistinct {Trit.pos} {Trit.neg} ()
balancedRemainderDistinct {Trit.pos} {Trit.zer} ()
balancedRemainderDistinct {Trit.pos} {Trit.pos} refl = refl

natCodeInjective :
  ∀ {n} {x y : Vec Trit.Trit n} →
  natCode x ≡ natCode y → x ≡ y
natCodeInjective {zero} {[]} {[]} eq = refl
natCodeInjective {suc n} {t ∷ ts} {u ∷ us} eq with
  balancedRemainderDistinct
    (trans
      (sym (natCodeModThree t ts))
      (trans (cong (λ k → k mod 3) eq) (natCodeModThree u us)))
  where
  infixl 7 _mod_
  _mod_ = Agda.Builtin.Nat.mod-helper 0 2
... | refl =
  cong (t ∷_)
    (natCodeInjective
      (ℕP.*-cancelˡ-≡
        (natCode ts) (natCode us) 3
        (ℕP.+-cancelˡ-≡
          (3 * natCode ts) (3 * natCode us) (digitNat t) eq)))

toIntegerInjective :
  ∀ {n} {x y : Vec Trit.Trit n} →
  BT.toInteger (BT.eval x) ≡ BT.toInteger (BT.eval y) → x ≡ y
toIntegerInjective {n} {x} {y} eq =
  natCodeInjective
    (cong ℤ.∣_∣
      (trans
        (natCodeShift x)
        (trans
          (cong (λ z → z ℤ.+ (+ (center n))) eq)
          (sym (natCodeShift y)))))

------------------------------------------------------------------------
-- Regression rows requested by the paper-completion plan.
------------------------------------------------------------------------

oneTritNegativeInteger :
  BT.toInteger (BT.eval (Trit.neg ∷ [])) ≡ -[1+ 0 ]
oneTritNegativeInteger = refl

oneTritZeroInteger :
  BT.toInteger (BT.eval (Trit.zer ∷ [])) ≡ + 0
oneTritZeroInteger = refl

oneTritPositiveInteger :
  BT.toInteger (BT.eval (Trit.pos ∷ [])) ≡ + 1
oneTritPositiveInteger = refl

twoTritNegativePositiveInteger :
  BT.toInteger (BT.eval (Trit.neg ∷ Trit.pos ∷ [])) ≡ + 2
twoTritNegativePositiveInteger = refl

twoTritZeroPositiveInteger :
  BT.toInteger (BT.eval (Trit.zer ∷ Trit.pos ∷ [])) ≡ + 3
twoTritZeroPositiveInteger = refl

twoTritPositivePositiveInteger :
  BT.toInteger (BT.eval (Trit.pos ∷ Trit.pos ∷ [])) ≡ + 4
twoTritPositivePositiveInteger = refl
