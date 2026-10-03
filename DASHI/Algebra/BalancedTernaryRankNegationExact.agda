module DASHI.Algebra.BalancedTernaryRankNegationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _∸_)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Fin.Base using (toℕ; opposite)
import Data.Fin.Properties as FinP
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Relation.Binary.PropositionalEquality.≡-Reasoning

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.Algebra.BalancedTernaryRankReconstructionExact as Rank
import DASHI.Algebra.BalancedTernaryCenteredReconstructionExact as Centered

------------------------------------------------------------------------
-- The shifted trit digits {0,1,2} are complemented by digitwise inversion.
------------------------------------------------------------------------

digitNatInvertComplement :
  (t : Trit.Trit) →
  Positional.digitNat (Trit.inv t) + Positional.digitNat t ≡ 2
digitNatInvertComplement Trit.neg = refl
digitNatInvertComplement Trit.zer = refl
digitNatInvertComplement Trit.pos = refl

centerSucc :
  (n : Nat) →
  Positional.center (suc n) ≡ 1 + 3 * Positional.center n
centerSucc n = refl

combineComplement :
  (x y a b : Nat) →
  (x + 3 * a) + (y + 3 * b)
  ≡ (x + y) + 3 * (a + b)
combineComplement x y a b =
  solve 4
    (λ x′ y′ a′ b′ →
      (x′ :+ (con 3 :* a′)) :+ (y′ :+ (con 3 :* b′))
      :=
      (x′ :+ y′) :+ (con 3 :* (a′ :+ b′)))
    refl x y a b

natCodeInvertComplement :
  ∀ {n} (ts : Vec Trit.Trit n) →
  Positional.natCode (BT.invertWord ts) + Positional.natCode ts
  ≡ 2 * Positional.center n
natCodeInvertComplement [] = refl
natCodeInvertComplement {suc n} (t ∷ ts) =
  begin
    (Positional.digitNat (Trit.inv t)
      + 3 * Positional.natCode (BT.invertWord ts))
      + (Positional.digitNat t + 3 * Positional.natCode ts)
  ≡⟨ combineComplement
        (Positional.digitNat (Trit.inv t))
        (Positional.digitNat t)
        (Positional.natCode (BT.invertWord ts))
        (Positional.natCode ts) ⟩
    (Positional.digitNat (Trit.inv t) + Positional.digitNat t)
      + 3 * (Positional.natCode (BT.invertWord ts) + Positional.natCode ts)
  ≡⟨ cong₂ (λ x y → x + 3 * y)
        (digitNatInvertComplement t)
        (natCodeInvertComplement ts) ⟩
    2 + 3 * (2 * Positional.center n)
  ≡⟨ solve 1
        (λ c → con 2 :+ (con 3 :* (con 2 :* c))
          := con 2 :* (con 1 :+ (con 3 :* c)))
        refl (Positional.center n) ⟩
    2 * (1 + 3 * Positional.center n)
  ≡⟨ cong (2 *_) (sym (centerSucc n)) ⟩
    2 * Positional.center (suc n)
  ∎
  where
  cong₂ : ∀ {A B C : Set} (f : A → B → C)
    {x x′ : A} {y y′ : B} →
    x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
  cong₂ f refl refl = refl

natCodeInvertIsCenteredComplement :
  ∀ {n} (ts : Vec Trit.Trit n) →
  Positional.natCode (BT.invertWord ts)
  ≡ 2 * Positional.center n ∸ Positional.natCode ts
natCodeInvertIsCenteredComplement ts =
  trans
    (sym (NatP.m+n∸n≡m
      (Positional.natCode (BT.invertWord ts))
      (Positional.natCode ts)))
    (cong (_∸ Positional.natCode ts) (natCodeInvertComplement ts))

oppositeRankToNatCode :
  ∀ {n} (ts : Vec Trit.Trit n) →
  toℕ (opposite (Rank.rankWord ts))
  ≡ 2 * Positional.center n ∸ Positional.natCode ts
oppositeRankToNatCode {n} ts =
  trans
    (FinP.opposite-prop (Rank.rankWord ts))
    (trans
      (cong₂ _∸_
        (Centered.pow3RightIsSucTwiceCenter n)
        (cong suc (Rank.rankToNatCode ts)))
      refl)
  where
  cong₂ : ∀ {A B C : Set} (f : A → B → C)
    {x x′ : A} {y y′ : B} →
    x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
  cong₂ f refl refl = refl

rankInvertIsOpposite :
  ∀ {n} (ts : Vec Trit.Trit n) →
  Rank.rankWord (BT.invertWord ts) ≡ opposite (Rank.rankWord ts)
rankInvertIsOpposite ts =
  FinP.toℕ-injective
    (trans
      (Rank.rankToNatCode (BT.invertWord ts))
      (trans
        (natCodeInvertIsCenteredComplement ts)
        (sym (oppositeRankToNatCode ts))))
