module DASHI.Algebra.BalancedTernaryCenteredReconstructionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s⁻¹)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Integer.Base as ℤ using (ℤ; +_; _+_; _-_; -_; _≤_; +≤+)
import Data.Integer.Properties as ℤP
import Data.Integer.Solver as IntSolver
open IntSolver.+-*-Solver using ()
  renaming
    ( solve to solveℤ
    ; _:+_ to _ℤ+_
    ; _:-_ to _ℤ-_
    ; _:*_ to _ℤ*_
    ; con to conℤ
    ; _:=_ to _ℤ=_
    )
open import Data.Fin.Base using (Fin; toℕ)
import Data.Fin.Properties as FinP
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.Algebra.BalancedTernaryRankReconstructionExact as Rank

------------------------------------------------------------------------
-- A003462 really is (3^n - 1)/2, stated without division.
------------------------------------------------------------------------

twiceCenterPlusOne :
  (n : Nat) → 2 * Positional.center n + 1 ≡ BT.pow3 n
twiceCenterPlusOne zero = refl
twiceCenterPlusOne (suc n)
  rewrite sym (twiceCenterPlusOne n) =
  solve 1
    (λ c →
      (con 2 :* (con 1 :+ (con 3 :* c))) :+ con 1
      :=
      con 3 :* ((con 2 :* c) :+ con 1))
    refl
    (Positional.center n)

pow3RightIsSucTwiceCenter :
  (n : Nat) →
  Rank.pow3Right n ≡ suc (2 * Positional.center n)
pow3RightIsSucTwiceCenter n =
  trans
    (Rank.pow3RightMatchesPow3 n)
    (trans
      (sym (twiceCenterPlusOne n))
      (NatP.+-comm (2 * Positional.center n) 1))

------------------------------------------------------------------------
-- Canonical centered integer carrier.
--
-- rank k in Fin(3^n) denotes the actual integer k - A_n.
------------------------------------------------------------------------

record CenteredInteger (n : Nat) : Set where
  constructor centeredInteger
  field
    rank : Fin (Rank.pow3Right n)
open CenteredInteger public

centeredValue : ∀ {n} → CenteredInteger n → ℤ
centeredValue {n} c =
  (+ (toℕ (rank c))) ℤ.- (+ (Positional.center n))

encodeCentered :
  ∀ {n} → Vec Trit.Trit n → CenteredInteger n
encodeCentered ts = centeredInteger (Rank.rankWord ts)

decodeCentered :
  ∀ {n} → CenteredInteger n → Vec Trit.Trit n
decodeCentered {n} c = Rank.unrankWord n (rank c)

decodeEncodeCentered :
  ∀ {n} (ts : Vec Trit.Trit n) →
  decodeCentered (encodeCentered ts) ≡ ts
decodeEncodeCentered = Rank.unrankRankWord

encodeDecodeCentered :
  ∀ {n} (c : CenteredInteger n) →
  encodeCentered (decodeCentered c) ≡ c
encodeDecodeCentered {n} (centeredInteger r) =
  cong centeredInteger (Rank.rankUnrankWord n r)

------------------------------------------------------------------------
-- Exact signed-value interpretation and range.
------------------------------------------------------------------------

centeredValueEncode :
  ∀ {n} (ts : Vec Trit.Trit n) →
  centeredValue (encodeCentered ts)
  ≡ BT.toInteger (BT.eval ts)
centeredValueEncode {n} ts =
  trans
    (cong (λ k → (+ k) ℤ.- (+ (Positional.center n)))
      (Rank.rankToNatCode ts))
    (trans
      (cong (λ z → z ℤ.- (+ (Positional.center n)))
        (Positional.natCodeShift ts))
      (solveℤ 2
        (λ v c → (v ℤ+ c) ℤ- c ℤ= v)
        refl
        (BT.toInteger (BT.eval ts))
        (+ (Positional.center n))))

rankNatAtMostTwiceCenter :
  ∀ {n} (r : Fin (Rank.pow3Right n)) →
  toℕ r ≤ 2 * Positional.center n
rankNatAtMostTwiceCenter {n} r =
  s≤s⁻¹
    (subst
      (λ bound → toℕ r < bound)
      (pow3RightIsSucTwiceCenter n)
      (FinP.toℕ<n r))

doubleCenterMinusCenter :
  (n : Nat) →
  (+ (2 * Positional.center n)) ℤ.- (+ (Positional.center n))
  ≡ + (Positional.center n)
doubleCenterMinusCenter n
  rewrite ℤP.pos-* 2 (Positional.center n) =
  solveℤ 1
    (λ c → (conℤ (+ 2) ℤ* c) ℤ- c ℤ= c)
    refl
    (+ (Positional.center n))

centeredValueLower :
  ∀ {n} (c : CenteredInteger n) →
  ℤ.- (+ (Positional.center n)) ≤ centeredValue c
centeredValueLower {n} c =
  let open ℤP.≤-Reasoning in
  begin
    ℤ.- (+ (Positional.center n))
      ≡⟨ sym (ℤP.+-identityˡ (ℤ.- (+ (Positional.center n)))) ⟩
    (+ 0) ℤ.+ (ℤ.- (+ (Positional.center n)))
      ≤⟨ ℤP.+-monoˡ-≤ (ℤ.- (+ (Positional.center n))) (+≤+ z≤n) ⟩
    (+ (toℕ (rank c))) ℤ.+ (ℤ.- (+ (Positional.center n)))
      ∎

centeredValueUpper :
  ∀ {n} (c : CenteredInteger n) →
  centeredValue c ≤ + (Positional.center n)
centeredValueUpper {n} c =
  let open ℤP.≤-Reasoning in
  begin
    centeredValue c
      ≤⟨ ℤP.+-monoˡ-≤
            (ℤ.- (+ (Positional.center n)))
            (+≤+ (rankNatAtMostTwiceCenter (rank c))) ⟩
    (+ (2 * Positional.center n)) ℤ.- (+ (Positional.center n))
      ≡⟨ doubleCenterMinusCenter n ⟩
    + (Positional.center n)
      ∎

centeredValueWithinRange :
  ∀ {n} (c : CenteredInteger n) →
  (ℤ.- (+ (Positional.center n)) ≤ centeredValue c)
  × (centeredValue c ≤ + (Positional.center n))
centeredValueWithinRange c = centeredValueLower c , centeredValueUpper c

------------------------------------------------------------------------
-- Explicit same-object bijection used by the concrete Hunhold int_n backend.
------------------------------------------------------------------------

record Bijection (A B : Set) : Set where
  constructor bijection
  field
    forward : A → B
    backward : B → A
    backwardForward : (x : A) → backward (forward x) ≡ x
    forwardBackward : (y : B) → forward (backward y) ≡ y

balancedTernaryCenteredBijection :
  (n : Nat) → Bijection (Vec Trit.Trit n) (CenteredInteger n)
balancedTernaryCenteredBijection n =
  bijection encodeCentered decodeCentered decodeEncodeCentered encodeDecodeCentered
