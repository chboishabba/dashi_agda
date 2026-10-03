module DASHI.ComputerScience.TekumBalancedSuccessorExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base as ℤ using (ℤ; +_; _+_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using () renaming
  ( solve to solveℤ
  ; _:+_ to _ℤ+_
  ; _:*_ to _ℤ*_
  ; con to conℤ
  ; _:=_ to _ℤ=_
  )
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional

------------------------------------------------------------------------
-- ONE-STEP BALANCED-TERNARY SUCCESSOR, LST FIRST
--
--   T -> 0
--   0 -> 1
--   1 -> T with carry
--
-- The empty/all-positive case wraps and is deliberately excluded from the
-- arithmetic successor theorem.  This is exactly the carry mechanism used by
-- Hunhold Proposition 4 before the infinity endpoint.
------------------------------------------------------------------------

successorWord : ∀ {n} → Vec Trit.Trit n → Vec Trit.Trit n
successorWord [] = []
successorWord (Trit.neg ∷ xs) = Trit.zer ∷ xs
successorWord (Trit.zer ∷ xs) = Trit.pos ∷ xs
successorWord (Trit.pos ∷ xs) = Trit.neg ∷ successorWord xs

data HasSuccessor : ∀ {n} → Vec Trit.Trit n → Set where
  negativeHead : ∀ {n} {xs : Vec Trit.Trit n} →
    HasSuccessor (Trit.neg ∷ xs)
  zeroHead : ∀ {n} {xs : Vec Trit.Trit n} →
    HasSuccessor (Trit.zer ∷ xs)
  positiveCarry : ∀ {n} {xs : Vec Trit.Trit n} →
    HasSuccessor xs → HasSuccessor (Trit.pos ∷ xs)

successorInteger :
  ∀ {n} {xs : Vec Trit.Trit n} →
  HasSuccessor xs →
  BT.toInteger (BT.eval (successorWord xs))
  ≡ BT.toInteger (BT.eval xs) ℤ.+ (+ 1)
successorInteger {xs = Trit.neg ∷ xs} negativeHead
  rewrite Positional.evalIntegerCons Trit.neg xs
        | Positional.evalIntegerCons Trit.zer xs =
  solveℤ 1
    (λ t →
      conℤ (+ 0) ℤ+ (conℤ (+ 3) ℤ* t)
      ℤ= (conℤ -[1+ 0 ] ℤ+ (conℤ (+ 3) ℤ* t)) ℤ+ conℤ (+ 1))
    refl (BT.toInteger (BT.eval xs))
successorInteger {xs = Trit.zer ∷ xs} zeroHead
  rewrite Positional.evalIntegerCons Trit.zer xs
        | Positional.evalIntegerCons Trit.pos xs =
  solveℤ 1
    (λ t →
      conℤ (+ 1) ℤ+ (conℤ (+ 3) ℤ* t)
      ℤ= (conℤ (+ 0) ℤ+ (conℤ (+ 3) ℤ* t)) ℤ+ conℤ (+ 1))
    refl (BT.toInteger (BT.eval xs))
successorInteger {xs = Trit.pos ∷ xs} (positiveCarry carry)
  rewrite Positional.evalIntegerCons Trit.pos xs
        | Positional.evalIntegerCons Trit.neg (successorWord xs)
        | successorInteger carry =
  solveℤ 1
    (λ t →
      conℤ -[1+ 0 ] ℤ+ (conℤ (+ 3) ℤ* (t ℤ+ conℤ (+ 1)))
      ℤ= (conℤ (+ 1) ℤ+ (conℤ (+ 3) ℤ* t)) ℤ+ conℤ (+ 1))
    refl (BT.toInteger (BT.eval xs))

------------------------------------------------------------------------
-- The witness is exactly "not all positive", exposed structurally rather than
-- through a Boolean so downstream parser proofs can pattern-match on carry.
------------------------------------------------------------------------

hasSuccessorTail :
  ∀ {n} {t : Trit.Trit} {xs : Vec Trit.Trit n} →
  HasSuccessor (t ∷ xs) →
  t ≡ Trit.pos →
  HasSuccessor xs
hasSuccessorTail negativeHead ()
hasSuccessorTail zeroHead ()
hasSuccessorTail (positiveCarry carry) refl = carry

successorInjectiveOnWitness :
  ∀ {n} {left right : Vec Trit.Trit n} →
  HasSuccessor left →
  HasSuccessor right →
  successorWord left ≡ successorWord right →
  left ≡ right
successorInjectiveOnWitness leftWitness rightWitness successorEq =
  Positional.toIntegerInjective
    (let
       leftStep = successorInteger leftWitness
       rightStep = successorInteger rightWitness
     in
     ℤ.+-cancelʳ-≡
       (BT.toInteger (BT.eval left))
       (BT.toInteger (BT.eval right))
       (+ 1)
       (trans leftStep (trans (cong (λ w → BT.toInteger (BT.eval w)) successorEq) (Relation.Binary.PropositionalEquality.sym rightStep))))
  where
  left = _
  right = _
