module DASHI.ComputerScience.TekumBalancedSuccessorExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; _+_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using () renaming
  ( solve to solveℤ
  ; _:+_ to _ℤ+_
  ; _:*_ to _ℤ*_
  ; con to conℤ
  ; _:=_ to _ℤ=_
  )
open import Data.Vec using (Vec; []; _∷_)

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
-- arithmetic successor theorem. This is the exact carry kernel used by
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

-- Structural eliminator used by the parser-carry proof: a carry past a leading
-- positive trit preserves the witness on the remaining higher-order digits.
hasSuccessorTail :
  ∀ {n} {xs : Vec Trit.Trit n} →
  HasSuccessor (Trit.pos ∷ xs) →
  HasSuccessor xs
hasSuccessorTail (positiveCarry carry) = carry
