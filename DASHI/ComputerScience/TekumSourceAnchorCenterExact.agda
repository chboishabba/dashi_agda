module DASHI.ComputerScience.TekumSourceAnchorCenterExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; _+_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using () renaming
  ( solve to solveℤ
  ; _:+_ to _ℤ+_
  ; _:*_ to _ℤ*_
  ; con to conℤ
  ; _:=_ to _ℤ=_
  )
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.ComputerScience.TekumWidthAdmissibilityExact as Width

------------------------------------------------------------------------
-- HUNHOLD DEFINITION 7: THE ANCHOR MIDPOINT WORD
--
-- The paper subtracts the alternating balanced-ternary code 1T...1T at even
-- source widths. Repository Vec words are least-significant-trit first, so the
-- same word is stored T1T1....
------------------------------------------------------------------------

sourceAnchorCenterWord : (n : Nat) → Vec Trit.Trit n
sourceAnchorCenterWord zero = []
sourceAnchorCenterWord (suc zero) = Trit.neg ∷ []
sourceAnchorCenterWord (suc (suc n)) =
  Trit.neg ∷ Trit.pos ∷ sourceAnchorCenterWord n

sourceAnchorCenterWidth2 :
  sourceAnchorCenterWord 2
  ≡ Trit.neg ∷ Trit.pos ∷ []
sourceAnchorCenterWidth2 = refl

sourceAnchorCenterWidth4 :
  sourceAnchorCenterWord 4
  ≡ Trit.neg ∷ Trit.pos ∷ Trit.neg ∷ Trit.pos ∷ []
sourceAnchorCenterWidth4 = refl

sourceAnchorCenterInteger2 :
  BT.toInteger (BT.eval (sourceAnchorCenterWord 2)) ≡ + 2
sourceAnchorCenterInteger2 = refl

sourceAnchorCenterInteger4 :
  BT.toInteger (BT.eval (sourceAnchorCenterWord 4)) ≡ + 20
sourceAnchorCenterInteger4 = refl

------------------------------------------------------------------------
-- Closed coordinates without division.
------------------------------------------------------------------------

evenLength : Nat → Nat
evenLength zero = zero
evenLength (suc k) = suc (suc (evenLength k))

sourceCenterMagnitude : Nat → Nat
sourceCenterMagnitude zero = zero
sourceCenterMagnitude (suc k) = 2 + 9 * sourceCenterMagnitude k

evenLengthIsTwice :
  (k : Nat) → evenLength k ≡ 2 * k
evenLengthIsTwice zero = refl
evenLengthIsTwice (suc k)
  rewrite evenLengthIsTwice k =
  solve 1
    (λ h → con 2 :+ (con 2 :* h) := con 2 :* (con 1 :+ h))
    refl k

sourceCenterIntegerEvenLength :
  (k : Nat) →
  BT.toInteger (BT.eval (sourceAnchorCenterWord (evenLength k)))
  ≡ + (sourceCenterMagnitude k)
sourceCenterIntegerEvenLength zero = refl
sourceCenterIntegerEvenLength (suc k)
  rewrite sourceCenterIntegerEvenLength k
        | Positional.evalIntegerCons Trit.neg
            (Trit.pos ∷ sourceAnchorCenterWord (evenLength k))
        | Positional.evalIntegerCons Trit.pos
            (sourceAnchorCenterWord (evenLength k)) =
  solveℤ 1
    (λ c →
      conℤ -[1+ 0 ] ℤ+ (conℤ (+ 3) ℤ* (conℤ (+ 1) ℤ+ (conℤ (+ 3) ℤ* c)))
      ℤ= conℤ (+ 2) ℤ+ (conℤ (+ 9) ℤ* c))
    refl (+ (sourceCenterMagnitude k))

sourceCenterNatCodeEvenLength :
  (k : Nat) →
  Positional.natCode (sourceAnchorCenterWord (evenLength k))
  ≡ 3 * sourceCenterMagnitude k
sourceCenterNatCodeEvenLength zero = refl
sourceCenterNatCodeEvenLength (suc k)
  rewrite sourceCenterNatCodeEvenLength k =
  solve 1
    (λ c →
      con 0 :+ (con 3 :* (con 2 :+ (con 3 :* (con 3 :* c))))
      := con 3 :* (con 2 :+ (con 9 :* c)))
    refl (sourceCenterMagnitude k)

centerEvenLength :
  (k : Nat) →
  Positional.center (evenLength k) ≡ 2 * sourceCenterMagnitude k
centerEvenLength zero = refl
centerEvenLength (suc k)
  rewrite centerEvenLength k =
  solve 1
    (λ c →
      con 1 :+ (con 3 :* (con 1 :+ (con 3 :* (con 2 :* c))))
      := con 2 :* (con 2 :+ (con 9 :* c)))
    refl (sourceCenterMagnitude k)

------------------------------------------------------------------------
-- Transport the closed coordinates through the repository EvenWidth witness.
------------------------------------------------------------------------

sourceCenterMagnitudeAt : ∀ {n} → Width.EvenWidth n → Nat
sourceCenterMagnitudeAt w = sourceCenterMagnitude (Width.half w)

evenLengthMatchesWidth :
  ∀ {n} (w : Width.EvenWidth n) → evenLength (Width.half w) ≡ n
evenLengthMatchesWidth w =
  trans (evenLengthIsTwice (Width.half w)) (Width.twiceHalf w)

centerAtEvenWidth :
  ∀ {n} (w : Width.EvenWidth n) →
  Positional.center n ≡ 2 * sourceCenterMagnitudeAt w
centerAtEvenWidth w =
  subst
    (λ m → Positional.center m ≡ 2 * sourceCenterMagnitudeAt w)
    (evenLengthMatchesWidth w)
    (centerEvenLength (Width.half w))

sourceCenterNatCodeAtEvenWidth :
  ∀ {n} (w : Width.EvenWidth n) →
  Positional.natCode (sourceAnchorCenterWord n)
  ≡ 3 * sourceCenterMagnitudeAt w
sourceCenterNatCodeAtEvenWidth w =
  subst
    (λ m →
      Positional.natCode (sourceAnchorCenterWord m)
      ≡ 3 * sourceCenterMagnitudeAt w)
    (evenLengthMatchesWidth w)
    (sourceCenterNatCodeEvenLength (Width.half w))

sourceCenterIntegerAtEvenWidth :
  ∀ {n} (w : Width.EvenWidth n) →
  BT.toInteger (BT.eval (sourceAnchorCenterWord n))
  ≡ + (sourceCenterMagnitudeAt w)
sourceCenterIntegerAtEvenWidth w =
  subst
    (λ m →
      BT.toInteger (BT.eval (sourceAnchorCenterWord m))
      ≡ + (sourceCenterMagnitudeAt w))
    (evenLengthMatchesWidth w)
    (sourceCenterIntegerEvenLength (Width.half w))
