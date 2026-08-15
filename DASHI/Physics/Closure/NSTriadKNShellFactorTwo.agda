module DASHI.Physics.Closure.NSTriadKNShellFactorTwo where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s; ∣_-_∣)
import Data.Nat.Properties as Nat
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNCeilLogShellBounds as Bounds

shellBelowSuccessorFromFactorTwo :
  ∀ {a b} →
  a ≤ 2 * b →
  Shell.shellIndexMagnitude a ≤ suc (Shell.shellIndexMagnitude b)
shellBelowSuccessorFromFactorTwo {a} {b} a≤2b =
  subst
    (λ upper → Shell.shellIndexMagnitude a ≤ upper)
    (Shell.shellIndexPowerOfTwo (suc (Shell.shellIndexMagnitude b)))
    (Shell.shellIndexMonotone a≤power)
  where
  a≤power :
    a ≤ Shell.pow2 (suc (Shell.shellIndexMagnitude b))
  a≤power =
    Nat.≤-trans
      a≤2b
      (Nat.*-monoʳ-≤ 2
        (Bounds.ceilLogShellUpperMagnitude b))

mutual
  shellDistanceAtMostOne :
    ∀ {left right} →
    left ≤ suc right →
    right ≤ suc left →
    ∣ left - right ∣ ≤ 1
  shellDistanceAtMostOne {zero} {zero} leftBound rightBound = z≤n
  shellDistanceAtMostOne {zero} {suc zero} leftBound rightBound =
    s≤s z≤n
  shellDistanceAtMostOne {zero} {suc (suc right)}
    leftBound (s≤s ())
  shellDistanceAtMostOne {suc zero} {zero} leftBound rightBound =
    s≤s z≤n
  shellDistanceAtMostOne {suc (suc left)} {zero}
    (s≤s ()) rightBound
  shellDistanceAtMostOne {suc left} {suc right}
    (s≤s leftBound) (s≤s rightBound) =
    shellDistanceAtMostOne leftBound rightBound

factorTwoNormsGiveShellDistanceOne :
  ∀ {a b} →
  a ≤ 2 * b →
  b ≤ 2 * a →
  ∣ Shell.shellIndexMagnitude a - Shell.shellIndexMagnitude b ∣ ≤ 1
factorTwoNormsGiveShellDistanceOne {a} {b} a≤2b b≤2a =
  shellDistanceAtMostOne
    {left = Shell.shellIndexMagnitude a}
    {right = Shell.shellIndexMagnitude b}
    (shellBelowSuccessorFromFactorTwo {a = a} {b = b} a≤2b)
    (shellBelowSuccessorFromFactorTwo {a = b} {b = a} b≤2a)

shellFactorTwoTheoremClosed : Bool
shellFactorTwoTheoremClosed = true

shellFactorTwoTheoremClosedIsTrue :
  shellFactorTwoTheoremClosed ≡ true
shellFactorTwoTheoremClosedIsTrue = refl
