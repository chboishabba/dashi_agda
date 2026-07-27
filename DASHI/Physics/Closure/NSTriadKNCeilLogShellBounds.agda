module DASHI.Physics.Closure.NSTriadKNCeilLogShellBounds where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; _<_; _∸_; z≤n; s≤s)
open import Data.Nat.Logarithm using (n≤2^⌈log₂n⌉)
import Data.Nat.Properties as Nat
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity

sucNotLeSelf : ∀ {n} → suc n ≤ n → ⊥
sucNotLeSelf {zero} ()
sucNotLeSelf {suc n} (s≤s proof) = sucNotLeSelf proof

positiveNotLePredecessor :
  ∀ {n} → 0 < n → n ≤ n ∸ 1 → ⊥
positiveNotLePredecessor {zero} ()
positiveNotLePredecessor {suc n} positive proof =
  sucNotLeSelf proof

ceilLogShellUpperMagnitude :
  ∀ n → n ≤ Shell.pow2 (Shell.shellIndexMagnitude n)
ceilLogShellUpperMagnitude = n≤2^⌈log₂n⌉

ceilLogShellLowerMagnitude :
  ∀ n →
  0 < Shell.shellIndexMagnitude n →
  Shell.pow2 (Shell.shellIndexMagnitude n ∸ 1) < n
ceilLogShellLowerMagnitude n positive =
  Nat.≰⇒> contradiction
  where
  index : Nat
  index = Shell.shellIndexMagnitude n

  contradiction : n ≤ Shell.pow2 (index ∸ 1) → ⊥
  contradiction n≤power =
    positiveNotLePredecessor positive
      (subst
        (λ upper → index ≤ upper)
        (Shell.shellIndexPowerOfTwo (index ∸ 1))
        (Shell.shellIndexMonotone n≤power))

literalDyadicShellBoundsClosed : Shell.DyadicShellBounds
literalDyadicShellBoundsClosed = record
  { shellUpper = λ k nonzero →
      ceilLogShellUpperMagnitude (Infinity.infinityNorm k)
  ; shellLower = λ k nonzero positive →
      ceilLogShellLowerMagnitude (Infinity.infinityNorm k) positive
  }

ceilLogShellBoundaryProofClosed : Bool
ceilLogShellBoundaryProofClosed = true

ceilLogShellBoundaryProofClosedIsTrue :
  ceilLogShellBoundaryProofClosed ≡ true
ceilLogShellBoundaryProofClosedIsTrue = refl
