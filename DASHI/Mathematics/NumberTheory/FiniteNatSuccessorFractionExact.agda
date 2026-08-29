module DASHI.Mathematics.NumberTheory.FiniteNatSuccessorFractionExact where

------------------------------------------------------------------------
-- SUCCESSOR NUMERATOR FRACTION IDENTITY
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base using (+_)
open import Data.Integer.Solver renaming (module +-*-Solver to ℤSolver)
open ℤSolver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Nat.Base using (NonZero)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_; _+_; _≃_; *≡*)

open import DASHI.Physics.YangMills.CompactLieProofLevel

successorFraction :
  (k n : Nat) → .{{_ : NonZero n}} → ℚᵘ
successorFraction k n = + suc k / n

splitSuccessorFraction :
  (k n : Nat) → .{{_ : NonZero n}} → ℚᵘ
splitSuccessorFraction k n = (+ k / n) ℚ.+ (+ 1 / n)

successorFractionEquivalent :
  (k n : Nat) → .{{_ : NonZero n}} →
  successorFraction k n ℚ.≃ splitSuccessorFraction k n
successorFractionEquivalent k n =
  ℚ.*≡*
    (solve 2
      (λ k′ n′ →
        (k′ :+ con (+ 1)) :* (n′ :* n′)
        :=
        ((k′ :* n′) :+ (con (+ 1) :* n′)) :* n′)
      refl
      (+ k)
      (+ n))

successorFractionIdentityLevel : ProofLevel
successorFractionIdentityLevel = machineChecked
