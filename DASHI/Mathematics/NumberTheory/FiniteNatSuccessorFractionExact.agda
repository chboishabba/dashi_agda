module DASHI.Mathematics.NumberTheory.FiniteNatSuccessorFractionExact where

------------------------------------------------------------------------
-- SUCCESSOR NUMERATOR FRACTION IDENTITY
--
-- For positive natural denominator n,
--
--   (k + 1) / n  ≃  k / n + 1 / n.
--
-- The equality is the setoid equality of Data.Rational.Unnormalised, matching
-- the rational representation used by the pinned vendor/bishop Real carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (NonZero)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_; _+_; _≃_)
import Data.Rational.Unnormalised.Properties as ℚP

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
  ℚP.*≡*
    (begin
      (+ suc k) * (+ n * + n)
        ≡⟨⟩
      (+ k + + 1) * (+ n * + n)
        ≡⟨ solveIdentity k n ⟩
      ((+ k * + n) + (+ 1 * + n)) * + n
        ∎)
  where
  open import Data.Integer.Properties as ℤP
  open ℤP.≡-Reasoning

  solveIdentity :
    (k n : Nat) →
    (+ k + + 1) * (+ n * + n)
    ≡ ((+ k * + n) + (+ 1 * + n)) * + n
  solveIdentity k n =
    begin
      (+ k + + 1) * (+ n * + n)
        ≡⟨ ℤP.*-assoc (+ k + + 1) (+ n) (+ n) ⟨
      ((+ k + + 1) * + n) * + n
        ≡⟨ cong (_* + n) (ℤP.*-distribʳ-+ (+ k) (+ 1) (+ n)) ⟩
      ((+ k * + n) + (+ 1 * + n)) * + n
        ∎

successorFractionIdentityLevel : ProofLevel
successorFractionIdentityLevel = machineChecked
