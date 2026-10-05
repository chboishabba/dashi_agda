module DASHI.Mathematics.NumberTheory.FiniteNatRationalEmbeddingExact where

------------------------------------------------------------------------
-- NAT -> UNNORMALISED RATIONAL SEMIRING EMBEDDING
--
-- Repository-original glue for the concrete rational carrier used by the
-- vendored Bishop reals.  Keeping these laws here prevents domain modules from
-- asking a real-ring solver to infer arithmetic relationships between opaque
-- embedded Nat constants.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
import Data.Integer.Base as ℤB
open ℤB using (ℤ; +_)
import Data.Integer.Properties as ℤP
import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; cong₂)
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; _/_; _≃_; *≡*)

open import DASHI.Physics.YangMills.CompactLieProofLevel

natAsRational : Nat → ℚᵘ
natAsRational n = + n / 1

natAsRationalAdd :
  (left right : Nat) →
  natAsRational (left + right)
  ℚ.≃
  (natAsRational left ℚ.+ natAsRational right)
natAsRationalAdd left right = ℚ.*≡*
  (trans (ℤP.*-identityʳ (+ (left + right)))
    (trans (ℤP.pos-+ left right)
      (trans (cong₂ ℤB._+_ (sym (ℤP.*-identityʳ (+ left))) (sym (ℤP.*-identityʳ (+ right))))
        (sym (ℤP.*-identityʳ (ℤB._+_ (+ left ℤB.* + 1) (+ right ℤB.* + 1)))))))

natAsRationalMul :
  (left right : Nat) →
  natAsRational (left * right)
  ℚ.≃
  (natAsRational left ℚ.* natAsRational right)
natAsRationalMul left right = ℚ.*≡*
  (trans (ℤP.*-identityʳ (+ (left * right)))
    (trans (ℤP.pos-* left right)
      (sym (ℤP.*-identityʳ (+ left ℤB.* + right)))))

natAsRationalSuccessor :
  (n : Nat) →
  natAsRational (suc n)
  ℚ.≃
  (natAsRational n ℚ.+ (+ 1 / 1))
natAsRationalSuccessor n = ℚ.*≡*
  (trans (ℤP.*-identityʳ (+ (suc n)))
    (trans (cong +_ (sym (ℕP.+-comm n 1)))
      (trans (ℤP.pos-+ n 1)
        (trans (cong₂ ℤB._+_ (sym (ℤP.*-identityʳ (+ n))) (sym (ℤP.*-identityʳ (+ 1))))
          (sym (ℤP.*-identityʳ (ℤB._+_ (+ n ℤB.* + 1) (+ 1 ℤB.* + 1))))))))

finiteNatRationalEmbeddingLevel : ProofLevel
finiteNatRationalEmbeddingLevel = machineChecked
