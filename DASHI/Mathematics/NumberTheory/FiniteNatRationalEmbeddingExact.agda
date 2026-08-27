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
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; _/_; _+_; _*_; _≃_; *≡*)

open import DASHI.Physics.YangMills.CompactLieProofLevel

natAsRational : Nat → ℚᵘ
natAsRational n = + n / 1

natAsRationalAdd :
  (left right : Nat) →
  natAsRational (left + right)
  ℚ.≃
  (natAsRational left ℚ.+ natAsRational right)
natAsRationalAdd left right = ℚ.*≡* refl

natAsRationalMul :
  (left right : Nat) →
  natAsRational (left * right)
  ℚ.≃
  (natAsRational left ℚ.* natAsRational right)
natAsRationalMul left right = ℚ.*≡* refl

finiteNatRationalEmbeddingLevel : ProofLevel
finiteNatRationalEmbeddingLevel = machineChecked
