module DASHI.Geometry.MQContractive where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (_<_; _≤_)

open import DASHI.Core.Q using (ℚ; _*ℚ_; 1ℚ)
open import DASHI.Geometry.MaskedQuadratic

record MQContractive {n : Nat} (MQ : MaskedQuadratic n) : Set₁ where
  field
    T     : MaskedQuadratic.V MQ → MaskedQuadratic.V MQ
    lambda : ℚ
    lambda<1   : lambda < 1ℚ
    contract : ∀ x → MaskedQuadratic.Q MQ (T x) ≤ (lambda *ℚ lambda) *ℚ MaskedQuadratic.Q MQ x

open MQContractive public
