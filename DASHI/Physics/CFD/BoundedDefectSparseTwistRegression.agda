module DASHI.Physics.CFD.BoundedDefectSparseTwistRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (z≤n)

import DASHI.Algebra.Trit as Trit
import DASHI.Physics.CFD.SparseTwistLESOperator as Exact
open import DASHI.Physics.CFD.BoundedDefectSparseTwistOperator

------------------------------------------------------------------------
-- Equality geometry inhabits the bounded interface with zero defect.
------------------------------------------------------------------------

equalityGeometry : ErrorGeometry Trit.Trit
equalityGeometry = record
  { Within = λ _ x y → x ≡ y
  ; within-refl = λ _ → refl
  ; within-compose = λ { refl refl → refl }
  }

identityCodec : Exact.LosslessStructuralCodec
identityCodec = record
  { FullState = Trit.Trit
  ; ProxyState = Trit.Trit
  ; encode = λ x → x
  ; decode = λ x → x
  ; decode-encode = λ _ → refl
  ; fullStorageCost = λ _ → zero
  ; proxyStorageCost = λ _ → zero
  ; storageNonexpansive = λ _ → z≤n
  }

identityBoundedOperator :
  BoundedDefectProxyOperator identityCodec equalityGeometry
identityBoundedOperator = record
  { fullStep = λ x → x
  ; proxyStep = λ x → x
  ; oneStepError = zero
  ; stabilityFactor = suc zero
  ; oneStepDefect = λ _ → refl
  ; fullStepStable = λ witness → witness
  }

zero-defect-rollout :
  ∀ n x →
  Within equalityGeometry
    (rolloutBound zero (suc zero) n)
    (Exact.decode identityCodec
      (Exact.iterate n (proxyStep identityBoundedOperator)
        (Exact.encode identityCodec x)))
    (Exact.iterate n (fullStep identityBoundedOperator) x)
zero-defect-rollout =
  bounded-encoded-rollout
    identityCodec
    equalityGeometry
    identityBoundedOperator

boundary-keeps-clay-closed :
  clayPromotionAvailable canonicalBoundedDefectBoundary ≡ Agda.Builtin.Bool.false
boundary-keeps-clay-closed = refl
