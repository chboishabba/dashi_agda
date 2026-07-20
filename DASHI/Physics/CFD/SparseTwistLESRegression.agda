module DASHI.Physics.CFD.SparseTwistLESRegression where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Nat.Base using (z≤n)

import DASHI.Algebra.Trit as Trit
import DASHI.Foundations.InvolutiveTernaryDynamics as Ternary
import DASHI.Learning.GrokkingOperatorContract as Learning
open import DASHI.Physics.CFD.SparseTwistLESOperator
open import DASHI.Physics.CFD.SparseTwistLESBridge

------------------------------------------------------------------------
-- Finite executable witness.
--
-- The identity witness is intentionally modest: its purpose is to regression
-- check that the codec, learner, sparse signed carrier, twist transport, and
-- exact rollout interfaces are jointly inhabitable without postulates.  It is
-- not a CFD calibration.
------------------------------------------------------------------------

identityCodec : LosslessStructuralCodec
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

identityLearner : Learning.LearningOperator Trit.Trit
identityLearner = record
  { step = λ x → x
  ; dataCode = λ _ → zero
  ; modelCode = λ _ → zero
  ; totalMDL = λ _ → zero
  ; totalMDL-def = λ _ → refl
  ; mdlMonotone = λ _ → z≤n
  }

identityLearnedOperator : ExactLearnedProxyOperator identityCodec
identityLearnedOperator = record
  { fullStep = λ x → x
  ; proxyStep = λ x → x
  ; step-commutes = λ _ → refl
  ; learner = identityLearner
  ; learner-step-agrees = λ _ → refl
  ; fullUpdateCost = λ _ → zero
  ; proxyUpdateCost = λ _ → zero
  ; updateNonexpansive = λ _ → z≤n
  }

identityTwistOperator : TwistOperator
identityTwistOperator = record
  { Field = Trit.Trit
  ; Control = Trit.Trit
  ; fieldι = Trit.inv
  ; controlι = Trit.inv
  ; fieldι-involutive = Trit.inv-invol
  ; controlι-involutive = Trit.inv-invol
  ; twist = λ x _ → x
  ; twist-equivariant = λ _ _ → refl
  ; activeCost = λ _ → zero
  ; sparseNonexpansive = λ _ _ → z≤n
  }

identityTwistBridge :
  TwistCodecBridge identityCodec identityLearnedOperator identityTwistOperator
identityTwistBridge = record
  { toTwistField = λ x → x
  ; fromTwistField = λ x → x
  ; from-to = λ _ → refl
  ; to-from = λ _ → refl
  ; controlAt = λ _ → Trit.zer
  ; full-step-is-twist = λ _ → refl
  }

singleSiteStructure : Trit.Trit → SignedSparseField ⊤
singleSiteStructure x = record
  { value = λ _ → x
  ; support = λ _ → Ternary.support x
  ; support-is-derived = λ _ → refl
  }

identitySparseTwistDASHILES : SparseTwistDASHILESFormalism
identitySparseTwistDASHILES = record
  { codec = identityCodec
  ; learnedOperator = identityLearnedOperator
  ; twistOperator = identityTwistOperator
  ; twistBridge = identityTwistBridge
  ; structuralIndex = ⊤
  ; signedStructure = singleSiteStructure
  ; claimBoundary = canonicalClaimBoundaryText
  }

negative-support-survives :
  support (singleSiteStructure Trit.neg) tt ≡ true
negative-support-survives = refl

positive-support-survives :
  support (singleSiteStructure Trit.pos) tt ≡ true
positive-support-survives = refl

identity-rollout-exact :
  ∀ n x →
  decode identityCodec
    (iterate n (proxyStep identityLearnedOperator) (encode identityCodec x))
  ≡
  iterate n (fullStep identityLearnedOperator) x
identity-rollout-exact =
  encoded-rollout-exact identityCodec identityLearnedOperator

identity-step-is-twist :
  ∀ x →
  fullStep identityLearnedOperator x ≡
  fromTwistField identityTwistBridge
    (twist identityTwistOperator
      (toTwistField identityTwistBridge x)
      (controlAt identityTwistBridge x))
identity-step-is-twist = full-step-is-twist identityTwistBridge
