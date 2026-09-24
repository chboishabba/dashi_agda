{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.SingleSectorUnifiedCandidateValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.SingleSectorUnifiedCandidateExact as S
import DASHI.Physics.Foundations.SingleSectorRecoveryTransportExact as T

totalEqualityNotPrimitive :
  S.singleSectorTotalEqualityIsPrimitiveTheorem ≡ false
totalEqualityNotPrimitive = refl

recoveryUnaffected :
  T.singleSectorTotalisationChangesRecoveryTheorems ≡ false
recoveryUnaffected = refl
