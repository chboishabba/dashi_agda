{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.ColliderChiSquareScopeMatrixValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Closure.ColliderChiSquareScopeMatrixExact as C

atlasFixtureNotAuthority :
  C.ColliderChiSquareScopeBoundary.lowChi2FixtureIsAcceptedEmpiricalAuthority
    C.canonicalColliderChiSquareScopeBoundary
  ≡ false
atlasFixtureNotAuthority = refl

w4DoesNotCancelCMSRatio :
  C.ColliderChiSquareScopeBoundary.rejectedAbsoluteProjectionCancelsBoundedRatioContact
    C.canonicalColliderChiSquareScopeBoundary
  ≡ false
w4DoesNotCancelCMSRatio = refl
