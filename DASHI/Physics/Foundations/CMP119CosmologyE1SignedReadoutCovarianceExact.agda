{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1SignedReadoutCovarianceExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; -ℝ_)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed

applyBasisSign : Signed.BasisSign → ℝ → ℝ
applyBasisSign Signed.plus value = value
applyBasisSign Signed.minus value = -ℝ value

signedComponentReadout :
  (K.SymmetricTensorComponent4 → ℝ) →
  Signed.SignedSymmetricComponent → ℝ
signedComponentReadout readout signed =
  applyBasisSign (Signed.sign signed)
    (readout (Signed.component signed))

transformedComponentReadout :
  Signed.SignedAxisAction →
  (K.SymmetricTensorComponent4 → ℝ) →
  K.SymmetricTensorComponent4 → ℝ
transformedComponentReadout action readout component =
  signedComponentReadout readout
    (Signed.actSignedComponent action component)

record SignedTenSlotReadoutCovariance
    (EuclideanAction : Set)
    (axisAction : EuclideanAction → Signed.SignedAxisAction)
    (readout : K.SymmetricTensorComponent4 → ℝ)
    : Set₁ where
  field
    componentCovariant :
      ∀ action component →
      transformedComponentReadout (axisAction action) readout component
      ≡ readout component

open SignedTenSlotReadoutCovariance public

reflection01CovarianceHasRequiredMinusSign :
  ∀ (readout : K.SymmetricTensorComponent4 → ℝ) →
  transformedComponentReadout Signed.timeReflection readout K.component01
  ≡ -ℝ (readout K.component01)
reflection01CovarianceHasRequiredMinusSign readout = Agda.Builtin.Equality.refl

signedReadoutAvoidsFakeNegativeTangentLabel : Bool
signedReadoutAvoidsFakeNegativeTangentLabel = true

remainingFullE1LeafIsSignedComponentReadoutCovariance : Bool
remainingFullE1LeafIsSignedComponentReadoutCovariance = true
