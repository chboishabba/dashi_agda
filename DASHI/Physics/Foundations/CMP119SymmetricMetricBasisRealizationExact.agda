{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119MetricBasisStressComponentCompilerExact as Basis
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain

------------------------------------------------------------------------
-- TEN SYMMETRIC TENSOR SLOTS -> CMP119 METRIC PERTURBATION DOMAIN
------------------------------------------------------------------------

symmetricSlotOfAxes :
  Flat.Axis4 → Flat.Axis4 → K.SymmetricTensorComponent4
symmetricSlotOfAxes Flat.timeAxis Flat.timeAxis = K.component00
symmetricSlotOfAxes Flat.timeAxis Flat.xAxis = K.component01
symmetricSlotOfAxes Flat.timeAxis Flat.yAxis = K.component02
symmetricSlotOfAxes Flat.timeAxis Flat.zAxis = K.component03
symmetricSlotOfAxes Flat.xAxis Flat.timeAxis = K.component01
symmetricSlotOfAxes Flat.xAxis Flat.xAxis = K.component11
symmetricSlotOfAxes Flat.xAxis Flat.yAxis = K.component12
symmetricSlotOfAxes Flat.xAxis Flat.zAxis = K.component13
symmetricSlotOfAxes Flat.yAxis Flat.timeAxis = K.component02
symmetricSlotOfAxes Flat.yAxis Flat.xAxis = K.component12
symmetricSlotOfAxes Flat.yAxis Flat.yAxis = K.component22
symmetricSlotOfAxes Flat.yAxis Flat.zAxis = K.component23
symmetricSlotOfAxes Flat.zAxis Flat.timeAxis = K.component03
symmetricSlotOfAxes Flat.zAxis Flat.xAxis = K.component13
symmetricSlotOfAxes Flat.zAxis Flat.yAxis = K.component23
symmetricSlotOfAxes Flat.zAxis Flat.zAxis = K.component33

record SymmetricMetricBasisRealization
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    (domain : Domain.CanonicalMetricSourceDomain Scale Volume activity) : Set₁ where
  field
    componentPerturbation :
      K.SymmetricTensorComponent4 →
      Domain.MetricPerturbation domain

    componentPerturbationAdmissible :
      ∀ component →
      Domain.AdmissibleMetricPerturbation domain
        (componentPerturbation component)

open SymmetricMetricBasisRealization public

compileSymmetricBasis16 :
  ∀ {Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity} →
  SymmetricMetricBasisRealization domain →
  Basis.MetricBasis16 domain
compileSymmetricBasis16 realization = record
  { Basis.MetricBasis16.basisPerturbation =
      λ a b →
        componentPerturbation realization (symmetricSlotOfAxes a b)
  ; Basis.MetricBasis16.basisAdmissible =
      λ a b →
        componentPerturbationAdmissible realization
          (symmetricSlotOfAxes a b)
  }

orderedPairBasisIsGeneratedFromTenSlots : Bool
orderedPairBasisIsGeneratedFromTenSlots = true

orderedPairBasisIsGeneratedFromTenSlotsIsTrue :
  orderedPairBasisIsGeneratedFromTenSlots ≡ true
orderedPairBasisIsGeneratedFromTenSlotsIsTrue = refl

sixteenIndependentMetricBasisVectorsRequired : Bool
sixteenIndependentMetricBasisVectorsRequired = false

sixteenIndependentMetricBasisVectorsRequiredIsFalse :
  sixteenIndependentMetricBasisVectorsRequired ≡ false
sixteenIndependentMetricBasisVectorsRequiredIsFalse = refl

symmetricSlotToCMP119PerturbationStillRequired : Bool
symmetricSlotToCMP119PerturbationStillRequired = true

symmetricSlotToCMP119PerturbationStillRequiredIsTrue :
  symmetricSlotToCMP119PerturbationStillRequired ≡ true
symmetricSlotToCMP119PerturbationStillRequiredIsTrue = refl
