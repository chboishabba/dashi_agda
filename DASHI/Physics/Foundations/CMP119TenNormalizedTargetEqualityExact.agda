{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119TenNormalizedTargetEqualityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Data.Nat.Base using (Nat)
open import Data.Rational.Base using (ℚ; +_; -[1+_]; 0ℚ)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Cut
import DASHI.Physics.Foundations.CMP119MetricBasisStressComponentCompilerExact as Basis
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as MetricBasis
import DASHI.Physics.Foundations.CMP119SymmetricStressComponentReductionExact as Sym
import DASHI.Physics.Foundations.CMP119TenNormalizedStressInsertionNumeratorsExact as Ten
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- TERMINAL NORMALIZED STRESS PAYMENT
--
-- The ten R116/R119 source-native stress insertion numerators are already
-- literal rational terms.  The remaining normalized cross-sector payment is
-- exactly their equality to the ten independent components of the checked
-- finite GR source.
------------------------------------------------------------------------

record TenNormalizedGRTargetEqualities
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        domain representation coordinate)
    (basis : MetricBasis.SymmetricMetricBasisRealization domain)
    (background : Chain.Background activity) : Set where
  field
    n00IsGR00 :
      Ten.stressInsertionNumeratorForComponent selected basis background K.component00
      ≡ + 1
    n01IsGR01 :
      Ten.stressInsertionNumeratorForComponent selected basis background K.component01
      ≡ 0ℚ
    n02IsGR02 :
      Ten.stressInsertionNumeratorForComponent selected basis background K.component02
      ≡ 0ℚ
    n03IsGR03 :
      Ten.stressInsertionNumeratorForComponent selected basis background K.component03
      ≡ 0ℚ
    n11IsGR11 :
      Ten.stressInsertionNumeratorForComponent selected basis background K.component11
      ≡ -[1+ zero ]
    n12IsGR12 :
      Ten.stressInsertionNumeratorForComponent selected basis background K.component12
      ≡ 0ℚ
    n13IsGR13 :
      Ten.stressInsertionNumeratorForComponent selected basis background K.component13
      ≡ 0ℚ
    n22IsGR22 :
      Ten.stressInsertionNumeratorForComponent selected basis background K.component22
      ≡ -[1+ zero ]
    n23IsGR23 :
      Ten.stressInsertionNumeratorForComponent selected basis background K.component23
      ≡ 0ℚ
    n33IsGR33 :
      Ten.stressInsertionNumeratorForComponent selected basis background K.component33
      ≡ -[1+ zero ]

open TenNormalizedGRTargetEqualities public

r119PairingReadout :
  ∀ {C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate Y group} →
  R119.CanonicalMetricSelectedStressWeld
    {C = C} {S = S} {Y = Y} {group = group}
    domain representation coordinate →
  Basis.RationalStressPairingReadout representation
r119PairingReadout selected = record
  { Basis.RationalStressPairingReadout.pairingToRational =
      R119.readoutToRational selected
  }

targetEqualitiesBuildNormalizedTenComponentInstance :
  ∀ {C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate Y group}
    {selected :
      R119.CanonicalMetricSelectedStressWeld
        {C = C} {S = S} {Y = Y} {group = group}
        domain representation coordinate}
    {basis : MetricBasis.SymmetricMetricBasisRealization domain}
    {background : Chain.Background activity} →
  TenNormalizedGRTargetEqualities selected basis background →
  Sym.NormalizedSymmetricTenComponentInstance
    (Basis.cmp119MetricBasisEvaluator
      (MetricBasis.compileSymmetricBasis16 basis)
      (r119PairingReadout selected))
    (StressRep.stressTensor representation)
targetEqualitiesBuildNormalizedTenComponentInstance
    {representation = representation}
    {selected = selected} {basis = basis} {background = background}
    payment = record
  { Sym.NormalizedSymmetricTenComponentInstance.symmetry =
      Sym.metricBasisEvaluatorIsComponentSymmetric
        basis (r119PairingReadout selected)
        (StressRep.stressTensor representation)
  ; Sym.NormalizedSymmetricTenComponentInstance.qft00 =
      trans
        (Ten.metricStressPairingReadoutIsInsertionNumerator
          selected basis background K.component00)
        (n00IsGR00 payment)
  ; Sym.NormalizedSymmetricTenComponentInstance.qft01 =
      trans
        (Ten.metricStressPairingReadoutIsInsertionNumerator
          selected basis background K.component01)
        (n01IsGR01 payment)
  ; Sym.NormalizedSymmetricTenComponentInstance.qft02 =
      trans
        (Ten.metricStressPairingReadoutIsInsertionNumerator
          selected basis background K.component02)
        (n02IsGR02 payment)
  ; Sym.NormalizedSymmetricTenComponentInstance.qft03 =
      trans
        (Ten.metricStressPairingReadoutIsInsertionNumerator
          selected basis background K.component03)
        (n03IsGR03 payment)
  ; Sym.NormalizedSymmetricTenComponentInstance.qft11 =
      trans
        (Ten.metricStressPairingReadoutIsInsertionNumerator
          selected basis background K.component11)
        (n11IsGR11 payment)
  ; Sym.NormalizedSymmetricTenComponentInstance.qft12 =
      trans
        (Ten.metricStressPairingReadoutIsInsertionNumerator
          selected basis background K.component12)
        (n12IsGR12 payment)
  ; Sym.NormalizedSymmetricTenComponentInstance.qft13 =
      trans
        (Ten.metricStressPairingReadoutIsInsertionNumerator
          selected basis background K.component13)
        (n13IsGR13 payment)
  ; Sym.NormalizedSymmetricTenComponentInstance.qft22 =
      trans
        (Ten.metricStressPairingReadoutIsInsertionNumerator
          selected basis background K.component22)
        (n22IsGR22 payment)
  ; Sym.NormalizedSymmetricTenComponentInstance.qft23 =
      trans
        (Ten.metricStressPairingReadoutIsInsertionNumerator
          selected basis background K.component23)
        (n23IsGR23 payment)
  ; Sym.NormalizedSymmetricTenComponentInstance.qft33 =
      trans
        (Ten.metricStressPairingReadoutIsInsertionNumerator
          selected basis background K.component33)
        (n33IsGR33 payment)
  }

targetEqualitiesCompileToFullTensorEquality :
  ∀ {C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate Y group}
    {selected :
      R119.CanonicalMetricSelectedStressWeld
        {C = C} {S = S} {Y = Y} {group = group}
        domain representation coordinate}
    {basis : MetricBasis.SymmetricMetricBasisRealization domain}
    {background : Chain.Background activity} →
  TenNormalizedGRTargetEqualities selected basis background →
  (a b : Flat.Axis4) →
  Cut.finiteGRStressRational a b
  ≡
  Cut.cmp119RationalTensor
    (Basis.cmp119MetricBasisEvaluator
      (MetricBasis.compileSymmetricBasis16 basis)
      (r119PairingReadout selected))
    (StressRep.stressTensor representation)
    a b
targetEqualitiesCompileToFullTensorEquality payment =
  Sym.tenSymmetricComponentsCompileToTensorEquality
    (targetEqualitiesBuildNormalizedTenComponentInstance payment)

additionalTensorTheoremAfterTenTargetEqualitiesRequired : Bool
additionalTensorTheoremAfterTenTargetEqualitiesRequired = false

additionalTensorTheoremAfterTenTargetEqualitiesRequiredIsFalse :
  additionalTensorTheoremAfterTenTargetEqualitiesRequired ≡ false
additionalTensorTheoremAfterTenTargetEqualitiesRequiredIsFalse = refl
