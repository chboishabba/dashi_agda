{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119TenNormalizedStressInsertionNumeratorsExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as MetricBasis
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- TEN LITERAL RATIONAL SOURCE-NATIVE STRESS INSERTION NUMERATORS
--
-- R119 already constructs one normalized source-derivative datum for every
-- admissible metric perturbation and proves its rational first-variation readout
-- is the selected CMP119 stress insertion.  Evaluate that existing object on
-- the ten symmetric metric directions.
------------------------------------------------------------------------

normalizedInsertionForComponent :
  ∀ {C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        {C = C} {S = S} {Y = Y} {group = group}
        domain representation coordinate)
    (basis : MetricBasis.SymmetricMetricBasisRealization domain)
    (background : Chain.Background activity) →
  K.SymmetricTensorComponent4 →
  R116.NormalizedSourceDerivativeCrossData
normalizedInsertionForComponent selected basis background component =
  R119.normalizedSource selected background
    (MetricBasis.componentPerturbation basis component)

stressInsertionNumeratorForComponent :
  ∀ {C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        {C = C} {S = S} {Y = Y} {group = group}
        domain representation coordinate)
    (basis : MetricBasis.SymmetricMetricBasisRealization domain)
    (background : Chain.Background activity) →
  K.SymmetricTensorComponent4 →
  ℚ
stressInsertionNumeratorForComponent selected basis background component =
  R116.sourceDerivativeCrossNumerator
    (normalizedInsertionForComponent selected basis background component)

record TenNormalizedStressInsertionNumerators : Set where
  constructor tenNormalizedStressInsertionNumerators
  field
    n00 n01 n02 n03 n11 n12 n13 n22 n23 n33 : ℚ

open TenNormalizedStressInsertionNumerators public

evaluateTenNormalizedStressInsertionNumerators :
  ∀ {C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        {C = C} {S = S} {Y = Y} {group = group}
        domain representation coordinate)
    (basis : MetricBasis.SymmetricMetricBasisRealization domain)
    (background : Chain.Background activity) →
  TenNormalizedStressInsertionNumerators
evaluateTenNormalizedStressInsertionNumerators selected basis background =
  tenNormalizedStressInsertionNumerators
    (stressInsertionNumeratorForComponent selected basis background K.component00)
    (stressInsertionNumeratorForComponent selected basis background K.component01)
    (stressInsertionNumeratorForComponent selected basis background K.component02)
    (stressInsertionNumeratorForComponent selected basis background K.component03)
    (stressInsertionNumeratorForComponent selected basis background K.component11)
    (stressInsertionNumeratorForComponent selected basis background K.component12)
    (stressInsertionNumeratorForComponent selected basis background K.component13)
    (stressInsertionNumeratorForComponent selected basis background K.component22)
    (stressInsertionNumeratorForComponent selected basis background K.component23)
    (stressInsertionNumeratorForComponent selected basis background K.component33)

metricStressPairingReadoutIsInsertionNumerator :
  ∀ {C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        {C = C} {S = S} {Y = Y} {group = group}
        domain representation coordinate)
    (basis : MetricBasis.SymmetricMetricBasisRealization domain)
    (background : Chain.Background activity)
    (component : K.SymmetricTensorComponent4) →
  R119.readoutToRational selected
    (StressRep.stressMetricPairing representation
      (StressRep.stressTensor representation)
      (MetricBasis.componentPerturbation basis component))
  ≡ stressInsertionNumeratorForComponent selected basis background component
metricStressPairingReadoutIsInsertionNumerator
    {representation = representation}
    selected basis background component =
  let
    perturbation = MetricBasis.componentPerturbation basis component
    admissible = MetricBasis.componentPerturbationAdmissible basis component
    represented =
      StressRep.admittedMetricVariationEqualsStressPairing
        representation background perturbation admissible
    sourceWeld =
      R119.canonicalMetricVariationIsExactSelectedCMP119StressInsertion
        selected background perturbation admissible
  in
  trans
    (sym (cong (R119.readoutToRational selected) represented))
    sourceWeld

tenRationalStressInsertionTermsAreDefined : Bool
tenRationalStressInsertionTermsAreDefined = true

tenRationalStressInsertionTermsAreDefinedIsTrue :
  tenRationalStressInsertionTermsAreDefined ≡ true
tenRationalStressInsertionTermsAreDefinedIsTrue = refl

tenNormalizedGRTargetEqualitiesStillRequired : Bool
tenNormalizedGRTargetEqualitiesStillRequired = true

tenNormalizedGRTargetEqualitiesStillRequiredIsTrue :
  tenNormalizedGRTargetEqualitiesStillRequired ≡ true
tenNormalizedGRTargetEqualitiesStillRequiredIsTrue = refl
