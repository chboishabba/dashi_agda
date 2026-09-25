{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SelectedMetricInsertionFamilyWilsonGibbsExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as Basis
import DASHI.Physics.Foundations.CMP119SymmetricCanonicalMetricRechartExact as Rechart
import DASHI.Physics.Foundations.CMP119WilsonGibbsFiniteMeasureSameObjectExact as Same
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- CORRECTED SAME-OBJECT SURFACE: THE STRESS INSERTION IS A METRIC-SLOT FAMILY
--
-- R119's historical localInsertionNumerator is one scalar attached to one
-- source-native insertion pair.  That shape is sufficient for a single selected
-- stress direction, but it is not a valid ten-component family by itself.
--
-- The antigravity trace needs four different metric directions.  Therefore the
-- exact physical same-object datum must be indexed by the symmetric metric slot:
--
--   h |-> selected CMP119 insertion numerator for h.
--
-- This record is deliberately the least-privilege correction.  It does not
-- alter R119; it states the additional physical family theorem required when
-- R119 is consumed simultaneously in several metric directions.
------------------------------------------------------------------------

module _
    {G X Cutoff Configuration Observable Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Hamiltonian VacuumState : Set}
  where

  C : Top.LiteralYangMillsCarriers
  C =
    Physical.physicalLiteralCarriers
      G X Cutoff Configuration ℚ Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState

  module _
      {trajectory split}
      {inputs : Beta.BetaDrivenCompleteDensityInputs
        {trajectory = trajectory} {split = split}}
      {S : Top.LiteralYangMillsSemantics C}
      {Y : Top.LiteralYangMillsConstruction C S}
      {group : Top.CompactSimpleGroup C}
      {Scale Volume : Set}
      {activity : Chain.SubstitutedActivitySecondVariation}
      (domain : Domain.CanonicalMetricSourceDomain Scale Volume activity)
      (realization : Basis.SymmetricMetricBasisRealization domain)
      (representation : StressRep.CanonicalMetricStressRepresentation domain)
      {coordinate : R114.LiteralStressCoordinate Y group}
      (selected :
        R119.CanonicalMetricSelectedStressWeld
          domain representation coordinate)
      (measureWeld :
        R124.BalabanDensityLiteralFiniteMeasureWeld
          {trajectory = trajectory} {split = split} {inputs = inputs}
          Y group)
      (wilsonInsertion :
        Wilson.ClassicalWilsonSelectedInsertion Configuration)
    where

    rechartedSelected =
      Rechart.rechartedSelectedStress
        domain realization representation selected

    record SelectedMetricInsertionFamilyWilsonGibbsWeld : Set₁ where
      field
        selectedScale : Scale
        sourceScaleIndex : Scale → Nat

        selectedInsertionNumeratorAt :
          K.SymmetricTensorComponent4 → ℚ

        connectedNumeratorIsSelectedInsertionAt :
          ∀ background component →
          R116.connectedInsertionNumerator
            (R119.normalizedSource
              rechartedSelected background component)
          ≡ selectedInsertionNumeratorAt component

        selectedInsertionAtIsWilsonGibbs :
          ∀ component →
          selectedInsertionNumeratorAt component
          ≡
          Same.wilsonFiniteMeasureConnectedNumerator
            measureWeld wilsonInsertion
            (Top.finiteMeasure Y group
              (R124.cutoffAtScale measureWeld
                (sourceScaleIndex selectedScale)))
            component

    open SelectedMetricInsertionFamilyWilsonGibbsWeld public

    selectedLiteralFiniteMeasure :
      SelectedMetricInsertionFamilyWilsonGibbsWeld →
      Top.FiniteMeasure C
    selectedLiteralFiniteMeasure weld =
      Top.finiteMeasure Y group
        (R124.cutoffAtScale measureWeld
          (sourceScaleIndex weld (selectedScale weld)))

    selectedConnectedNumeratorIsWilsonGibbs :
      (weld : SelectedMetricInsertionFamilyWilsonGibbsWeld) →
      ∀ background component →
      R116.connectedInsertionNumerator
        (R119.normalizedSource
          rechartedSelected background component)
      ≡
      Same.wilsonFiniteMeasureConnectedNumerator
        measureWeld wilsonInsertion
        (selectedLiteralFiniteMeasure weld)
        component
    selectedConnectedNumeratorIsWilsonGibbs weld background component =
      trans
        (connectedNumeratorIsSelectedInsertionAt weld background component)
        (selectedInsertionAtIsWilsonGibbs weld component)
