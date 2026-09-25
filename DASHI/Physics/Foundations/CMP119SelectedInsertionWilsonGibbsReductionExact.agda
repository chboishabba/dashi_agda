{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SelectedInsertionWilsonGibbsReductionExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as Basis
import DASHI.Physics.Foundations.CMP119SymmetricCanonicalMetricRechartExact as Rechart
import DASHI.Physics.Foundations.CMP119WilsonGibbsFiniteMeasureSameObjectExact as Same
import DASHI.Physics.Foundations.CMP119AntigravitySelectedWilsonGibbsMinimalAnchorExact as Minimal
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- R119 SAME-OBJECT FIELD -> ONE SCALAR WILSON/GIBBS WELD
--
-- R119 already proves that the connected numerator selected by normalizedSource
-- is the numerator of the exact selected CMP119 stress insertion.  Therefore
-- the remaining Wilson/Gibbs source identification does NOT need to inspect the
-- whole normalized source record.
--
-- It is enough to identify, for each symmetric metric slot, the literal selected
-- CMP119 insertion numerator with the canonical Wilson/Gibbs connected
-- numerator on the chosen finite measure.
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

    selectedCMP119InsertionNumerator : ℚ
    selectedCMP119InsertionNumerator =
      R119.localInsertionNumerator rechartedSelected
        (Source.pair
          (R109.stressInsertion
            (R114.asCMP119Cauchy coordinate
              (R114.coordinate coordinate))))

    record SelectedInsertionWilsonGibbsScalarWeld : Set₁ where
      field
        selectedScale : Scale
        sourceScaleIndex : Scale → Nat

        selectedInsertionNumeratorIsWilsonGibbs :
          ∀ component →
          selectedCMP119InsertionNumerator
          ≡
          Same.wilsonFiniteMeasureConnectedNumerator
            measureWeld wilsonInsertion
            (Top.finiteMeasure Y group
              (R124.cutoffAtScale measureWeld
                (sourceScaleIndex selectedScale)))
            component

    open SelectedInsertionWilsonGibbsScalarWeld public

    selectedLiteralFiniteMeasure :
      SelectedInsertionWilsonGibbsScalarWeld →
      Top.FiniteMeasure C
    selectedLiteralFiniteMeasure weld =
      Top.finiteMeasure Y group
        (R124.cutoffAtScale measureWeld
          (sourceScaleIndex weld (selectedScale weld)))

    connectedNumeratorSameObjectFromSelectedInsertion :
      (weld : SelectedInsertionWilsonGibbsScalarWeld) →
      ∀ background component →
      R116.connectedInsertionNumerator
        (R119.normalizedSource
          rechartedSelected background component)
      ≡
      Same.wilsonFiniteMeasureConnectedNumerator
        measureWeld wilsonInsertion
        (selectedLiteralFiniteMeasure weld)
        component
    connectedNumeratorSameObjectFromSelectedInsertion
        weld background component =
      trans
        (R119.connectedInsertionIsSelectedCMP119StressInsertion
          rechartedSelected background component)
        (selectedInsertionNumeratorIsWilsonGibbs weld component)


------------------------------------------------------------------------
-- Direct constructor for the antigravity minimal anchor.
------------------------------------------------------------------------

module _
    {G X Cutoff Configuration Observable Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Hamiltonian VacuumState : Set}
    {trajectory split}
    {inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {S : Top.LiteralYangMillsSemantics
      (Physical.physicalLiteralCarriers
        G X Cutoff Configuration ℚ Observable Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        HilbertSpace Hamiltonian VacuumState)}
    {Y : Top.LiteralYangMillsConstruction
      (Physical.physicalLiteralCarriers
        G X Cutoff Configuration ℚ Observable Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        HilbertSpace Hamiltonian VacuumState) S}
    {group : Top.CompactSimpleGroup
      (Physical.physicalLiteralCarriers
        G X Cutoff Configuration ℚ Observable Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        HilbertSpace Hamiltonian VacuumState)}
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

  scalarWeldToMinimalAnchor :
    SelectedInsertionWilsonGibbsScalarWeld
      domain realization representation selected
      measureWeld wilsonInsertion →
    Minimal.MinimalSelectedWilsonGibbsAnchor
      domain realization representation selected
      measureWeld wilsonInsertion
  scalarWeldToMinimalAnchor weld = record
    { Minimal.MinimalSelectedWilsonGibbsAnchor.selectedScale =
        selectedScale weld
    ; Minimal.MinimalSelectedWilsonGibbsAnchor.sourceScaleIndex =
        sourceScaleIndex weld
    ; Minimal.MinimalSelectedWilsonGibbsAnchor.selectedConnectedNumeratorIsCanonicalWilsonGibbs =
        connectedNumeratorSameObjectFromSelectedInsertion
          domain realization representation selected
          measureWeld wilsonInsertion weld
    }
