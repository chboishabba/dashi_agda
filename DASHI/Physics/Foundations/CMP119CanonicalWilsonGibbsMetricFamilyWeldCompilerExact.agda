{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CanonicalWilsonGibbsMetricFamilyWeldCompilerExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as Basis
import DASHI.Physics.Foundations.CMP119SymmetricCanonicalMetricRechartExact as Rechart
import DASHI.Physics.Foundations.CMP119SymmetricWilsonGibbsAnchorConstructorExact as Anchor
import DASHI.Physics.Foundations.CMP119SelectedMetricInsertionFamilyWilsonGibbsExact as Family
import DASHI.Physics.Foundations.CMP119WilsonGibbsFiniteMeasureSameObjectExact as Same
import DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureStressSourceConstructorExact as FiniteSource
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanLiteralDensityNormalizedSourceRound121Exact as R121
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
-- CANONICAL SOURCE ANCHOR -> FULL MULTI-COMPONENT WILSON/GIBBS FAMILY WELD
--
-- The source-facing equality in `SelectedSourceCanonicalWilsonGibbsInput`
-- already identifies, component-by-component, the ACTUAL recharted R119
-- normalized source with the canonical Wilson/Gibbs finite-measure cross data.
--
-- The finite-measure constructor then proves definitionally that its connected
-- numerator is the canonical Wilson/Gibbs connected numerator on the literal
-- selected measure.  Hence the older multi-component family weld is compiler
-- output; it is not an additional physical payment.
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

    canonicalCalculus =
      Anchor.canonicalCalculus
        domain realization representation selected
        measureWeld wilsonInsertion

    canonicalSelectedMeasure :
      Anchor.SelectedSourceCanonicalWilsonGibbsInput
        domain realization representation selected
        measureWeld wilsonInsertion →
      Top.FiniteMeasure C
    canonicalSelectedMeasure input =
      Top.finiteMeasure Y group
        (R124.cutoffAtScale measureWeld
          (Anchor.sourceScaleIndex input (Anchor.selectedScale input)))

    selectedConnectedNumeratorIsCanonicalWilsonGibbs :
      (input :
        Anchor.SelectedSourceCanonicalWilsonGibbsInput
          domain realization representation selected
          measureWeld wilsonInsertion) →
      ∀ background component →
      R116.connectedInsertionNumerator
        (R119.normalizedSource rechartedSelected background component)
      ≡
      Same.wilsonFiniteMeasureConnectedNumerator
        measureWeld wilsonInsertion
        (canonicalSelectedMeasure input)
        component
    selectedConnectedNumeratorIsCanonicalWilsonGibbs input background component =
      trans
        (cong R116.connectedInsertionNumerator
          (Anchor.selectedNormalizedSourceIsCanonicalWilsonGibbs
            input background component))
        (trans
          (FiniteSource.connectedNumeratorAtBetaScaleIsFiniteMeasureNumerator
            canonicalCalculus
            (Anchor.sourceScaleIndex input (Anchor.selectedScale input))
            component)
          (Same.finiteMeasureCalculusIsWilsonGibbsConnectedNumerator
            measureWeld wilsonInsertion
            (canonicalSelectedMeasure input)
            component))

    compileSelectedMetricInsertionFamilyWilsonGibbsWeld :
      Anchor.SelectedSourceCanonicalWilsonGibbsInput
        domain realization representation selected
        measureWeld wilsonInsertion →
      Family.SelectedMetricInsertionFamilyWilsonGibbsWeld
        domain realization representation selected
        measureWeld wilsonInsertion
    compileSelectedMetricInsertionFamilyWilsonGibbsWeld input = record
      { Family.SelectedMetricInsertionFamilyWilsonGibbsWeld.selectedScale =
          Anchor.selectedScale input
      ; Family.SelectedMetricInsertionFamilyWilsonGibbsWeld.sourceScaleIndex =
          Anchor.sourceScaleIndex input
      ; Family.SelectedMetricInsertionFamilyWilsonGibbsWeld.selectedInsertionNumeratorAt =
          λ component →
            Same.wilsonFiniteMeasureConnectedNumerator
              measureWeld wilsonInsertion
              (canonicalSelectedMeasure input)
              component
      ; Family.SelectedMetricInsertionFamilyWilsonGibbsWeld.connectedNumeratorIsSelectedInsertionAt =
          selectedConnectedNumeratorIsCanonicalWilsonGibbs input
      ; Family.SelectedMetricInsertionFamilyWilsonGibbsWeld.selectedInsertionAtIsWilsonGibbs =
          λ component → refl
      }

metricFamilyWeldIsCompilerOutputFromCanonicalSourceAnchor : Bool
metricFamilyWeldIsCompilerOutputFromCanonicalSourceAnchor = true

remainingSameObjectPaymentIsSelectedNormalizedSourceEquality : Bool
remainingSameObjectPaymentIsSelectedNormalizedSourceEquality = true
