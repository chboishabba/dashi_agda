{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySelectedWilsonGibbsMinimalAnchorExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as Basis
import DASHI.Physics.Foundations.CMP119SymmetricCanonicalMetricRechartExact as Rechart
import DASHI.Physics.Foundations.CMP119WilsonGibbsFiniteMeasureSameObjectExact as Same
import DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureStressSourceConstructorExact as FiniteSource
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson
import DASHI.Physics.Foundations.CMP119PhysicalFiniteMeasureNZDNDZExact as NZ
import DASHI.Physics.Foundations.CMP119GibbsFiniteMeasureNZDNDZReductionExact as Gibbs
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
-- LEAST-PRIVILEGE SELECTED CMP119 -> WILSON/GIBBS ANCHOR
--
-- The general R122 route asks for equality of the whole normalized-source
-- record.  The antigravity trace consumer does not need that much structure.
-- It consumes only the connected numerator.
--
-- Therefore the shortest physical same-object theorem is one forall-over-slots
-- equality of the connected numerator on the selected CMP119 source with the
-- canonical Wilson/Gibbs connected numerator on the same selected finite
-- measure.
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

    record MinimalSelectedWilsonGibbsAnchor : Set₁ where
      field
        selectedScale : Scale
        sourceScaleIndex : Scale → Nat

        selectedConnectedNumeratorIsCanonicalWilsonGibbs :
          ∀ background component →
          R116.connectedInsertionNumerator
            (R119.normalizedSource
              rechartedSelected background component)
          ≡
          Same.wilsonFiniteMeasureConnectedNumerator
            measureWeld wilsonInsertion
            (Top.finiteMeasure Y group
              (R124.cutoffAtScale measureWeld
                (sourceScaleIndex selectedScale)))
            component

    open MinimalSelectedWilsonGibbsAnchor public

    selectedLiteralFiniteMeasure :
      MinimalSelectedWilsonGibbsAnchor →
      Top.FiniteMeasure C
    selectedLiteralFiniteMeasure anchor =
      Top.finiteMeasure Y group
        (R124.cutoffAtScale measureWeld
          (sourceScaleIndex anchor (selectedScale anchor)))

    selectedComponentNumerator :
      Chain.Background activity →
      K.SymmetricTensorComponent4 →
      ℚ
    selectedComponentNumerator background component =
      R116.connectedInsertionNumerator
        (R119.normalizedSource
          rechartedSelected background component)

    wilsonComponentNumerator :
      MinimalSelectedWilsonGibbsAnchor →
      K.SymmetricTensorComponent4 →
      ℚ
    wilsonComponentNumerator anchor component =
      Same.wilsonFiniteMeasureConnectedNumerator
        measureWeld wilsonInsertion
        (selectedLiteralFiniteMeasure anchor)
        component

    selectedComponentIsWilsonComponent :
      (anchor : MinimalSelectedWilsonGibbsAnchor) →
      ∀ background component →
      selectedComponentNumerator background component
      ≡ wilsonComponentNumerator anchor component
    selectedComponentIsWilsonComponent anchor =
      selectedConnectedNumeratorIsCanonicalWilsonGibbs anchor

    selectedDiagonalActiveSum :
      Chain.Background activity →
      ℚ
    selectedDiagonalActiveSum background =
      selectedComponentNumerator background K.component00
      + selectedComponentNumerator background K.component11
      + selectedComponentNumerator background K.component22
      + selectedComponentNumerator background K.component33

    wilsonDiagonalActiveSum :
      MinimalSelectedWilsonGibbsAnchor →
      ℚ
    wilsonDiagonalActiveSum anchor =
      wilsonComponentNumerator anchor K.component00
      + wilsonComponentNumerator anchor K.component11
      + wilsonComponentNumerator anchor K.component22
      + wilsonComponentNumerator anchor K.component33

    selectedDiagonalActiveSumIsWilsonDiagonalActiveSum :
      (anchor : MinimalSelectedWilsonGibbsAnchor) →
      ∀ background →
      selectedDiagonalActiveSum background
      ≡ wilsonDiagonalActiveSum anchor
    selectedDiagonalActiveSumIsWilsonDiagonalActiveSum anchor background
      rewrite selectedComponentIsWilsonComponent anchor background K.component00
            | selectedComponentIsWilsonComponent anchor background K.component11
            | selectedComponentIsWilsonComponent anchor background K.component22
            | selectedComponentIsWilsonComponent anchor background K.component33 =
      refl
