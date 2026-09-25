{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SelectedWilsonDiagonalCoordinateAnchorExact where

open import Data.Rational.Base using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)

import DASHI.Physics.Foundations.CMP119SelectedWilsonGibbsAnchorExact as Selected
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson
import DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureStressSourceConstructorExact as FiniteSource
import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- ONE SYMMETRIC-SLOT ROUND-TRIP WELD
--
-- The present-cut finite tangent is already definitionally
-- SymmetricTensorComponent4.  The selected source is already anchored to the
-- canonical Wilson/Gibbs finite-measure calculus.  Therefore the only remaining
-- coordinate issue is whether the metric perturbation chosen for a symmetric
-- slot is sent back by the R122 finite-measure perturbation map to that SAME
-- slot.
--
-- One forall-over-slots theorem pays all ten coordinates at once; the
-- antigravity consumer below uses only 00,11,22,33.
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
      {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
      {representation : StressRep.CanonicalMetricStressRepresentation domain}
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
      (anchor :
        Selected.SelectedWilsonGibbsAnchor
          selected measureWeld wilsonInsertion)
    where

    record SymmetricSlotRoundTripAnchor : Set₁ where
      field
        metricPerturbationOf :
          K.SymmetricTensorComponent4 →
          Domain.MetricPerturbation domain

        finiteMeasureRoundTrip :
          ∀ component →
          Selected.selectedWilsonPerturbation
            selected measureWeld wilsonInsertion
            anchor
            (metricPerturbationOf component)
          ≡ component

    open SymmetricSlotRoundTripAnchor public

    selectedComponentNumerator :
      SymmetricSlotRoundTripAnchor →
      Chain.Background activity →
      K.SymmetricTensorComponent4 →
      ℚ
    selectedComponentNumerator coordinateAnchor background component =
      Selected.selectedCMP119ConnectedNumerator
        selected measureWeld wilsonInsertion
        background
        (metricPerturbationOf coordinateAnchor component)

    wilsonComponentNumerator :
      K.SymmetricTensorComponent4 →
      ℚ
    wilsonComponentNumerator component =
      let
        measure =
          Selected.selectedLiteralFiniteMeasure
            selected measureWeld wilsonInsertion anchor
      in
      DASHI.Physics.Foundations.CMP119PhysicalFiniteMeasureNZDNDZExact.connectedCrossNumerator
        (DASHI.Physics.Foundations.CMP119GibbsFiniteMeasureNZDNDZReductionExact.asPhysicalMetricStressData
          (Wilson.asGibbsMetricInsertionData
            {measure = measure}
            wilsonInsertion))
        component

    selectedComponentIsWilsonComponent :
      (coordinateAnchor : SymmetricSlotRoundTripAnchor) →
      ∀ background component →
      selectedComponentNumerator coordinateAnchor background component
      ≡ wilsonComponentNumerator component
    selectedComponentIsWilsonComponent coordinateAnchor background component =
      trans
        (Selected.selectedCMP119ConnectedNumeratorIsWilsonGibbs
          selected measureWeld wilsonInsertion
          anchor background
          (metricPerturbationOf coordinateAnchor component))
        (cong wilsonComponentNumerator
          (finiteMeasureRoundTrip coordinateAnchor component))

    selectedDiagonalActiveSum :
      SymmetricSlotRoundTripAnchor →
      Chain.Background activity →
      ℚ
    selectedDiagonalActiveSum coordinateAnchor background =
      selectedComponentNumerator coordinateAnchor background K.component00
      + selectedComponentNumerator coordinateAnchor background K.component11
      + selectedComponentNumerator coordinateAnchor background K.component22
      + selectedComponentNumerator coordinateAnchor background K.component33

    wilsonDiagonalActiveSum : ℚ
    wilsonDiagonalActiveSum =
      wilsonComponentNumerator K.component00
      + wilsonComponentNumerator K.component11
      + wilsonComponentNumerator K.component22
      + wilsonComponentNumerator K.component33

    selectedDiagonalActiveSumIsWilsonDiagonalActiveSum :
      (coordinateAnchor : SymmetricSlotRoundTripAnchor) →
      ∀ background →
      selectedDiagonalActiveSum coordinateAnchor background
      ≡ wilsonDiagonalActiveSum
    selectedDiagonalActiveSumIsWilsonDiagonalActiveSum
        coordinateAnchor background
      rewrite selectedComponentIsWilsonComponent
          coordinateAnchor background K.component00
            | selectedComponentIsWilsonComponent
          coordinateAnchor background K.component11
            | selectedComponentIsWilsonComponent
          coordinateAnchor background K.component22
            | selectedComponentIsWilsonComponent
          coordinateAnchor background K.component33 =
      Relation.Binary.PropositionalEquality.refl
