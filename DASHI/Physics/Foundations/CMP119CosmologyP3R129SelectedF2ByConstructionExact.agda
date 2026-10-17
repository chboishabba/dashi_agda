{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3R129SelectedF2ByConstructionExact where

------------------------------------------------------------------------
-- S3a SOURCE-FIRST RECUT.
--
-- R129 already exports the completed same-family marked-source datum consumed
-- by the cosmology/anomaly lane.  Therefore the selected F^2 source should not
-- first be placed in an arbitrary curvature-family map and then proved equal to
-- the R129 export.  Choose the selected source to BE the R129 export.
--
-- This removes only representation debt.  It does not prove that the chosen
-- polynomial/mark has the physical F^2 meaning, uniform source normalization,
-- or gauge/local semantics required by the physical application.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Foundations.CMP119CosmologyP3SelectedMarkedF2Exact as Selected

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanSectorQFTRecoveryExportRound129Exact as R129
import DASHI.Physics.YangMills.BalabanCanonicalMetricStressLaneRound120Exact as R120
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.YMClayLevel2SameFamilyStressRecoveryExact as Recovery
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

module _
    {trajectory split}
    {inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation}
    (export : R129.BalabanSectorQFTRecoveryExport stressLane)
  where

  private
    selected = R120.coordinate (R123.stressLane stressLane)
    completion = R114.asMarkedCompletion selected (R114.coordinate selected)
    r129Source = Recovery.r129ExportsCompositeMarkedSourceData export
    r129Composite =
      Marked.continuumComposite
        (Marked.sameFamilyMarkedSourceGivesNuclearCompositeField r129Source)

  compileR129SelectedF2 :
    ∀ {CurvaturePolynomial Position}
      (fieldStrengthSquarePolynomial : CurvaturePolynomial)
      (GaugeInvariant : R109.Composite completion → Set)
      (LocalAt : R109.Composite completion → Position → Set) →
    GaugeInvariant r129Composite →
    (∀ position → LocalAt r129Composite position) →
    Selected.SelectedMarkedF2Source
      CurvaturePolynomial Position
      (R109.continuityScale completion)
      (R109.CompletedState completion)
      (R109.Composite completion)
  compileR129SelectedF2
      fieldStrengthSquarePolynomial GaugeInvariant LocalAt
      gaugeInvariant local = record
    { Selected.SelectedMarkedF2Source.fieldStrengthSquarePolynomial =
        fieldStrengthSquarePolynomial
    ; Selected.SelectedMarkedF2Source.markedF2Source = r129Source
    ; Selected.SelectedMarkedF2Source.GaugeInvariant = GaugeInvariant
    ; Selected.SelectedMarkedF2Source.LocalAt = LocalAt
    ; Selected.SelectedMarkedF2Source.completedF2GaugeInvariant = gaugeInvariant
    ; Selected.SelectedMarkedF2Source.completedF2Local = local
    }

postHocR129MarkedSourceEqualityRequired : Bool
postHocR129MarkedSourceEqualityRequired = false

postHocLocalCF2OperatorEqualityRequired : Bool
postHocLocalCF2OperatorEqualityRequired = false

remainingS3aWorkIsSelectedPhysicalF2Semantics : Bool
remainingS3aWorkIsSelectedPhysicalF2Semantics = true
