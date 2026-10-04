{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3R129RechartedLocalCF2Exact where

------------------------------------------------------------------------
-- R3 / R129 SAME-CARRIER ATTACHMENT AFTER THE LOCAL-C RECHART.
--
-- Once Local-C's operator map is chosen to be the marked-curvature compiler on
-- the already-shared R109 `Composite` carrier, the old field
--
--   selectedLocalCF2IsMarkedCurvatureF2
--
-- is definitional.  The only source-semantic statement left in the R129 F^2
-- attachment is that the selected marked F^2 source is the exact completed
-- source exported by R129.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyP3MarkedCurvatureLocalCRechartExact as Rechart
import DASHI.Physics.Foundations.CMP119AntigravityR129PinnedLocalCF2SameCarrierExact as Attachment

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanSectorQFTRecoveryExportRound129Exact as R129
import DASHI.Physics.YangMills.BalabanCanonicalMetricStressLaneRound120Exact as R120
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.YMClayLevel2SameFamilyStressRecoveryExact as Recovery
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119MarkedCurvatureCompositeExact as Curvature
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
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

  selected = R120.coordinate (R123.stressLane stressLane)
  completion = R114.asMarkedCompletion selected (R114.coordinate selected)
  compositeData = Recovery.r129ExportsCompositeMarkedSourceData export

  compileRechartedR129LocalCF2 :
    ∀ {Position CurvaturePolynomial OPECoefficient StressTensor Hamiltonian}
      (baseLocalC :
        Local.ContinuumLocalOperatorOPEStressTensor
          (Top.ContinuumMeasure C)
          CurvaturePolynomial (R109.Composite completion)
          Position OPECoefficient StressTensor Hamiltonian)
      (fieldStrengthSquarePolynomial : CurvaturePolynomial)
      (curvatureFamily :
        Curvature.MarkedCurvatureCompositeFamily
          CurvaturePolynomial Position
          (R109.continuityScale completion)
          (R109.CompletedState completion)
          (R109.Composite completion)) →
    Curvature.markedSource curvatureFamily fieldStrengthSquarePolynomial
      ≡ compositeData →
    Attachment.R129PinnedLocalCF2SameCarrier
      export
      (Rechart.rechartLocalCOnMarkedCurvature baseLocalC curvatureFamily)
  compileRechartedR129LocalCF2
      baseLocalC fieldStrengthSquarePolynomial curvatureFamily sourceIdentity = record
    { Attachment.R129PinnedLocalCF2SameCarrier.fieldStrengthSquarePolynomial =
        fieldStrengthSquarePolynomial
    ; Attachment.R129PinnedLocalCF2SameCarrier.curvatureFamily =
        curvatureFamily
    ; Attachment.R129PinnedLocalCF2SameCarrier.selectedF2MarkedSourceIsR129Source =
        sourceIdentity
    ; Attachment.R129PinnedLocalCF2SameCarrier.selectedLocalCF2IsMarkedCurvatureF2 =
        refl
    }

rechartedLocalCF2EqualityIsDefinitional : Bool
rechartedLocalCF2EqualityIsDefinitional = true

onlyR129MarkedSourceSelectionRemainsInSameCarrierAttachment : Bool
onlyR129MarkedSourceSelectionRemainsInSameCarrierAttachment = true
