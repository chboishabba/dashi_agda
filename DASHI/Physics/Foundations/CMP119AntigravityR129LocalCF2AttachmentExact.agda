{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityR129LocalCF2AttachmentExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
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
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119MarkedCurvatureCompositeExact as Curvature
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- R129 COMPLETED COMPOSITE -> PINNED LOCAL-C F^2
--
-- R129 already owns the SAME completed composite state used by the recovered
-- stress lane.  MarkedCurvatureCompositeFamily already compiles a selected
-- curvature-polynomial marked source into a nuclear-continuous local operator.
--
-- Antigravity therefore does not need another composite-field construction.
-- The remaining F^2 physics is one semantic attachment:
--
--   selected polynomial = physical F^2 polynomial,
--   its R129 completed marked composite = the pinned Local-C local operator.
------------------------------------------------------------------------

record R129PinnedLocalCF2Attachment
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
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
    {Position CurvaturePolynomial LocalOperator OPECoefficient
     StressTensor Hamiltonian : Set}
    (localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        (Top.ContinuumMeasure C)
        CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian) : Set₂ where

  private
    selected = R120.coordinate (R123.stressLane stressLane)
    completion = R114.asMarkedCompletion selected (R114.coordinate selected)
    compositeData = Recovery.r129ExportsCompositeMarkedSourceData export

  field
    fieldStrengthSquarePolynomial : CurvaturePolynomial

    curvatureFamily :
      Curvature.MarkedCurvatureCompositeFamily
        CurvaturePolynomial Position
        (R109.continuityScale completion)
        (R109.CompletedState completion)
        (R109.Composite completion)

    curvatureFamilyUsesR129CompletedSource :
      ∀ polynomial →
      Curvature.markedSource curvatureFamily polynomial
      ≡ compositeData

    operatorOfCompletedComposite :
      R109.Composite completion → LocalOperator

    localOperatorIsR129CompletedF2 :
      Local.localOperator localC fieldStrengthSquarePolynomial
      ≡
      operatorOfCompletedComposite
        (Marked.compositeProjection compositeData
          (Marked.completedState compositeData))

open R129PinnedLocalCF2Attachment public

r129LocalCF2CompletionCompilerLevel : ProofLevel
r129LocalCF2CompletionCompilerLevel = machineChecked

-- The completion is not open.  The physical content is exactly the semantic
-- identification of the chosen F^2 marked source/operator with the pinned
-- Local-C operator on this same R129 family.
physicalR129LocalCF2SemanticAttachmentLevel : ProofLevel
physicalR129LocalCF2SemanticAttachmentLevel = conditional
