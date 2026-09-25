{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityR129PinnedLocalCF2SameCarrierExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import DASHI.Physics.YangMills.CompactLieProofLevel

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
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119MarkedCurvatureCompositeExact as Curvature
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- AG-S2 / SAME-CARRIER R129 -> PINNED LOCAL-C F^2
--
-- Preferred specialization: use the R109 completed-composite carrier itself
-- as LocalOperator.  This removes the arbitrary post-hoc map
--
--     completed composite -> LocalOperator
--
-- from the earlier attachment.  The sole physical equality left is that the
-- selected Local-C F^2 operator is the completed marked-curvature F^2 operator.
------------------------------------------------------------------------

record R129PinnedLocalCF2SameCarrier
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
    {Position CurvaturePolynomial OPECoefficient StressTensor Hamiltonian : Set}
    (localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        (Top.ContinuumMeasure C)
        CurvaturePolynomial
        (R109.Composite
          (R114.asMarkedCompletion
            (R120.coordinate (R123.stressLane stressLane))
            (R114.coordinate (R120.coordinate (R123.stressLane stressLane)))))
        Position OPECoefficient StressTensor Hamiltonian) : Set₂ where

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

    selectedF2MarkedSourceIsR129Source :
      Curvature.markedSource curvatureFamily fieldStrengthSquarePolynomial
      ≡ compositeData

    selectedLocalCF2IsMarkedCurvatureF2 :
      Local.localOperator localC fieldStrengthSquarePolynomial
      ≡
      Curvature.localOperator curvatureFamily fieldStrengthSquarePolynomial

open R129PinnedLocalCF2SameCarrier public

selectedLocalCF2IsR129CompletedComposite :
  ∀ {trajectory split inputs C S Y group Scale Volume activity domain
      representation stressLane export Position CurvaturePolynomial
      OPECoefficient StressTensor Hamiltonian localC}
    (attachment :
      R129PinnedLocalCF2SameCarrier
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {C = C} {S = S} {Y = Y} {group = group}
        {Scale = Scale} {Volume = Volume} {activity = activity}
        {domain = domain} {representation = representation}
        {stressLane = stressLane}
        export
        {Position = Position}
        {CurvaturePolynomial = CurvaturePolynomial}
        {OPECoefficient = OPECoefficient}
        {StressTensor = StressTensor}
        {Hamiltonian = Hamiltonian}
        localC) →
  Local.localOperator localC (fieldStrengthSquarePolynomial attachment)
  ≡
  Marked.continuumComposite
    (Marked.sameFamilyMarkedSourceGivesNuclearCompositeField
      (Recovery.r129ExportsCompositeMarkedSourceData export))
selectedLocalCF2IsR129CompletedComposite
    {export = export} attachment =
  trans
    (selectedLocalCF2IsMarkedCurvatureF2 attachment)
    (subst
      (λ source →
        Curvature.localOperator
          (curvatureFamily attachment)
          (fieldStrengthSquarePolynomial attachment)
        ≡
        Marked.continuumComposite
          (Marked.sameFamilyMarkedSourceGivesNuclearCompositeField source))
      (selectedF2MarkedSourceIsR129Source attachment)
      (Relation.Binary.PropositionalEquality.refl))

r129PinnedLocalCF2SameCarrierCompilerLevel : ProofLevel
r129PinnedLocalCF2SameCarrierCompilerLevel = machineChecked

literalR129PinnedLocalCF2SameObjectLevel : ProofLevel
literalR129PinnedLocalCF2SameObjectLevel = conditional
