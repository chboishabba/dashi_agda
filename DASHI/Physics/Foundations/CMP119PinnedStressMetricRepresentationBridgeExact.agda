{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119PinnedStressMetricRepresentationBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanContinuumMetricStressPairingRound130Exact as R130
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as C
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119LiteralStressAttachmentExact as Attach
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR

------------------------------------------------------------------------
-- CMP119 EXPORTED STRESS -> LITERAL CLAY STRESS -> R130 METRIC STRESS
--
-- No fresh stress object or pairing law is introduced here.  The first equality
-- is the existing explicit CMP119/literal attachment.  The second is R130's
-- same-family literal-stress representation weld.
------------------------------------------------------------------------

record CMP119PinnedStressMetricRepresentationBridge
    {trajectory split}
    {densityInputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {Carriers : Top.LiteralYangMillsCarriers}
    {Semantics : Top.LiteralYangMillsSemantics Carriers}
    {Y : Top.LiteralYangMillsConstruction Carriers Semantics}
    {group : Top.CompactSimpleGroup Carriers}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = densityInputs}
      {C = Carriers} {S = Semantics} {Y = Y} {group = group}
      domain representation}
    {X Configuration Position CurvaturePolynomial LocalOperator OPECoefficient
     Hilbert Vector Algebra Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division S osInputs reconstruction}
    (inputs :
      C.PinnedCMP119ConcreteLocalCInputs
        (Top.CompactSimpleGroup Carriers)
        X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor Carriers)
        Hilbert Vector (Top.Hamiltonian Carriers) Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient}
        {division = division} {S = S}
        osInputs reconstruction group) : Set₁ where
  field
    literalAttachment :
      Attach.PinnedCMP119LiteralStressAttachment
        Y group inputs

    metricPairing :
      R130.ContinuumMetricStressPairingWeld stressLane

open CMP119PinnedStressMetricRepresentationBridge public

cmp119StressToMetricRepresentation :
  ∀ {trajectory split densityInputs Carriers Semantics Y group Scale Volume
      activity domain representation stressLane X Configuration Position
      CurvaturePolynomial LocalOperator OPECoefficient Hilbert Vector Algebra
      Root ContinuumFamily Core sequenceLimit limitLaws quotient division S
      osInputs reconstruction inputs} →
  CMP119PinnedStressMetricRepresentationBridge
    {trajectory = trajectory} {split = split} {densityInputs = densityInputs}
    {Carriers = Carriers} {Semantics = Semantics} {Y = Y} {group = group}
    {Scale = Scale} {Volume = Volume} {activity = activity}
    {domain = domain} {representation = representation}
    {stressLane = stressLane}
    {X = X} {Configuration = Configuration} {Position = Position}
    {CurvaturePolynomial = CurvaturePolynomial} {LocalOperator = LocalOperator}
    {OPECoefficient = OPECoefficient} {Hilbert = Hilbert} {Vector = Vector}
    {Algebra = Algebra} {Root = Root} {ContinuumFamily = ContinuumFamily}
    {Core = Core} {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
    {quotient = quotient} {division = division} {S = S}
    {osInputs = osInputs} {reconstruction = reconstruction}
    inputs →
  Top.StressTensor Carriers →
  StressRep.StressTensor representation
cmp119StressToMetricRepresentation bridge =
  R130.literalStressToRepresentation (metricPairing bridge)

cmp119EndpointStressIsCanonicalMetricStress :
  ∀ {trajectory split densityInputs Carriers Semantics Y group Scale Volume
      activity domain representation stressLane X Configuration Position
      CurvaturePolynomial LocalOperator OPECoefficient Hilbert Vector Algebra
      Root ContinuumFamily Core sequenceLimit limitLaws quotient division S
      osInputs reconstruction}
    {inputs :
      C.PinnedCMP119ConcreteLocalCInputs
        (Top.CompactSimpleGroup Carriers)
        X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor Carriers)
        Hilbert Vector (Top.Hamiltonian Carriers) Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient}
        {division = division} {S = S}
        osInputs reconstruction group}
    (bridge :
      CMP119PinnedStressMetricRepresentationBridge
        {trajectory = trajectory} {split = split} {densityInputs = densityInputs}
        {Carriers = Carriers} {Semantics = Semantics} {Y = Y} {group = group}
        {Scale = Scale} {Volume = Volume} {activity = activity}
        {domain = domain} {representation = representation}
        {stressLane = stressLane}
        inputs) →
  cmp119StressToMetricRepresentation bridge (C.stressTensor inputs)
  ≡ StressRep.stressTensor representation
cmp119EndpointStressIsCanonicalMetricStress bridge =
  trans
    (cong
      (cmp119StressToMetricRepresentation bridge)
      (Attach.cmp119StressIsLiteralStress (literalAttachment bridge)))
    (R130.literalStressIsFiniteRepresentationStress (metricPairing bridge))

secondEndpointToMetricStressIdentificationRequired : Bool
secondEndpointToMetricStressIdentificationRequired = false

secondEndpointToMetricStressIdentificationRequiredIsFalse :
  secondEndpointToMetricStressIdentificationRequired ≡ false
secondEndpointToMetricStressIdentificationRequiredIsFalse = refl
