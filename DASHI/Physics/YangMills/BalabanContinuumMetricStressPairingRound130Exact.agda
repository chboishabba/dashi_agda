{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanContinuumMetricStressPairingRound130Exact where

------------------------------------------------------------------------
-- ROUND130: NUCLEAR STRESS FUNCTIONAL -> CANONICAL METRIC PAIRING
--
-- Round114/129 correctly retain the continuum stress as a nuclear test-space
-- functional.  Common-metric QFT/GR consumers instead require h |-> <T,h>.
-- This module makes that representation transport explicit; it does not add a
-- convergence theorem or identify the two carriers by name alone.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanCanonicalMetricStressLaneRound120Exact as R120
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanCharacteristicNuclearContinuityTransportExact as Nuclear
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record ContinuumMetricStressPairingWeld
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
    (stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation) : Set₁ where
  field
    selectedCoordinate : R114.LiteralStressCoordinate Y group
    selectedCoordinateIsLaneCoordinate :
      selectedCoordinate ≡ R120.coordinate (R123.stressLane stressLane)

    literalStressToRepresentation :
      Top.StressTensor C → StressRep.StressTensor representation

    literalStressIsFiniteRepresentationStress :
      literalStressToRepresentation (Top.stressTensor Y group)
      ≡ StressRep.stressTensor representation

    metricPerturbationToNuclearTest :
      Domain.MetricPerturbation domain →
      let completion =
            R114.asMarkedCompletion selectedCoordinate
              (R114.coordinate selectedCoordinate)
      in Nuclear.Test (R109.continuityScale completion)

    continuumValueToPairingScalar :
      let completion =
            R114.asMarkedCompletion selectedCoordinate
              (R114.coordinate selectedCoordinate)
      in Nuclear.Value (R109.continuityScale completion) →
         StressRep.PairingScalar representation

    completedFunctionalRepresentsLiteralMetricPairing :
      ∀ perturbation →
      Domain.AdmissibleMetricPerturbation domain perturbation →
      continuumValueToPairingScalar
        (R114.cmp119CompletedResponse selectedCoordinate
          (metricPerturbationToNuclearTest perturbation))
      ≡ StressRep.stressMetricPairing representation
          (literalStressToRepresentation (Top.stressTensor Y group))
          perturbation

open ContinuumMetricStressPairingWeld public

completedStressFunctionalEqualsCanonicalStressPairing :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation}
    (weld : ContinuumMetricStressPairingWeld stressLane) →
  ∀ perturbation →
  Domain.AdmissibleMetricPerturbation domain perturbation →
  continuumValueToPairingScalar weld
    (R114.cmp119CompletedResponse (selectedCoordinate weld)
      (metricPerturbationToNuclearTest weld perturbation))
  ≡ StressRep.stressMetricPairing representation
      (StressRep.stressTensor representation) perturbation
completedStressFunctionalEqualsCanonicalStressPairing weld perturbation admissible
  rewrite literalStressIsFiniteRepresentationStress weld =
  completedFunctionalRepresentsLiteralMetricPairing weld perturbation admissible

continuumMetricStressPairingCompilerLevel : ProofLevel
continuumMetricStressPairingCompilerLevel = machineChecked

-- Physical representation seam: identify the literal metric perturbation with
-- the nuclear test insertion used by the completed marked source, identify the
-- literal Clay stress with the finite Round106 stress carrier, and prove the
-- displayed pairing compatibility.  No additional convergence estimate lives
-- here.
literalContinuumMetricStressPairingInstantiationLevel : ProofLevel
literalContinuumMetricStressPairingInstantiationLevel = conditional
