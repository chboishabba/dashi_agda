{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR136LocalCSameStressExact where

------------------------------------------------------------------------
-- R136 CONTINUUM METRIC STRESS = PINNED CMP119 LOCAL-C STRESS.
--
-- Round130 maps the literal Clay stress
--
--   Top.stressTensor Y group
--
-- into the canonical metric stress representation and proves that this image
-- is the represented stress tensor.
--
-- Round109 independently proves on the SAME pinned CMP119 reconstruction:
--
--   Top.stressTensor Y group = LocalC.stressTensor localC.
--
-- Therefore the Local-C stress and the R136/R130 continuum metric stress are
-- the SAME stress object after the already-selected representation map.
--
-- This removes a major part of the Euclidean->Lorentzian producer: the
-- continuation theorem no longer needs to identify two unrelated stress
-- tensors.  It only needs to continue this one pinned Local-C/R136 stress into
-- its Lorentzian operator expectation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanContinuumMetricStressPairingRound130Exact as R130
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119Round109ConcreteLocalCExact as Round109
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

module _
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation}
    (metricWeld : R130.ContinuumMetricStressPairingWeld stressLane)
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = osS}
        osInputs reconstruction group)
    (round109 :
      Round109.Round109ConcreteLocalCStressWeld
        Y group localC)
  where

  representedLocalCStress :
    StressRep.StressTensor representation
  representedLocalCStress =
    R130.literalStressToRepresentation metricWeld
      (LocalC.stressTensor localC)

  representedLocalCStressIsCanonicalStress :
    representedLocalCStress
    ≡ StressRep.stressTensor representation
  representedLocalCStressIsCanonicalStress =
    trans
      (cong
        (R130.literalStressToRepresentation metricWeld)
        (sym
          (Round109.literalClayStressIsConcreteLocalCStress round109)))
      (R130.literalStressIsFiniteRepresentationStress metricWeld)

  completedResponseIsPinnedLocalCStressPairing :
    ∀ perturbation →
    Domain.AdmissibleMetricPerturbation domain perturbation →
    R130.continuumValueToPairingScalar metricWeld
      (R114.cmp119CompletedResponse
        (R130.selectedCoordinate metricWeld)
        (R130.metricPerturbationToNuclearTest metricWeld perturbation))
    ≡
    StressRep.stressMetricPairing representation
      representedLocalCStress perturbation
  completedResponseIsPinnedLocalCStressPairing perturbation admissible =
    trans
      (R130.completedStressFunctionalEqualsCanonicalStressPairing
        metricWeld perturbation admissible)
      (cong
        (λ stress →
          StressRep.stressMetricPairing representation
            stress perturbation)
        (sym representedLocalCStressIsCanonicalStress))

  sameLiteralStressObjectAlreadyProved : Bool
  sameLiteralStressObjectAlreadyProved = true

  euclideanStressIdentityNoLongerOpen : Bool
  euclideanStressIdentityNoLongerOpen = true
