{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPinnedLocalCTraceContinuationExact where

------------------------------------------------------------------------
-- PIN THE E->L TRACE CONTINUATION PRODUCER TO THE SAME LOCAL-C STRESS
-- AND THE SAME PINNED OS VACUUM.
--
-- Euclidean endpoint:
--   literal R136/R130 four-direction continuum stress pairing.
--
-- Lorentzian endpoint:
--   trace readout of LocalC.stressTensor localC in
--   OSR.reconstructedVacuum reconstruction group.
--
-- The only remaining continuation law is equality of those two readouts,
-- together with identification of the Lorentzian readout with the isotropic
-- trace used by the cosmology compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum
import DASHI.Physics.Foundations.CMP119CosmologyPinnedLocalCBoostCovarianceExact as BoostLocalC

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as StressLane
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact as R133
import DASHI.Physics.YangMills.BalabanPresentCutCanonicalMetricDomainRound134Exact as R134
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionStressScaleRound135Exact as R135
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionRecoveryRound136Exact as R136
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR

module _
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set}
    {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    {firstWeld : R133.UnifiedGeneratedActionFirstVariation actionWeld}
    {metricInputs : R134.PresentCutMetricSpecificInputs firstWeld}
    {representation : StressRep.CanonicalMetricStressRepresentation
      (R134.presentCutCanonicalMetricDomain metricInputs)}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {lane : StressLane.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      (R134.presentCutCanonicalMetricDomain metricInputs) representation}
    {scaleWeld : R135.UnifiedGeneratedActionStressScale lane}
    (recovery : R136.UnifiedGeneratedActionSectorRecovery scaleWeld)
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        (R134.presentCutCanonicalMetricDomain metricInputs)
        representation coordinate)
    (directions :
      Continuum.FourAdmittedMetricDirections
        (R134.presentCutCanonicalMetricDomain metricInputs))
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily Core
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
    (boostData :
      BoostLocalC.PinnedLocalCBoostCovariance
        Y group localC)
  where

  literalEuclideanTrace : ℚ
  literalEuclideanTrace =
    Continuum.literalStressFourDiagonalPairing
      recovery selected directions

  record PinnedLocalCTraceContinuation : Set₁ where
    field
      lorentzianTraceReadout :
        Vector → Top.StressTensor C → ℚ

      localCTraceIsIsotropicLorentzianTrace :
        lorentzianTraceReadout
          (OSR.reconstructedVacuum reconstruction group)
          (LocalC.stressTensor localC)
        ≡
        Vacuum.trace
          (BoostLocalC.lorentzianIsotropicStress boostData)

      sameLocalCStressEuclideanToLorentzian :
        lorentzianTraceReadout
          (OSR.reconstructedVacuum reconstruction group)
          (LocalC.stressTensor localC)
        ≡
        literalEuclideanTrace

  open PinnedLocalCTraceContinuation public

  isotropicTraceIsLiteralEuclideanTrace :
    PinnedLocalCTraceContinuation →
    Vacuum.trace
      (BoostLocalC.lorentzianIsotropicStress boostData)
    ≡ literalEuclideanTrace
  isotropicTraceIsLiteralEuclideanTrace continuation =
    trans
      (sym
        (localCTraceIsIsotropicLorentzianTrace continuation))
      (sameLocalCStressEuclideanToLorentzian continuation)

  euclideanEndpointIsLiteralR136Stress : Bool
  euclideanEndpointIsLiteralR136Stress = true

  lorentzianEndpointIsPinnedLocalCStressOnPinnedVacuum : Bool
  lorentzianEndpointIsPinnedLocalCStressOnPinnedVacuum = true
