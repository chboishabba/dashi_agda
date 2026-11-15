{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkEntropyDensityExpansionMaxCutExact where

------------------------------------------------------------------------
-- BIRTHMARK / RESIDUAL-INFORMATION -> EFFECTIVE DENSITY -> EXPANSION MAX-CUT
--
-- This owner cross-pollinates the quantum-birthmark residual-information lane
-- with the already-complete CMP119 density/action/stress/cosmology lane.
--
-- It does NOT identify entropy density with curvature.  The declared route is
-- instead
--
--   history-sensitive residual sector
--     -> selected metric-dependent generated density/action
--     -> existing first metric variation / selected stress lane
--     -> existing continuum trace / vacuum active-stress lane
--     -> positive-G acceleration contribution.
--
-- The two exact model identifications introduced here are:
--   1. the selected residual sector maps to the SAME Round132 generated density;
--   2. its real trace readout is the SAME real trace already consumed by the
--      R136/CMP119 expansion compiler.
--
-- Once those equalities are supplied, the acceleration theorem below is a
-- direct reuse of existing repo machinery; no new entropic-force law, negative
-- Newton constant, or negative inertial mass is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _<ℝ_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Foundations.EntropyDensityExact as Density
import DASHI.Quantum.QuantumBirthmarkEntropyDensityGravityBridgeExact as Birthmark

import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as RealBridge
import DASHI.Physics.Foundations.CMP119CosmologyRealTraceToExpansionMaxCutExact as Expansion
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSMaxCutRootExact as Root
import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum
import DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanTerminalMaxCutExact as Terminal

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as StressLane
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact as R133
import DASHI.Physics.YangMills.BalabanPresentCutCanonicalMetricDomainRound134Exact as R134
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionStressScaleRound135Exact as R135
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionRecoveryRound136Exact as R136
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC

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
     Scale Volume RootType ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        Scale Volume RootType ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = osS}
        osInputs reconstruction group)
  where

  ----------------------------------------------------------------------
  -- Exact residual-sector instantiation into the existing action carrier.
  ----------------------------------------------------------------------

  record ResidualEffectiveDensityInstantiation (realTrace : ℝ) : Set₁ where
    field
      ResidualSector : Set
      selectedResidualSector : ResidualSector

      residualToGeneratedDensity :
        ResidualSector → BetaDensity.Density inputs

      selectedResidualSectorMapsToGeneratedDensity :
        residualToGeneratedDensity selectedResidualSector
        ≡ BetaDensity.densityAt inputs (R132.selectedDensityIndex actionWeld)

      residualTraceReadout : ResidualSector → ℝ

      residualTraceReadoutMatchesContinuumTrace :
        residualTraceReadout selectedResidualSector ≡ realTrace

  open ResidualEffectiveDensityInstantiation public

  selectedResidualSectorIsRound132Density :
    ∀ {realTrace} →
    (instantiation : ResidualEffectiveDensityInstantiation realTrace) →
    residualToGeneratedDensity instantiation
      (selectedResidualSector instantiation)
    ≡ BetaDensity.densityAt inputs (R132.selectedDensityIndex actionWeld)
  selectedResidualSectorIsRound132Density =
    selectedResidualSectorMapsToGeneratedDensity

  residualNegativeGivesRealTraceNegative :
    ∀ {realTrace} →
    (instantiation : ResidualEffectiveDensityInstantiation realTrace) →
    residualTraceReadout instantiation
      (selectedResidualSector instantiation) <ℝ 0ℝ →
    realTrace <ℝ 0ℝ
  residualNegativeGivesRealTraceNegative instantiation residualNegative =
    subst
      (λ value → value <ℝ 0ℝ)
      (residualTraceReadoutMatchesContinuumTrace instantiation)
      residualNegative

  ----------------------------------------------------------------------
  -- End-to-end reuse of the already-compiled CMP119 expansion consumer.
  ----------------------------------------------------------------------

  residualTraceNegativeForcesPositiveMatterAcceleration :
    (embedding : Embed.OrderedRationalRealEmbedding) →
    (realTrace : ℝ) →
    (instantiation : ResidualEffectiveDensityInstantiation realTrace) →
    (traceWeld :
      RealBridge.R136RealTraceReadoutWeld
        embedding
        (Root.literalContinuumTrace recovery selected directions localC)
        realTrace) →
    (root : Root.MarkedStressOSMaxCutRoot recovery selected directions localC) →
    (positiveGravityFactor : ℚ) →
    0ℚ < positiveGravityFactor →
    residualTraceReadout instantiation
      (selectedResidualSector instantiation) <ℝ 0ℝ →
    0ℚ <
      Vacuum.matterAccelerationContribution
        positiveGravityFactor
        (Terminal.lorentzianIsotropicStress
          (Root.reconstructedTerminalConsequences
            recovery selected directions localC root))
  residualTraceNegativeForcesPositiveMatterAcceleration
      embedding realTrace instantiation traceWeld root positiveGravityFactor
      factorPositive residualNegative =
    Expansion.realTraceNegativeForcesPositiveMatterAcceleration
      recovery selected directions localC
      embedding realTrace traceWeld root positiveGravityFactor factorPositive
      (residualNegativeGivesRealTraceNegative instantiation residualNegative)

  ----------------------------------------------------------------------
  -- Max-cut accounting.
  ----------------------------------------------------------------------

  densityMetricVariationStressRouteReused : Bool
  densityMetricVariationStressRouteReused = true

  vacuumActiveStressExpansionRouteReused : Bool
  vacuumActiveStressExpansionRouteReused = true

  formalCrossLaneCompositionClosed : Bool
  formalCrossLaneCompositionClosed = true

------------------------------------------------------------------------
-- Semantic/authority firewall.
------------------------------------------------------------------------

birthmarkPersistenceSuppliesResidualSectorSemantics : Bool
birthmarkPersistenceSuppliesResidualSectorSemantics =
  Birthmark.BirthmarkEntropyDensityBridge.quantumBirthmarkSuppliesHistorySensitiveResidualExample
    Birthmark.canonicalBirthmarkEntropyDensityBridge

residualDensityIsNotIdentifiedWithThermodynamicEntropy : Bool
residualDensityIsNotIdentifiedWithThermodynamicEntropy = true

entropyDensityStillDoesNotDirectlySourceCurvature : Bool
entropyDensityStillDoesNotDirectlySourceCurvature =
  Density.EntropyDensityAuthorityBoundary.entropyDensityDoesNotByItselfSourceCurvature
    Density.canonicalEntropyDensityAuthorityBoundary

negativeGravityConstantNotUsed : Bool
negativeGravityConstantNotUsed = true

negativeInertialMassNotUsed : Bool
negativeInertialMassNotUsed = true

birthmarkDoesNotByItselfFixResidualTraceSign : Bool
birthmarkDoesNotByItselfFixResidualTraceSign = true

interpretationBoundary : Bool
interpretationBoundary = true
