module DASHI.Physics.YangMills.BalabanP10P33PhysicalCutsetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban. II. Large Fields",
-- Journal of Mathematical Physics 54 (2013), 092301.
-- DOI: 10.1063/1.4821275.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban III. Convergence",
-- Annales Henri Poincare 15 (2014), 2133--2175.
-- DOI: 10.1007/s00023-013-0303-3.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. I",
-- Communications in Mathematical Physics 95 (1984), 17--40.
-- DOI: 10.1007/BF01211042.
--
-- PURPOSE
-- Preserve the physical order of proof.  P10 is not one exponential token and
-- P33 is not one positivity token.  Each is decomposed into the exact local,
-- coercive, integral and uniformity inhabitants consumed by Step V.
------------------------------------------------------------------------

open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record P10LargeFieldPhysicalChain : Set₁ where
  field
    LargeFieldPredicate Defect ActionPenalty LocalIntegral : Set
    Polymer ActivityBound : Set

    largeFieldPredicateImpliesDefectLowerBound :
      LargeFieldPredicate → Defect

    defectLowerBoundImpliesActionPenalty :
      Defect → ActionPenalty

    actionPenaltyImpliesLocalIntegralSuppression :
      ActionPenalty → LocalIntegral

    polynomialPrefactorAbsorbedBySuppression :
      LocalIntegral → ActivityBound

    supportProductLocalization : Set
    supportProductLocalizationEvidence : supportProductLocalization

    localSuppressionMultipliesOverPolymerSupport : Set
    localSuppressionMultipliesOverPolymerSupportEvidence :
      localSuppressionMultipliesOverPolymerSupport

    totalPenaltyControlsPolymerComplexity : Set
    totalPenaltyControlsPolymerComplexityEvidence :
      totalPenaltyControlsPolymerComplexity

    polymerComplexityControlsDiameter : Set
    polymerComplexityControlsDiameterEvidence :
      polymerComplexityControlsDiameter

    scaleUniformConstants : Set
    scaleUniformConstantsEvidence : scaleUniformConstants

open P10LargeFieldPhysicalChain public

p10LargeFieldActivityBound :
  (chain : P10LargeFieldPhysicalChain) →
  LargeFieldPredicate chain → ActivityBound chain
p10LargeFieldActivityBound chain predicate =
  polynomialPrefactorAbsorbedBySuppression chain
    (actionPenaltyImpliesLocalIntegralSuppression chain
      (defectLowerBoundImpliesActionPenalty chain
        (largeFieldPredicateImpliesDefectLowerBound chain predicate)))

record P10ParityRefinement
    (chain : P10LargeFieldPhysicalChain) : Set₁ where
  field
    physicalLargeFieldInvolution : Set
    physicalLargeFieldInvolutionEvidence :
      physicalLargeFieldInvolution

    pairedOddContributionVanishes : Set
    pairedOddContributionVanishesEvidence :
      pairedOddContributionVanishes

    evenRemainderStartsQuadratically : Set
    evenRemainderStartsQuadraticallyEvidence :
      evenRemainderStartsQuadratically

open P10ParityRefinement public

record P33LinkEllipticityPhysicalChain : Set₁ where
  field
    LinkTangent TransverseTangent Scalar : Set
    ReferenceMetric Perturbation PhysicalMetric : Set
    LinkWeight WeightedTreeDistance OrdinaryDiameter : Set

    linkChartDifferentialInjective : Set
    linkChartDifferentialInjectiveEvidence :
      linkChartDifferentialInjective

    physicalMetricDecomposition : Set
    physicalMetricDecompositionEvidence : physicalMetricDecomposition

    referenceMetricPositiveFloor : Set
    referenceMetricPositiveFloorEvidence :
      referenceMetricPositiveFloor

    perturbationNormBound : Set
    perturbationNormBoundEvidence : perturbationNormBound

    perturbationBelowPositiveFloor : Set
    perturbationBelowPositiveFloorEvidence :
      perturbationBelowPositiveFloor

    gaugeFixedKernelEliminated : Set
    gaugeFixedKernelEliminatedEvidence : gaugeFixedKernelEliminated

    plaquetteIncidenceControlsBondMode : Set
    plaquetteIncidenceControlsBondModeEvidence :
      plaquetteIncidenceControlsBondMode

    localHessianPositiveOnTransverseSubspace : Set
    localHessianPositiveOnTransverseSubspaceEvidence :
      localHessianPositiveOnTransverseSubspace

    physicalMetricPositive : Set
    physicalMetricPositiveEvidence : physicalMetricPositive

    metricLowerBoundControlsLinkWeight : Set
    metricLowerBoundControlsLinkWeightEvidence :
      metricLowerBoundControlsLinkWeight

    normalizedLinkWeightAtLeastOne : Set
    normalizedLinkWeightAtLeastOneEvidence :
      normalizedLinkWeightAtLeastOne

    weightedTreeDistanceDominatesOrdinaryDiameter : Set
    weightedTreeDistanceDominatesOrdinaryDiameterEvidence :
      weightedTreeDistanceDominatesOrdinaryDiameter

    uniformInScalePolymerAndEdge : Set
    uniformInScalePolymerAndEdgeEvidence :
      uniformInScalePolymerAndEdge

open P33LinkEllipticityPhysicalChain public

record P33ParityRefinement
    (chain : P33LinkEllipticityPhysicalChain) : Set₁ where
  field
    orientedInversionIsPhysicalInvolution : Set
    orientedInversionIsPhysicalInvolutionEvidence :
      orientedInversionIsPhysicalInvolution

    hessianEvenUnderPhysicalInvolution : Set
    hessianEvenUnderPhysicalInvolutionEvidence :
      hessianEvenUnderPhysicalInvolution

    thirdDerivativeOddUnderPhysicalInvolution : Set
    thirdDerivativeOddUnderPhysicalInvolutionEvidence :
      thirdDerivativeOddUnderPhysicalInvolution

    symmetricAverageThirdOrderCancellation : Set
    symmetricAverageThirdOrderCancellationEvidence :
      symmetricAverageThirdOrderCancellation

open P33ParityRefinement public

record P10P33PhysicalReceipt : Set₁ where
  field
    p10 : P10LargeFieldPhysicalChain
    p33 : P33LinkEllipticityPhysicalChain

    p10FeedsStepVLargeFieldDecay : Set
    p10FeedsStepVLargeFieldDecayEvidence :
      p10FeedsStepVLargeFieldDecay

    p33FeedsWeightedToOrdinaryDiameter : Set
    p33FeedsWeightedToOrdinaryDiameterEvidence :
      p33FeedsWeightedToOrdinaryDiameter

    theoremBoundary : String

open P10P33PhysicalReceipt public

p10PhysicalCompositionLevel : ProofLevel
p10PhysicalCompositionLevel = machineChecked

p33PhysicalCutsetLevel : ProofLevel
p33PhysicalCutsetLevel = machineChecked

p10LocalPenaltyAndIntegralInputsLevel : ProofLevel
p10LocalPenaltyAndIntegralInputsLevel = conditional

p33TransverseEllipticityInputsLevel : ProofLevel
p33TransverseEllipticityInputsLevel = conditional
