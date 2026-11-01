module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound6ExactCutset where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact unresolved cutset after the round-six analytic reductions.
--
-- This cutset is deliberately local.  It no longer asks for broad contour,
-- Hessian, polymer or fluctuation theorems where the new modules have reduced
-- those statements to coefficient, support, norm and source-dictionary data.
------------------------------------------------------------------------

record CMP109Round6Cutset : Set₁ where
  field
    executableWordHolonomyIdentification : Set
    rectangleCurvatureProductIdentification : Set
    adjacentSwapCurvatureEstimate : Set
    sixSwapBoundInsideGroupAverageDiameter : Set
    principalLogChartOnAveragedContour : Set

open CMP109Round6Cutset public

record BishopRound6Cutset : Set₁ where
  field
    halfBallSquareBelowQuarter : Set
    sineCoefficientRecurrence : Set
    cosineCoefficientRecurrence : Set
    sineAlternatingFirstOmittedTail : Set
    cosineAlternatingFirstOmittedTail : Set
    inverseDexpBernoulliTail : Set
    coefficientDifferenceTermBounds : Set
    orderClosedPowerSeriesLimit : Set
    normalizedSineHaarIdentification : Set
    scalarHaarLogRemainder : Set

open BishopRound6Cutset public

record FederbushRound6Cutset : Set₁ where
  field
    geometryChannelWithinAllocation : Set
    contourTransportChannelWithinAllocation : Set
    chartChannelWithinAllocation : Set
    inverseSeedChannelWithinAllocation : Set
    centreForcingWithinQuarter : Set

open FederbushRound6Cutset public

record BackgroundGaugeRound6Cutset : Set₁ where
  field
    sourceConfigurationIdentification : Set
    siteSupremumNormIdentification : Set
    scaledDerivativeNormIdentification : Set
    mixedNormSourceEquality : Set
    alpha0Alpha1PhysicalMeaning : Set
    centreForcingBound : Set
    backgroundActionConstraintIdentification : Set
    backgroundFineBondNormIdentification : Set

open BackgroundGaugeRound6Cutset public

record HessianRound6Cutset : Set₁ where
  field
    linkExponentialC1C2C3Bounds : Set
    plaquetteDerivativeIdentification : Set
    federbushAverageFirstJet : Set
    federbushAverageSecondJet : Set
    constraintNormalPerturbationIdentification : Set
    referenceAndPhysicalNormalInverseBounds : Set
    curvatureLinearSmallFieldConstant : Set
    transportLinearSmallFieldConstant : Set
    chartLinearSmallFieldConstant : Set
    gaugeLinearSmallFieldConstant : Set
    constraintLinearSmallFieldConstant : Set
    commonSmallFieldRadiusTargets : Set

open HessianRound6Cutset public

record PolymerRound6Cutset : Set₁ where
  field
    physicalCovarianceSmallness : Set
    gaussianCompletionIdentity : Set
    integratedLocalFluctuationMajorant : Set

    WilsonAnimalEntropyConstant : Set
    WilsonDecayWeightAndReservedSlack : Set
    WilsonPenaltyCompatibility : Set

    physicalWeakeningDependencyGraph : Set
    connectedActivityTreeRepresentation : Set
    perLinkOscillationEstimate : Set
    rootedAnimalCountConstant : Set
    weightedInfluenceRatioBelowOne : Set

    rOperationSourceRepositoryDictionary : Set
    smallFieldROperationBoundaryIdentity : Set

    determinantRelativeSpectrumTraceLog : Set
    normalizedTaylorInteractionBound : Set
    BishopHaarChartActivityBound : Set
    backgroundGaugeActivityBound : Set
    propagatorLocalizationActivityBound : Set

open PolymerRound6Cutset public

record PhysicalClosureRound6ExactCutset : Set₁ where
  field
    cmp109 : CMP109Round6Cutset
    bishop : BishopRound6Cutset
    federbush : FederbushRound6Cutset
    backgroundGauge : BackgroundGaugeRound6Cutset
    hessian : HessianRound6Cutset
    polymer : PolymerRound6Cutset

open PhysicalClosureRound6ExactCutset public

physicalClosureRound6CutsetDefinitionLevel : ProofLevel
physicalClosureRound6CutsetDefinitionLevel = machineChecked

physicalClosureRound6CutsetInhabitantsLevel : ProofLevel
physicalClosureRound6CutsetInhabitantsLevel = conditional
