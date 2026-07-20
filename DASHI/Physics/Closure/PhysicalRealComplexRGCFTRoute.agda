module DASHI.Physics.Closure.PhysicalRealComplexRGCFTRoute where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List)

open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope as Envelope

------------------------------------------------------------------------
-- Unified physical R/C fixed-point RG/CFT target.
--
-- This file turns the final physical frontier into one dependent theorem
-- surface.  It does not manufacture a physical instance.  A value of
-- PhysicalFixedPointRGCFTRoute must use one shared scalar carrier and must
-- supply every analytic, empirical, RG, OPE, and Ward obligation below.

------------------------------------------------------------------------
-- Real/complex scalar authority.

data ScalarKind : Set where
  realScalar : ScalarKind
  complexScalar : ScalarKind

record RealComplexScalar (Scalar : Set) : Set₁ where
  field
    scalarKind : ScalarKind

    zero one : Scalar
    _+_ _*_ : Scalar → Scalar → Scalar
    negate conjugate absoluteValue : Scalar → Scalar

    AtMost LessThan : Scalar → Scalar → Set
    Nonzero : Scalar → Set

    additiveFieldLaws : Set
    multiplicativeFieldLaws : Set
    conjugationLaws : Set
    absoluteValueLaws : Set
    orderOrModulusCompatibility : Set
    archimedeanOrComplexAuthority : Set

open RealComplexScalar public

------------------------------------------------------------------------
-- One physical Banach tangent over that scalar.

record PhysicalBanachTangent
  (Scalar Vector : Set)
  (S : RealComplexScalar Scalar)
  : Setω where
  field
    zeroVector : Vector
    _+V_ : Vector → Vector → Vector
    negateV : Vector → Vector
    _·V_ : Scalar → Vector → Vector

    norm distance : Vector → Scalar

    vectorSpaceLaws : Set
    normDefinite : Set
    normHomogeneous : Set
    triangleInequality : Set
    distanceInducedByNorm : Set

    Cauchy : (Nat → Vector) → Set
    ConvergesTo : (Nat → Vector) → Vector → Set
    complete :
      (sequence : Nat → Vector) →
      Cauchy sequence →
      Set

    finiteShiftEmbedding : Set
    finiteEmbeddingPreservesZero : Set
    finiteEmbeddingControlsNorm : Set

open PhysicalBanachTangent public

------------------------------------------------------------------------
-- Real-time Frechet derivative, generator, and analytic estimates.

record RealTimeAnalyticGenerator
  (Scalar Vector Time : Set)
  (S : RealComplexScalar Scalar)
  (B : PhysicalBanachTangent Scalar Vector S)
  : Setω where
  field
    zeroTime : Time
    _+Time_ : Time → Time → Time
    NonnegativeTime : Time → Set

    nonlinearFlow : Time → Vector → Vector
    linearizedFlow : Time → Vector → Vector
    frechetDerivative : Vector → Vector
    generator : Vector → Vector

    identityAtZero : Set
    nonlinearSemigroupLaw : Set
    linearizedSemigroupLaw : Set
    strongContinuityAtZero : Set

    derivativeLinear : Set
    frechetRemainderEstimate : Set
    generatorStrongLimit : Set

    growthBound : Scalar
    exponentialSemigroupEstimate : Set
    dissipativeEstimate : Set

    ResolventPoint : Scalar → Set
    resolvent : Scalar → Vector → Vector
    resolventEquation : Set
    sectorialResolventEstimate : Set
    analyticTimeExtension : Set

    finiteShiftLinearizationCompatibility : Set

open RealTimeAnalyticGenerator public

------------------------------------------------------------------------
-- Measured physical and anomalous dimensions.

record ScalingMeasurement
  (Scalar Operator : Set)
  : Set₁ where
  field
    operator : Operator
    engineeringDimension : Scalar
    measuredTotalDimension : Scalar
    uncertainty : Scalar

    sourceLabel sourceKind sourceRef : String
    analysisMethod datasetLabel : String

open ScalingMeasurement public

record MeasuredAnomalousDimensions
  (Scalar Operator : Set)
  (S : RealComplexScalar Scalar)
  : Setω where
  field
    measurements : List (ScalingMeasurement Scalar Operator)

    engineeringDimension : Operator → Scalar
    anomalousDimension : Operator → Scalar
    totalDimension : Operator → Scalar

    totalSplitsEngineeringPlusAnomaly : Set
    measurementMatchesTotalWithinUncertainty : Set
    covarianceOrErrorModelValid : Set
    renormalizationSchemeDeclared : Set
    scaleDependenceControlled : Set
    spectrumCompleteOnDeclaredSector : Set

    externalProvenanceAudited : Set
    independentReplicationOrAuthority : Set

open MeasuredAnomalousDimensions public

------------------------------------------------------------------------
-- Singular continuum OPE and conformal blocks.

record SingularContinuumOPE
  (Scalar Position Operator : Set)
  (S : RealComplexScalar Scalar)
  : Setω where
  field
    separation : Position → Position → Scalar
    Distinct : Position → Position → Set

    coefficient :
      Operator → Operator → Operator → Position → Position → Scalar
    operatorProduct :
      Operator → Operator → Position → Position → Operator

    conformalBlock :
      Operator → Operator → Operator → Operator → Scalar → Scalar
    crossRatio :
      Position → Position → Position → Position → Scalar

    correlation2 : Operator → Operator → Position → Position → Scalar
    correlation4 :
      Operator → Operator → Operator → Operator →
      Position → Position → Position → Position → Scalar

    singularKernelLaw : Set
    coefficientAnalyticAwayFromCoincidence : Set
    localOPEConverges : Set
    conformalBlockExpansionConverges : Set
    exchangeLocality : Set
    crossingSymmetry : Set
    commonDomainAssociativity : Set
    reflectionPositivityOrDeclaredReplacement : Set

    finiteOPERecovery : Set

open SingularContinuumOPE public

------------------------------------------------------------------------
-- Real/complex analytic depth convergence and RG compatibility.

record RealComplexDepthConvergence
  (Scalar : Set)
  (S : RealComplexScalar Scalar)
  : Setω where
  field
    depthModel : Envelope.DepthKernelModel
    continuousEnvelope : Envelope.ContinuousDepthEnvelope depthModel

    scalarize : Envelope.Scalar depthModel → Scalar
    physicalEmbed : Envelope.Stream → Scalar
    physicalDepthMetric : Envelope.Stream → Envelope.Stream → Scalar

    scalarizationMatchesEmbed : Set
    finiteApproximantsConvergeAnalytically : Set
    depthMetricComplete : Set
    cylinderContinuityEstimate : Set
    firstDifferenceTwoSidedEstimate : Set
    dominatedOrAbsoluteSummability : Set
    nontrivialImage : Set

open RealComplexDepthConvergence public

record RGUniversalityAcrossDepth
  (Scalar : Set)
  (S : RealComplexScalar Scalar)
  (D : RealComplexDepthConvergence Scalar S)
  : Setω where
  field
    coarseGrain : Envelope.Stream → Envelope.Stream
    fixedStream : Envelope.Stream
    rgFlow : Nat → Envelope.Stream → Envelope.Stream

    fixedPointLaw : Set
    semigroupAcrossDepth : Set
    envelopeIntertwinesRG : Set
    finiteShiftIntertwiner : Set
    convergenceToFixedPoint : Set

    Basin : Envelope.Stream → Set
    universalScalingData : Set
    regulatorIndependence : Set
    schemeChangeEquivalence : Set
    irrelevantDirectionsContract : Set
    relevantAndMarginalDirectionsClassified : Set
    universalityAcrossDeclaredBasin : Set

open RGUniversalityAcrossDepth public

------------------------------------------------------------------------
-- Nontrivial physical stress tensor, central charge, and Ward identities.

record PhysicalStressTensorConformalWard
  (Scalar Position Operator StressTensor : Set)
  (S : RealComplexScalar Scalar)
  : Setω where
  field
    stressInsertion : StressTensor → Position → Operator
    stressTwoPoint : StressTensor → StressTensor → Position → Position → Scalar
    correlation : List Operator → List Position → Scalar

    centralCharge : Scalar
    centralChargeNonzero : Nonzero S centralCharge
    stressTwoPointNontrivial : Set

    distributionalConservation : Set
    traceIdentityOrAnomaly : Set
    translationWard : Set
    rotationWard : Set
    dilationWard : Set
    specialConformalWard : Set
    wardCompatibleWithOPE : Set
    centralTermMatchesStressOPE : Set
    anomalyAndSchemeAccounting : Set

open PhysicalStressTensorConformalWard public

------------------------------------------------------------------------
-- One shared physical route.  All components use the same Scalar, Position,
-- Operator, and tangent model rather than the heterogeneous reference carriers.

record PhysicalFixedPointRGCFTRoute : Setω where
  field
    Scalar Vector Time Position Operator StressTensor : Set

    scalar : RealComplexScalar Scalar
    banachTangent : PhysicalBanachTangent Scalar Vector scalar
    analyticGenerator :
      RealTimeAnalyticGenerator Scalar Vector Time scalar banachTangent

    measuredSpectrum : MeasuredAnomalousDimensions Scalar Operator scalar
    singularOPE : SingularContinuumOPE Scalar Position Operator scalar

    analyticDepth : RealComplexDepthConvergence Scalar scalar
    rgUniversality : RGUniversalityAcrossDepth Scalar scalar analyticDepth

    stressWard :
      PhysicalStressTensorConformalWard
        Scalar Position Operator StressTensor scalar

    tangentOperatorsSharePhysicalSector : Set
    generatorMatchesRGLinearization : Set
    scalingMatchesGeneratorSpectrum : Set
    opeDimensionsMatchMeasuredSpectrum : Set
    stressWardMatchesOPE : Set
    depthRGMatchesFieldTheoryRG : Set

    declaredPhysicalSystem : String
    declaredDimension : Nat
    claimBoundary : List String

open PhysicalFixedPointRGCFTRoute public
