module DASHI.Physics.Closure.PhysicalRealComplexRGCFTRoute where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; map)

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
    _+S_ _*S_ : Scalar → Scalar → Scalar
    negate conjugate absoluteValue : Scalar → Scalar

    AtMost LessThan : Scalar → Scalar → Set
    Nonzero : Scalar → Set

    addLeftUnit : (x : Scalar) → zero +S x ≡ x
    addRightUnit : (x : Scalar) → x +S zero ≡ x
    addAssociative :
      (x y z : Scalar) → (x +S y) +S z ≡ x +S (y +S z)
    addCommutative : (x y : Scalar) → x +S y ≡ y +S x
    additiveInverse : (x : Scalar) → x +S negate x ≡ zero

    multiplyLeftUnit : (x : Scalar) → one *S x ≡ x
    multiplyRightUnit : (x : Scalar) → x *S one ≡ x
    multiplyAssociative :
      (x y z : Scalar) → (x *S y) *S z ≡ x *S (y *S z)
    multiplyCommutative : (x y : Scalar) → x *S y ≡ y *S x
    distributes :
      (x y z : Scalar) → x *S (y +S z) ≡ (x *S y) +S (x *S z)

    conjugateInvolutive : (x : Scalar) → conjugate (conjugate x) ≡ x
    conjugateAdditive :
      (x y : Scalar) → conjugate (x +S y) ≡ conjugate x +S conjugate y
    conjugateMultiplicative :
      (x y : Scalar) → conjugate (x *S y) ≡ conjugate x *S conjugate y

    absoluteZero : absoluteValue zero ≡ zero
    absoluteMultiplicative :
      (x y : Scalar) →
      absoluteValue (x *S y) ≡ absoluteValue x *S absoluteValue y
    absoluteTriangle :
      (x y : Scalar) →
      AtMost (absoluteValue (x +S y))
        (absoluteValue x +S absoluteValue y)

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

    vectorAddLeftUnit : (x : Vector) → zeroVector +V x ≡ x
    vectorAddRightUnit : (x : Vector) → x +V zeroVector ≡ x
    vectorAddAssociative :
      (x y z : Vector) → (x +V y) +V z ≡ x +V (y +V z)
    vectorAddCommutative : (x y : Vector) → x +V y ≡ y +V x
    vectorAddInverse : (x : Vector) → x +V negateV x ≡ zeroVector

    scalarUnit : (x : Vector) → RealComplexScalar.one S ·V x ≡ x
    scalarAssociative :
      (a b : Scalar) (x : Vector) →
      (RealComplexScalar._*S_ S a b) ·V x ≡ a ·V (b ·V x)
    scalarDistributesOverVectors :
      (a : Scalar) (x y : Vector) → a ·V (x +V y) ≡ (a ·V x) +V (a ·V y)
    vectorDistributesOverScalars :
      (a b : Scalar) (x : Vector) →
      (RealComplexScalar._+S_ S a b) ·V x ≡ (a ·V x) +V (b ·V x)

    normZero : norm zeroVector ≡ RealComplexScalar.zero S
    normSeparates :
      (x : Vector) → norm x ≡ RealComplexScalar.zero S → x ≡ zeroVector
    normHomogeneous :
      (a : Scalar) (x : Vector) →
      norm (a ·V x) ≡ RealComplexScalar._*S_ S (RealComplexScalar.absoluteValue S a) (norm x)
    triangleInequality :
      (x y : Vector) →
      RealComplexScalar.AtMost S
        (norm (x +V y))
        (RealComplexScalar._+S_ S (norm x) (norm y))
    distanceInducedByNorm :
      (x y : Vector) → distance x y ≡ norm (x +V negateV y)

    Cauchy : (Nat → Vector) → Set
    ConvergesTo : (Nat → Vector) → Vector → Set
    complete :
      (sequence : Nat → Vector) →
      Cauchy sequence →
      Σ Vector (λ limit → ConvergesTo sequence limit)

    FinitePerturbation : Set
    finiteZero : FinitePerturbation
    finiteNorm : FinitePerturbation → Scalar
    embedFinite : FinitePerturbation → Vector
    finiteEmbeddingPreservesZero : embedFinite finiteZero ≡ zeroVector
    finiteEmbeddingControlsNorm :
      (p : FinitePerturbation) → norm (embedFinite p) ≡ finiteNorm p

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

    nonlinearIdentityAtZero :
      (x : Vector) → nonlinearFlow zeroTime x ≡ x
    linearizedIdentityAtZero :
      (x : Vector) → linearizedFlow zeroTime x ≡ x
    nonlinearSemigroupLaw :
      (s t : Time) (x : Vector) →
      nonlinearFlow (s +Time t) x ≡ nonlinearFlow t (nonlinearFlow s x)
    linearizedSemigroupLaw :
      (s t : Time) (x : Vector) →
      linearizedFlow (s +Time t) x ≡ linearizedFlow t (linearizedFlow s x)

    derivativeAdditive :
      (x y : Vector) →
      frechetDerivative (PhysicalBanachTangent._+V_ B x y)
        ≡
      PhysicalBanachTangent._+V_ B
        (frechetDerivative x) (frechetDerivative y)
    derivativeHomogeneous :
      (a : Scalar) (x : Vector) →
      frechetDerivative (PhysicalBanachTangent._·V_ B a x)
        ≡
      PhysicalBanachTangent._·V_ B a (frechetDerivative x)

    FrechetRemainderControlled : Vector → Set
    frechetRemainderControlled :
      (x : Vector) → FrechetRemainderControlled x

    GeneratorLimitExists : Vector → Set
    generatorLimitExists : (x : Vector) → GeneratorLimitExists x

    StronglyContinuousAtZero : Vector → Set
    stronglyContinuousAtZero : (x : Vector) → StronglyContinuousAtZero x

    growthBound : Scalar
    SemigroupEstimate : Time → Vector → Set
    exponentialSemigroupEstimate :
      (t : Time) (x : Vector) → SemigroupEstimate t x

    DissipativeAt : Vector → Set
    dissipativeEstimate : (x : Vector) → DissipativeAt x

    ResolventPoint : Scalar → Set
    resolvent : Scalar → Vector → Vector
    ResolventEquationAt : Scalar → Vector → Set
    resolventEquation :
      (lambda : Scalar) → ResolventPoint lambda →
      (x : Vector) → ResolventEquationAt lambda x

    SectorialEstimateAt : Scalar → Set
    sectorialResolventEstimate :
      (lambda : Scalar) → ResolventPoint lambda → SectorialEstimateAt lambda

    AnalyticTimeExtensionAt : Time → Set
    analyticTimeExtension :
      (t : Time) → NonnegativeTime t → AnalyticTimeExtensionAt t

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

    totalSplitsEngineeringPlusAnomaly :
      (operator : Operator) →
      totalDimension operator
        ≡
      RealComplexScalar._+S_ S
        (engineeringDimension operator)
        (anomalousDimension operator)

    WithinUncertainty : Scalar → Scalar → Scalar → Set
    measurementMatchesTotalWithinUncertainty :
      (measurement : ScalingMeasurement Scalar Operator) →
      WithinUncertainty
        (ScalingMeasurement.measuredTotalDimension measurement)
        (totalDimension (ScalingMeasurement.operator measurement))
        (ScalingMeasurement.uncertainty measurement)

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

    SingularAtCoincidence : Operator → Operator → Operator → Set
    singularKernelLaw :
      (p q r : Operator) → SingularAtCoincidence p q r

    AnalyticAwayFromCoincidence :
      Operator → Operator → Operator → Position → Position → Set
    coefficientAnalyticAwayFromCoincidence :
      (p q r : Operator) (x y : Position) →
      Distinct x y → AnalyticAwayFromCoincidence p q r x y

    OPEConvergesAt : Operator → Operator → Position → Position → Set
    localOPEConverges :
      (p q : Operator) (x y : Position) →
      Distinct x y → OPEConvergesAt p q x y

    BlockExpansionConvergesAt :
      Operator → Operator → Operator → Operator →
      Position → Position → Position → Position → Set
    conformalBlockExpansionConverges :
      (p q r s : Operator) (x y z w : Position) →
      BlockExpansionConvergesAt p q r s x y z w

    coefficientExchange :
      (p q r : Operator) (x y : Position) →
      coefficient p q r x y ≡ coefficient q p r y x
    productExchange :
      (p q : Operator) (x y : Position) →
      operatorProduct p q x y ≡ operatorProduct q p y x

    CrossingEquation :
      Operator → Operator → Operator → Operator →
      Position → Position → Position → Position → Set
    crossingSymmetry :
      (p q r s : Operator) (x y z w : Position) →
      CrossingEquation p q r s x y z w

    CommonDomainAssociativity :
      Operator → Operator → Operator →
      Position → Position → Position → Set
    commonDomainAssociativity :
      (p q r : Operator) (x y z : Position) →
      CommonDomainAssociativity p q r x y z

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

    scalarizationMatchesEmbed :
      (d : Envelope.Stream) →
      scalarize (Envelope.embed continuousEnvelope d) ≡ physicalEmbed d

    ScalarConverges : (Nat → Scalar) → Scalar → Set
    finiteApproximantsConvergeAnalytically :
      (d : Envelope.Stream) →
      ScalarConverges
        (λ n → scalarize (Envelope.finiteEvaluation depthModel n d))
        (physicalEmbed d)

    MetricCauchy : (Nat → Envelope.Stream) → Set
    MetricConvergesTo :
      (Nat → Envelope.Stream) → Envelope.Stream → Set
    depthMetricComplete :
      (sequence : Nat → Envelope.Stream) →
      MetricCauchy sequence →
      Σ Envelope.Stream (λ limit → MetricConvergesTo sequence limit)

    CylinderEstimate :
      Nat → Envelope.Stream → Envelope.Stream → Scalar → Set
    cylinderContinuityEstimate :
      (n : Nat) (x y : Envelope.Stream) →
      Envelope.PrefixAgreement n x y →
      CylinderEstimate n x y (physicalDepthMetric x y)

    FirstDifferenceTwoSided : Nat → Scalar → Set
    firstDifferenceTwoSidedEstimate :
      (n : Nat) (x y : Envelope.Stream) →
      Envelope.FirstDifferenceAt n x y →
      FirstDifferenceTwoSided n (physicalDepthMetric x y)

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

    rgZero : (d : Envelope.Stream) → rgFlow zero d ≡ d
    fixedPointLaw : coarseGrain fixedStream ≡ fixedStream
    semigroupAcrossDepth :
      (m n : Nat) (d : Envelope.Stream) →
      rgFlow (m + n) d ≡ rgFlow n (rgFlow m d)

    envelopeIntertwinesRG : Set

    FinitePerturbation : Set
    finiteStep : FinitePerturbation → FinitePerturbation
    encodeFinite : FinitePerturbation → Envelope.Stream
    finiteShiftIntertwiner :
      (p : FinitePerturbation) →
      coarseGrain (encodeFinite p) ≡ encodeFinite (finiteStep p)

    ConvergesToFixedPoint : Envelope.Stream → Set
    convergenceToFixedPoint :
      (d : Envelope.Stream) → ConvergesToFixedPoint d

    Basin : Envelope.Stream → Set
    UniversalScalingDataFor : Envelope.Stream → Set
    universalScalingData :
      (d : Envelope.Stream) → Basin d → UniversalScalingDataFor d

    RegulatorEquivalent : Envelope.Stream → Envelope.Stream → Set
    regulatorIndependence :
      (x y : Envelope.Stream) →
      Basin x → Basin y → RegulatorEquivalent x y

    SchemeEquivalent : Envelope.Stream → Envelope.Stream → Set
    schemeChangeEquivalence :
      (x y : Envelope.Stream) →
      Basin x → Basin y → SchemeEquivalent x y

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
    centralChargeNonzero : RealComplexScalar.Nonzero S centralCharge

    nontrivialStressTensor : StressTensor
    nontrivialStressX nontrivialStressY : Position
    stressTwoPointNontrivial :
      RealComplexScalar.Nonzero S
        (stressTwoPoint
          nontrivialStressTensor
          nontrivialStressTensor
          nontrivialStressX
          nontrivialStressY)

    DivergenceFree : StressTensor → Set
    divergenceFree : (T : StressTensor) → DivergenceFree T

    TraceIdentityOrAnomaly : StressTensor → Set
    traceIdentityOrAnomaly :
      (T : StressTensor) → TraceIdentityOrAnomaly T

    translate rotate dilate specialConformal : Position → Position

    translationWard :
      (operators : List Operator) (positions : List Position) →
      correlation operators (map translate positions)
        ≡
      correlation operators positions
    rotationWard :
      (operators : List Operator) (positions : List Position) →
      correlation operators (map rotate positions)
        ≡
      correlation operators positions
    dilationWard :
      (operators : List Operator) (positions : List Position) →
      correlation operators (map dilate positions)
        ≡
      correlation operators positions
    specialConformalWard :
      (operators : List Operator) (positions : List Position) →
      correlation operators (map specialConformal positions)
        ≡
      correlation operators positions

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
