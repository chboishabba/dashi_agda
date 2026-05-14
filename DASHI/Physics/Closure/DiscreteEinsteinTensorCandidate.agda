module DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ)
open import Data.List.Base using (List; _∷_; [])
open import Data.Unit using (⊤; tt)

import DASHI.Physics.Closure.MinkowskiLimitReceipt as ML
import DASHI.Physics.CRTPeriodJFixedBridge as CRTJ

------------------------------------------------------------------------
-- Diagnostic-only GR candidate surface.
--
-- MinkowskiLimitReceipt supplies an exact flat Lorentzian quadratic.  This
-- module records the weakest next surface for a discrete curvature /
-- Einstein-tensor attempt.  It does not construct a curved connection, Ricci
-- contraction, Einstein equation law, source coupling, continuum limit, or GR
-- promotion receipt.

record DiscreteEinsteinTensorCandidateSurface : Set₁ where
  field
    Carrier :
      Set

    metricQuadratic :
      Carrier → ℤ

    connectionOrShift :
      Carrier → Carrier

    curvature :
      Carrier → Carrier → Carrier

    ricciTrace :
      Carrier → Carrier

    einsteinTensor :
      Carrier → Carrier

    flatCurvatureCondition :
      Set

    bianchiFlatCondition :
      Set

    sourceCouplingCondition :
      Set

    continuumLimitCondition :
      Set

flatIdentityShift :
  ML.MinkowskiCarrier →
  ML.MinkowskiCarrier
flatIdentityShift x = x

flatZeroCurvature :
  ML.MinkowskiCarrier →
  ML.MinkowskiCarrier →
  ML.MinkowskiCarrier
flatZeroCurvature x _ = x

flatZeroTrace :
  ML.MinkowskiCarrier →
  ML.MinkowskiCarrier
flatZeroTrace x = x

flatZeroEinsteinTensor :
  ML.MinkowskiCarrier →
  ML.MinkowskiCarrier
flatZeroEinsteinTensor x = x

flatOnlyDiscreteEinsteinTensorCandidateSurface :
  DiscreteEinsteinTensorCandidateSurface
flatOnlyDiscreteEinsteinTensorCandidateSurface =
  record
    { Carrier =
        ML.MinkowskiCarrier
    ; metricQuadratic =
        ML.minkowskiQuadratic
    ; connectionOrShift =
        flatIdentityShift
    ; curvature =
        flatZeroCurvature
    ; ricciTrace =
        flatZeroTrace
    ; einsteinTensor =
        flatZeroEinsteinTensor
    ; flatCurvatureCondition =
        ⊤
    ; bianchiFlatCondition =
        ⊤
    ; sourceCouplingCondition =
        ⊤
    ; continuumLimitCondition =
        ⊤
    }

flatCandidateUsesLandedMinkowskiQuadratic :
  DiscreteEinsteinTensorCandidateSurface.metricQuadratic
    flatOnlyDiscreteEinsteinTensorCandidateSurface
  ≡
  ML.minkowskiQuadratic
flatCandidateUsesLandedMinkowskiQuadratic = refl

flatCandidateNoCurvedGRPromotion :
  ML.CarrierQuadraticIsMinkowski.noCurvedGRPromotion
    ML.minkowskiLimitReceipt
flatCandidateNoCurvedGRPromotion =
  ML.minkowskiLimitNoCurvedGRPromotion

------------------------------------------------------------------------
-- First-missing diagnostic for the curved / field-equation route.

data DiscreteEinsteinTensorFirstMissingCondition : Set where
  missingNonFlatConnectionOrShift :
    DiscreteEinsteinTensorFirstMissingCondition
  missingCarrierInternalNonFlatConnectionFromCRT :
    DiscreteEinsteinTensorFirstMissingCondition
  missingCurvatureToRicciContraction :
    DiscreteEinsteinTensorFirstMissingCondition
  missingEinsteinTensorLaw :
    DiscreteEinsteinTensorFirstMissingCondition
  missingStressEnergySourceCoupling :
    DiscreteEinsteinTensorFirstMissingCondition
  missingContinuumLimitReceipt :
    DiscreteEinsteinTensorFirstMissingCondition

data DiscreteEinsteinTensorConstructionMissingPrimitive : Set where
  missingBasePointOrCellCarrier :
    DiscreteEinsteinTensorConstructionMissingPrimitive
  missingCoordinateIndexCarrier :
    DiscreteEinsteinTensorConstructionMissingPrimitive
  missingScalarAlgebraForTensorComponents :
    DiscreteEinsteinTensorConstructionMissingPrimitive
  missingFiniteContractionOverCoordinateIndex :
    DiscreteEinsteinTensorConstructionMissingPrimitive
  missingMetricComponents :
    DiscreteEinsteinTensorConstructionMissingPrimitive
  missingInverseMetricComponents :
    DiscreteEinsteinTensorConstructionMissingPrimitive
  missingDiscreteDifferenceDelta :
    DiscreteEinsteinTensorConstructionMissingPrimitive
  missingNonFlatGammaConnectionCoefficients :
    DiscreteEinsteinTensorConstructionMissingPrimitive
  missingRiemannFromDeltaGammaLaw :
    DiscreteEinsteinTensorConstructionMissingPrimitive
  missingRicciContractionLaw :
    DiscreteEinsteinTensorConstructionMissingPrimitive
  missingScalarCurvatureTraceLaw :
    DiscreteEinsteinTensorConstructionMissingPrimitive
  missingEinsteinTensorSubtractionLaw :
    DiscreteEinsteinTensorConstructionMissingPrimitive
  missingFiniteRBianchiWitness :
    DiscreteEinsteinTensorConstructionMissingPrimitive

canonicalDiscreteEinsteinTensorConstructionMissingPrimitives :
  List DiscreteEinsteinTensorConstructionMissingPrimitive
canonicalDiscreteEinsteinTensorConstructionMissingPrimitives =
  missingBasePointOrCellCarrier
  ∷ missingCoordinateIndexCarrier
  ∷ missingScalarAlgebraForTensorComponents
  ∷ missingFiniteContractionOverCoordinateIndex
  ∷ missingMetricComponents
  ∷ missingInverseMetricComponents
  ∷ missingDiscreteDifferenceDelta
  ∷ missingNonFlatGammaConnectionCoefficients
  ∷ missingRiemannFromDeltaGammaLaw
  ∷ missingRicciContractionLaw
  ∷ missingScalarCurvatureTraceLaw
  ∷ missingEinsteinTensorSubtractionLaw
  ∷ missingFiniteRBianchiWitness
  ∷ []

record DiscreteEinsteinTensorConstructionRequestSurface : Set₁ where
  field
    BasePoint :
      Set

    CoordinateIndex :
      Set

    Scalar :
      Set

    _+_ :
      Scalar →
      Scalar →
      Scalar

    _-_ :
      Scalar →
      Scalar →
      Scalar

    _*_ :
      Scalar →
      Scalar →
      Scalar

    oneHalf :
      Scalar

    finiteContraction :
      (CoordinateIndex → Scalar) →
      Scalar

    metricComponent :
      BasePoint →
      CoordinateIndex →
      CoordinateIndex →
      Scalar

    inverseMetricComponent :
      BasePoint →
      CoordinateIndex →
      CoordinateIndex →
      Scalar

    Δ :
      (BasePoint → Scalar) →
      BasePoint →
      CoordinateIndex →
      Scalar

    Γ :
      BasePoint →
      CoordinateIndex →
      CoordinateIndex →
      CoordinateIndex →
      Scalar

    Riemann :
      BasePoint →
      CoordinateIndex →
      CoordinateIndex →
      CoordinateIndex →
      CoordinateIndex →
      Scalar

    RiemannFromΔΓLaw :
      (base : BasePoint) →
      (rho sigma mu nu : CoordinateIndex) →
      Set

    Ricci :
      BasePoint →
      CoordinateIndex →
      CoordinateIndex →
      Scalar

    RicciFromRiemannLaw :
      (base : BasePoint) →
      (mu nu : CoordinateIndex) →
      Ricci base mu nu
      ≡
      finiteContraction
        (λ rho →
          Riemann base rho mu rho nu)

    scalarCurvature :
      BasePoint →
      Scalar

    scalarCurvatureTraceLaw :
      (base : BasePoint) →
      scalarCurvature base
      ≡
      finiteContraction
        (λ mu →
          finiteContraction
            (λ nu →
              inverseMetricComponent base mu nu *
              Ricci base mu nu))

    EinsteinTensor :
      BasePoint →
      CoordinateIndex →
      CoordinateIndex →
      Scalar

    EinsteinTensorLaw :
      (base : BasePoint) →
      (mu nu : CoordinateIndex) →
      EinsteinTensor base mu nu
      ≡
      Ricci base mu nu
      -
      ((oneHalf * scalarCurvature base) *
        metricComponent base mu nu)

    finiteRBianchiWitness :
      Set

    nonFlatWitness :
      Set

    constructionBoundary :
      List String

data DiscreteEinsteinTensorCandidateStatus : Set where
  flatMetricCandidateOnly :
    DiscreteEinsteinTensorCandidateStatus
  crtMoonshineAuditNoConnection :
    DiscreteEinsteinTensorCandidateStatus

------------------------------------------------------------------------
-- CRT / moonshine audit.
--
-- CRTPeriodJFixedBridge gives a finite p47/p59/p71 scalar coupling and a
-- periodicity target.  That is useful evidence for a future construction, but
-- it is not yet a canonical endomap on the Minkowski carrier and therefore is
-- not a non-flat connection.

record CRTMoonshineNonFlatConnectionAudit : Set₁ where
  field
    crtMoonshineCoupling :
      CRTJ.SSPMoonshineCoupling

    suppliedSurface :
      List String

    missingSurface :
      List String

    firstMissing :
      DiscreteEinsteinTensorFirstMissingCondition

    noGRPromotionBoundary :
      List String

canonicalCRTMoonshineNonFlatConnectionAudit :
  CRTMoonshineNonFlatConnectionAudit
canonicalCRTMoonshineNonFlatConnectionAudit =
  record
    { crtMoonshineCoupling =
        CRTJ.sspMoonshineCouplingSurface
    ; suppliedSurface =
        "CRT period product over p47/p59/p71 is available"
        ∷ "J contract bridge to period plus one is available"
        ∷ "active-wall p47/p59/p71 channel projections are available"
        ∷ "A W3 periodicity obligation target is named"
        ∷ []
    ; missingSurface =
        "No W3PeriodicityObligation inhabitant is supplied here"
        ∷ "No CRT-derived endomap on MinkowskiCarrier is supplied"
        ∷ "No connection coefficients, parallel transport, or non-linear shift law are supplied"
        ∷ "No curvature operator derived from CRT/J or p47/p59/p71 channels is supplied"
        ∷ []
    ; firstMissing =
        missingCarrierInternalNonFlatConnectionFromCRT
    ; noGRPromotionBoundary =
        "The CRT/J audit does not promote curved GR recovery"
        ∷ "The CRT/J audit does not construct a non-flat connection"
        ∷ "The CRT/J audit does not prove Einstein equations or continuum recovery"
        ∷ []
    }

crtMoonshineAuditExactFirstMissing :
  CRTMoonshineNonFlatConnectionAudit.firstMissing
    canonicalCRTMoonshineNonFlatConnectionAudit
  ≡
  missingCarrierInternalNonFlatConnectionFromCRT
crtMoonshineAuditExactFirstMissing = refl

record DiscreteEinsteinTensorCandidateDiagnostic : Set₁ where
  field
    status :
      DiscreteEinsteinTensorCandidateStatus

    flatMetricReceipt :
      ML.CarrierQuadraticIsMinkowski

    flatCandidateSurface :
      DiscreteEinsteinTensorCandidateSurface

    crtMoonshineAudit :
      CRTMoonshineNonFlatConnectionAudit

    firstMissing :
      DiscreteEinsteinTensorFirstMissingCondition

    orderedRemainingConditions :
      List DiscreteEinsteinTensorFirstMissingCondition

    tensorConstructionRequestName :
      String

    missingTensorConstructionPrimitives :
      List DiscreteEinsteinTensorConstructionMissingPrimitive

    missingTensorConstructionPrimitivesAreCanonical :
      missingTensorConstructionPrimitives
      ≡
      canonicalDiscreteEinsteinTensorConstructionMissingPrimitives

    diagnosticBoundary :
      List String

    noGRPromotionBoundary :
      List String

canonicalDiscreteEinsteinTensorCandidateDiagnostic :
  DiscreteEinsteinTensorCandidateDiagnostic
canonicalDiscreteEinsteinTensorCandidateDiagnostic =
  record
    { status =
        flatMetricCandidateOnly
    ; flatMetricReceipt =
        ML.minkowskiLimitReceipt
    ; flatCandidateSurface =
        flatOnlyDiscreteEinsteinTensorCandidateSurface
    ; crtMoonshineAudit =
        canonicalCRTMoonshineNonFlatConnectionAudit
    ; firstMissing =
        missingCarrierInternalNonFlatConnectionFromCRT
    ; orderedRemainingConditions =
        missingCarrierInternalNonFlatConnectionFromCRT
        ∷ missingNonFlatConnectionOrShift
        ∷ missingCurvatureToRicciContraction
        ∷ missingEinsteinTensorLaw
        ∷ missingStressEnergySourceCoupling
        ∷ missingContinuumLimitReceipt
        ∷ []
    ; tensorConstructionRequestName =
        "DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate.DiscreteEinsteinTensorConstructionRequestSurface"
    ; missingTensorConstructionPrimitives =
        canonicalDiscreteEinsteinTensorConstructionMissingPrimitives
    ; missingTensorConstructionPrimitivesAreCanonical =
        refl
    ; diagnosticBoundary =
        "MinkowskiLimitReceipt supplies the exact flat Lorentzian quadratic"
        ∷ "The candidate surface here is flat and identity-shift only"
        ∷ "CRT/J p47/p59/p71 surfaces are finite scalar/periodicity surfaces, not a canonical non-flat connection"
        ∷ "DiscreteEinsteinTensorConstructionRequestSurface now names the required Δ, Γ, Riemann, Ricci, scalar-curvature, and Einstein-tensor fields"
        ∷ "Known GR/QFT closure files require downstream curvature, stress-energy, and Einstein-equation consumer fields"
        ∷ "No concrete carrier-internal non-flat connection or shift-curvature operator is present in this module"
        ∷ []
    ; noGRPromotionBoundary =
        "This module does not prove curved GR recovery"
        ∷ "This module does not construct an Einstein field equation law"
        ∷ "This module does not construct stress-energy/source coupling"
        ∷ "This module does not construct a continuum-limit receipt"
        ∷ "This module does not construct a GRQFT closure-promotion receipt"
        ∷ []
    }

discreteEinsteinTensorExactFirstMissing :
  DiscreteEinsteinTensorCandidateDiagnostic.firstMissing
    canonicalDiscreteEinsteinTensorCandidateDiagnostic
  ≡
  missingCarrierInternalNonFlatConnectionFromCRT
discreteEinsteinTensorExactFirstMissing = refl

discreteEinsteinTensorFlatConditionWitness :
  DiscreteEinsteinTensorCandidateSurface.flatCurvatureCondition
    (DiscreteEinsteinTensorCandidateDiagnostic.flatCandidateSurface
      canonicalDiscreteEinsteinTensorCandidateDiagnostic)
discreteEinsteinTensorFlatConditionWitness = tt
