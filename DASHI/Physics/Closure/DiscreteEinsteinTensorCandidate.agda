module DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ)
open import Data.List.Base using (List; _∷_; [])
open import Data.Unit using (⊤; tt)

open import MonsterOntos using (SSP)
import DASHI.Physics.Closure.MinkowskiLimitReceipt as ML
import DASHI.Physics.CRTPeriodJFixedBridge as CRTJ
import Ontology.GodelLattice as GL
import Ontology.Hecke.FactorVecInstances as FVI

infix 4 _≢_

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

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

record DiscreteEinsteinTensorConstructionRequestSurface : Set₂ where
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
      Set₁

    constructionBoundary :
      List String

record FactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface : Set₂ where
  field
    constructionRequest :
      DiscreteEinsteinTensorConstructionRequestSurface

    basePointIsFactorVec :
      DiscreteEinsteinTensorConstructionRequestSurface.BasePoint
        constructionRequest
      ≡
      GL.FactorVec

    coordinateIndexIsSSP :
      DiscreteEinsteinTensorConstructionRequestSurface.CoordinateIndex
        constructionRequest
      ≡
      SSP

    alignmentBoundary :
      List String

zeroFactorVec :
  GL.FactorVec
zeroFactorVec =
  GL.v15
    zero zero zero zero zero
    zero zero zero zero zero
    zero zero zero zero zero

factorVecLeft :
  GL.FactorVec →
  GL.FactorVec →
  GL.FactorVec
factorVecLeft x _ = x

factorVecSSPPrimeDifferenceΔ :
  (GL.FactorVec → GL.FactorVec) →
  GL.FactorVec →
  SSP →
  GL.FactorVec
factorVecSSPPrimeDifferenceΔ observable base direction =
  observable (FVI.primeBump direction base)

factorVecSSPZeroMetric :
  GL.FactorVec →
  SSP →
  SSP →
  GL.FactorVec
factorVecSSPZeroMetric _ _ _ =
  zeroFactorVec

factorVecSSPZeroConnection :
  GL.FactorVec →
  SSP →
  SSP →
  SSP →
  GL.FactorVec
factorVecSSPZeroConnection _ _ _ _ =
  zeroFactorVec

factorVecSSPZeroRiemann :
  GL.FactorVec →
  SSP →
  SSP →
  SSP →
  SSP →
  GL.FactorVec
factorVecSSPZeroRiemann _ _ _ _ _ =
  zeroFactorVec

factorVecSSPContraction :
  (SSP → GL.FactorVec) →
  GL.FactorVec
factorVecSSPContraction component =
  component MonsterOntos.p2

factorVecSSPRicci :
  GL.FactorVec →
  SSP →
  SSP →
  GL.FactorVec
factorVecSSPRicci base mu nu =
  factorVecSSPContraction
    (λ rho →
      factorVecSSPZeroRiemann base rho mu rho nu)

factorVecSSPScalarCurvature :
  GL.FactorVec →
  GL.FactorVec
factorVecSSPScalarCurvature base =
  factorVecSSPContraction
    (λ mu →
      factorVecSSPContraction
        (λ nu →
          factorVecLeft
            (factorVecSSPZeroMetric base mu nu)
            (factorVecSSPRicci base mu nu)))

factorVecSSPEinsteinTensor :
  GL.FactorVec →
  SSP →
  SSP →
  GL.FactorVec
factorVecSSPEinsteinTensor base mu nu =
  factorVecLeft
    (factorVecSSPRicci base mu nu)
    (factorVecLeft
      (factorVecLeft zeroFactorVec (factorVecSSPScalarCurvature base))
      (factorVecSSPZeroMetric base mu nu))

factorVecSSPCommutatorShapedRiemannFromΔΓLaw :
  (base : GL.FactorVec) →
  (rho sigma mu nu : SSP) →
  Set
factorVecSSPCommutatorShapedRiemannFromΔΓLaw base rho sigma _ _ =
  (observable : GL.FactorVec → GL.FactorVec) →
  observable (FVI.primeBump sigma (FVI.primeBump rho base))
  ≡
  observable (FVI.primeBump rho (FVI.primeBump sigma base)) →
  observable (FVI.primeBump sigma (FVI.primeBump rho base))
  ≡
  observable (FVI.primeBump rho (FVI.primeBump sigma base))

data FactorVecSSPFiniteRBianchiWitness : Set where

data FactorVecSSPNonFlatConnectionWitnessMissingField : Set where
  missingFactorVecSSPConnectionCoefficientsDifferFromZero :
    FactorVecSSPNonFlatConnectionWitnessMissingField
  missingFactorVecSSPRiemannCurvatureDifferFromZero :
    FactorVecSSPNonFlatConnectionWitnessMissingField
  missingFactorVecSSPConnectionMatchesConstructionRequest :
    FactorVecSSPNonFlatConnectionWitnessMissingField
  missingFactorVecSSPRiemannMatchesConstructionRequest :
    FactorVecSSPNonFlatConnectionWitnessMissingField
  missingFactorVecSSPRiemannFromNonFlatDeltaGamma :
    FactorVecSSPNonFlatConnectionWitnessMissingField

record FactorVecSSPNonFlatConnectionWitness : Set₁ where
  field
    connectionCoefficients :
      GL.FactorVec →
      SSP →
      SSP →
      SSP →
      GL.FactorVec

    connectionMatchesConstructionRequest :
      connectionCoefficients
      ≡
      factorVecSSPZeroConnection

    nonFlatBase :
      GL.FactorVec

    nonFlatRho :
      SSP

    nonFlatSigma :
      SSP

    nonFlatMu :
      SSP

    nonFlatConnectionComponent :
      connectionCoefficients nonFlatBase nonFlatRho nonFlatSigma nonFlatMu
      ≢
      zeroFactorVec

    riemannCurvature :
      GL.FactorVec →
      SSP →
      SSP →
      SSP →
      SSP →
      GL.FactorVec

    riemannMatchesConstructionRequest :
      riemannCurvature
      ≡
      factorVecSSPZeroRiemann

    nonFlatNu :
      SSP

    nonFlatRiemannComponent :
      riemannCurvature nonFlatBase nonFlatRho nonFlatSigma nonFlatMu nonFlatNu
      ≢
      zeroFactorVec

    riemannFromNonFlatΔΓ :
      factorVecSSPCommutatorShapedRiemannFromΔΓLaw
        nonFlatBase
        nonFlatRho
        nonFlatSigma
        nonFlatMu
        nonFlatNu

    witnessBoundary :
      List String

canonicalFactorVecSSPNonFlatConnectionWitnessRequiredFields :
  List FactorVecSSPNonFlatConnectionWitnessMissingField
canonicalFactorVecSSPNonFlatConnectionWitnessRequiredFields =
  missingFactorVecSSPConnectionCoefficientsDifferFromZero
  ∷ missingFactorVecSSPRiemannCurvatureDifferFromZero
  ∷ missingFactorVecSSPConnectionMatchesConstructionRequest
  ∷ missingFactorVecSSPRiemannMatchesConstructionRequest
  ∷ missingFactorVecSSPRiemannFromNonFlatDeltaGamma
  ∷ []

factorVecSSPDiscreteEinsteinTensorConstructionRequest :
  DiscreteEinsteinTensorConstructionRequestSurface
factorVecSSPDiscreteEinsteinTensorConstructionRequest =
  record
    { BasePoint =
        GL.FactorVec
    ; CoordinateIndex =
        SSP
    ; Scalar =
        GL.FactorVec
    ; _+_ =
        factorVecLeft
    ; _-_ =
        factorVecLeft
    ; _*_ =
        factorVecLeft
    ; oneHalf =
        zeroFactorVec
    ; finiteContraction =
        factorVecSSPContraction
    ; metricComponent =
        factorVecSSPZeroMetric
    ; inverseMetricComponent =
        factorVecSSPZeroMetric
    ; Δ =
        factorVecSSPPrimeDifferenceΔ
    ; Γ =
        factorVecSSPZeroConnection
    ; Riemann =
        factorVecSSPZeroRiemann
    ; RiemannFromΔΓLaw =
        factorVecSSPCommutatorShapedRiemannFromΔΓLaw
    ; Ricci =
        factorVecSSPRicci
    ; RicciFromRiemannLaw =
        λ _ _ _ → refl
    ; scalarCurvature =
        factorVecSSPScalarCurvature
    ; scalarCurvatureTraceLaw =
        λ _ → refl
    ; EinsteinTensor =
        factorVecSSPEinsteinTensor
    ; EinsteinTensorLaw =
        λ _ _ _ → refl
    ; finiteRBianchiWitness =
        FactorVecSSPFiniteRBianchiWitness
    ; nonFlatWitness =
        FactorVecSSPNonFlatConnectionWitness
    ; constructionBoundary =
        "BasePoint is Ontology.GodelLattice.FactorVec"
        ∷ "CoordinateIndex is MonsterOntos.SSP"
        ∷ "Δ is prime-bump pullback over FactorVec"
        ∷ "RiemannFromΔΓLaw is only the commutator-shaped adapter law requested by the Bianchi surface"
        ∷ "Γ and Riemann remain zero placeholders; no non-flat connection inhabitant is supplied"
        ∷ "nonFlatWitness is the structured FactorVecSSPNonFlatConnectionWitness request boundary"
        ∷ []
    }

record FactorVecSSPNonFlatConnectionWitnessRequest : Set₂ where
  field
    targetConstructionRequest :
      DiscreteEinsteinTensorConstructionRequestSurface

    targetConstructionRequestIsCanonicalFactorVecSSP :
      targetConstructionRequest
      ≡
      factorVecSSPDiscreteEinsteinTensorConstructionRequest

    requestedWitnessName :
      String

    requiredMissingFields :
      List FactorVecSSPNonFlatConnectionWitnessMissingField

    firstMissingField :
      FactorVecSSPNonFlatConnectionWitnessMissingField

    firstMissingFieldIsNonZeroConnectionComponent :
      firstMissingField
      ≡
      missingFactorVecSSPConnectionCoefficientsDifferFromZero

    obstructionBoundary :
      List String

canonicalFactorVecSSPNonFlatConnectionWitnessRequest :
  FactorVecSSPNonFlatConnectionWitnessRequest
canonicalFactorVecSSPNonFlatConnectionWitnessRequest =
  record
    { targetConstructionRequest =
        factorVecSSPDiscreteEinsteinTensorConstructionRequest
    ; targetConstructionRequestIsCanonicalFactorVecSSP =
        refl
    ; requestedWitnessName =
        "DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate.FactorVecSSPNonFlatConnectionWitness"
    ; requiredMissingFields =
        canonicalFactorVecSSPNonFlatConnectionWitnessRequiredFields
    ; firstMissingField =
        missingFactorVecSSPConnectionCoefficientsDifferFromZero
    ; firstMissingFieldIsNonZeroConnectionComponent =
        refl
    ; obstructionBoundary =
        "A witness must supply Γ coefficients over FactorVec and SSP"
        ∷ "The supplied Γ must match the construction request's Γ field"
        ∷ "The witness must name a base/direction triple where Γ differs from zeroFactorVec"
        ∷ "The witness must supply Riemann curvature matching the construction request's Riemann field"
        ∷ "The witness must name a base/direction quadruple where Riemann differs from zeroFactorVec"
        ∷ "The witness must supply the RiemannFromΔΓ law at that non-flat component"
        ∷ "The canonical FactorVec/SSP request currently has zero Γ and zero Riemann placeholders, so this request is intentionally not inhabited"
        ∷ []
    }

factorVecSSPNonFlatConnectionWitnessRequestExactFirstMissing :
  FactorVecSSPNonFlatConnectionWitnessRequest.firstMissingField
    canonicalFactorVecSSPNonFlatConnectionWitnessRequest
  ≡
  missingFactorVecSSPConnectionCoefficientsDifferFromZero
factorVecSSPNonFlatConnectionWitnessRequestExactFirstMissing = refl

canonicalFactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface :
  FactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface
canonicalFactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface =
  record
    { constructionRequest =
        factorVecSSPDiscreteEinsteinTensorConstructionRequest
    ; basePointIsFactorVec =
        refl
    ; coordinateIndexIsSSP =
        refl
    ; alignmentBoundary =
        "DiscreteEinsteinTensorConstructionRequestSurface.BasePoint is GL.FactorVec"
        ∷ "DiscreteEinsteinTensorConstructionRequestSurface.CoordinateIndex is SSP"
        ∷ "The aligned request intentionally does not inhabit its nonFlatWitness"
        ∷ []
    }

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
