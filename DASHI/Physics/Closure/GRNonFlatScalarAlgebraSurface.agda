module DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Selected non-flat finite-r scalar/metric algebra surface.
--
-- This module intentionally does not construct a non-flat Levi-Civita
-- connection.  It sharpens the algebraic interface that such a construction
-- must inhabit after the existing flat Minkowski prerequisite.

record GRCarrierScalarOperations : Set₁ where
  field
    CarrierScalar :
      Set

    zeroScalar :
      CarrierScalar

    oneScalar :
      CarrierScalar

    twoScalar :
      CarrierScalar

    _+_ :
      CarrierScalar →
      CarrierScalar →
      CarrierScalar

    _-_ :
      CarrierScalar →
      CarrierScalar →
      CarrierScalar

    _*_ :
      CarrierScalar →
      CarrierScalar →
      CarrierScalar

    additiveIdentityLaw :
      (x : CarrierScalar) →
      (zeroScalar + x) ≡ x

    multiplicativeIdentityLaw :
      (x : CarrierScalar) →
      (oneScalar * x) ≡ x

    scalarBoundary :
      List String

data GRFiniteRScalar : Set where
  r0 r1 r2 r3 : GRFiniteRScalar

grFiniteRScalarAdd :
  GRFiniteRScalar →
  GRFiniteRScalar →
  GRFiniteRScalar
grFiniteRScalarAdd r0 y = y
grFiniteRScalarAdd r1 r0 = r1
grFiniteRScalarAdd r1 r1 = r2
grFiniteRScalarAdd r1 r2 = r3
grFiniteRScalarAdd r1 r3 = r0
grFiniteRScalarAdd r2 r0 = r2
grFiniteRScalarAdd r2 r1 = r3
grFiniteRScalarAdd r2 r2 = r0
grFiniteRScalarAdd r2 r3 = r1
grFiniteRScalarAdd r3 r0 = r3
grFiniteRScalarAdd r3 r1 = r0
grFiniteRScalarAdd r3 r2 = r1
grFiniteRScalarAdd r3 r3 = r2

grFiniteRScalarMul :
  GRFiniteRScalar →
  GRFiniteRScalar →
  GRFiniteRScalar
grFiniteRScalarMul r0 _ = r0
grFiniteRScalarMul r1 y = y
grFiniteRScalarMul r2 r0 = r0
grFiniteRScalarMul r2 r1 = r2
grFiniteRScalarMul r2 r2 = r0
grFiniteRScalarMul r2 r3 = r2
grFiniteRScalarMul r3 r0 = r0
grFiniteRScalarMul r3 r1 = r3
grFiniteRScalarMul r3 r2 = r2
grFiniteRScalarMul r3 r3 = r1

grFiniteRScalarNeg :
  GRFiniteRScalar →
  GRFiniteRScalar
grFiniteRScalarNeg r0 = r0
grFiniteRScalarNeg r1 = r3
grFiniteRScalarNeg r2 = r2
grFiniteRScalarNeg r3 = r1

grFiniteRScalarSub :
  GRFiniteRScalar →
  GRFiniteRScalar →
  GRFiniteRScalar
grFiniteRScalarSub x y =
  grFiniteRScalarAdd x (grFiniteRScalarNeg y)

grFiniteRScalarAdditiveIdentity :
  (x : GRFiniteRScalar) →
  grFiniteRScalarAdd r0 x ≡ x
grFiniteRScalarAdditiveIdentity _ = refl

grFiniteRScalarMultiplicativeIdentity :
  (x : GRFiniteRScalar) →
  grFiniteRScalarMul r1 x ≡ x
grFiniteRScalarMultiplicativeIdentity _ = refl

canonicalGRFiniteRCarrierScalarOperations :
  GRCarrierScalarOperations
canonicalGRFiniteRCarrierScalarOperations =
  record
    { CarrierScalar =
        GRFiniteRScalar
    ; zeroScalar =
        r0
    ; oneScalar =
        r1
    ; twoScalar =
        r2
    ; _+_ =
        grFiniteRScalarAdd
    ; _-_ =
        grFiniteRScalarSub
    ; _*_ =
        grFiniteRScalarMul
    ; additiveIdentityLaw =
        grFiniteRScalarAdditiveIdentity
    ; multiplicativeIdentityLaw =
        grFiniteRScalarMultiplicativeIdentity
    ; scalarBoundary =
        "Concrete four-residue CarrierScalar table for the selected finite-r algebra surface"
        ∷ "Operations are total finite tables for zero, one, two, addition, subtraction, and multiplication"
        ∷ "Only identity laws required by GRCarrierScalarOperations are inhabited here"
        ∷ "This scalar record does not instantiate a non-flat metric dependency, connection, or Levi-Civita witness"
        ∷ []
    }

record GRSelectedNonFlatMetricDependency
  (scalarOps : GRCarrierScalarOperations) : Setω where
  open GRCarrierScalarOperations scalarOps

  field
    FiniteRBaseCarrier :
      Set

    CoordinateIndex :
      Set

    MetricCarrier :
      Set

    ConnectionCarrier :
      Set

    CurvatureCarrier :
      Set

    RicciCarrier :
      Set

    ScalarTraceCarrier :
      Set

    metricAt :
      FiniteRBaseCarrier →
      MetricCarrier

    carrierConnection :
      FiniteRBaseCarrier →
      ConnectionCarrier

    metricComponent :
      MetricCarrier →
      CoordinateIndex →
      CoordinateIndex →
      CarrierScalar

    inverseMetricComponent :
      MetricCarrier →
      CoordinateIndex →
      CoordinateIndex →
      CarrierScalar

    coordinateDerivativeOfMetric :
      MetricCarrier →
      CoordinateIndex →
      CoordinateIndex →
      CoordinateIndex →
      CarrierScalar

    finiteContract :
      (CoordinateIndex → CarrierScalar) →
      CarrierScalar

    christoffelSymbol :
      ConnectionCarrier →
      CoordinateIndex →
      CoordinateIndex →
      CoordinateIndex →
      CarrierScalar

    covariantDerivativeOfMetric :
      ConnectionCarrier →
      MetricCarrier →
      CoordinateIndex →
      CoordinateIndex →
      CoordinateIndex →
      CarrierScalar

    metricContractionForRicci :
      MetricCarrier →
      CurvatureCarrier →
      RicciCarrier

    traceOfMetric :
      MetricCarrier →
      ScalarTraceCarrier

    dependencyBoundary :
      List String

record GRSelectedNonFlatMetricAlgebraLaws
  (scalarOps : GRCarrierScalarOperations)
  (dependency : GRSelectedNonFlatMetricDependency scalarOps) : Setω where
  open GRCarrierScalarOperations scalarOps
  open GRSelectedNonFlatMetricDependency dependency

  field
    kroneckerDelta :
      CoordinateIndex →
      CoordinateIndex →
      CarrierScalar

    inverseMetricLeftLaw :
      (base : FiniteRBaseCarrier) →
      (mu nu : CoordinateIndex) →
      finiteContract
        (λ rho →
          inverseMetricComponent (metricAt base) mu rho *
          metricComponent (metricAt base) rho nu)
      ≡
      kroneckerDelta mu nu

    inverseMetricRightLaw :
      (base : FiniteRBaseCarrier) →
      (mu nu : CoordinateIndex) →
      finiteContract
        (λ rho →
          metricComponent (metricAt base) mu rho *
          inverseMetricComponent (metricAt base) rho nu)
      ≡
      kroneckerDelta mu nu

    christoffelFromMetricLaw :
      (base : FiniteRBaseCarrier) →
      (lambda mu nu : CoordinateIndex) →
      (twoScalar *
        christoffelSymbol (carrierConnection base) lambda mu nu)
      ≡
      finiteContract
        (λ rho →
          inverseMetricComponent (metricAt base) lambda rho *
          ((coordinateDerivativeOfMetric (metricAt base) mu nu rho
            + coordinateDerivativeOfMetric (metricAt base) nu mu rho)
            - coordinateDerivativeOfMetric (metricAt base) rho mu nu))

    metricCompatibilityExpansion :
      (base : FiniteRBaseCarrier) →
      (lambda mu nu : CoordinateIndex) →
      covariantDerivativeOfMetric
        (carrierConnection base)
        (metricAt base)
        lambda
        mu
        nu
      ≡
      (coordinateDerivativeOfMetric (metricAt base) lambda mu nu
        - finiteContract
          (λ rho →
            christoffelSymbol (carrierConnection base) rho lambda mu *
            metricComponent (metricAt base) rho nu))
      - finiteContract
        (λ rho →
          christoffelSymbol (carrierConnection base) rho lambda nu *
          metricComponent (metricAt base) mu rho)

    sixTermRicciCancellationLaw :
      (base : FiniteRBaseCarrier) →
      (lambda mu nu : CoordinateIndex) →
      covariantDerivativeOfMetric
        (carrierConnection base)
        (metricAt base)
        lambda
        mu
        nu
      ≡
      zeroScalar

    traceEqualsFourLaw :
      (base : FiniteRBaseCarrier) →
      Set

    lawBoundary :
      List String

record GRSelectedNonFlatMetricDependencyChainInputs
  (scalarOps : GRCarrierScalarOperations)
  (dependency : GRSelectedNonFlatMetricDependency scalarOps)
  (laws : GRSelectedNonFlatMetricAlgebraLaws scalarOps dependency) : Set where
  field
    metricInput :
      String

    inverseLawInput :
      String

    derivativeInput :
      String

    contractionInput :
      String

    christoffelInput :
      String

    traceInput :
      String

    ricciCancellationInput :
      String

    dependencySurfaceBoundary :
      List String

record GRSelectedNonFlatConditionalDependencySurface : Set where
  field
    scalarOperationsState :
      String

    scalarStateBump :
      String

    metricInputName :
      String

    inverseLawInputName :
      String

    derivativeInputName :
      String

    contractionInputName :
      String

    christoffelInputName :
      String

    traceInputName :
      String

    ricciCancellationInputName :
      String

    noPromotionBoundary :
      List String

data GRSelectedNonFlatScalarAlgebraSurfaceStatus : Set where
  selectedNonFlatScalarAlgebraSurfaceObligationOnly :
    GRSelectedNonFlatScalarAlgebraSurfaceStatus

record GRSelectedNonFlatScalarAlgebraObligationReceipt : Set where
  field
    status :
      GRSelectedNonFlatScalarAlgebraSurfaceStatus

    carrierScalarOperationsInterface :
      String

    nonFlatMetricDependencyInterface :
      String

    exactLawInterface :
      String

    conditionalDependencySurfaceInterface :
      String

    firstMissingInterface :
      String

    noNonFlatLeviCivitaInhabitant :
      String

    receiptBoundary :
      List String

canonicalGRSelectedNonFlatScalarAlgebraObligationReceipt :
  GRSelectedNonFlatScalarAlgebraObligationReceipt
canonicalGRSelectedNonFlatScalarAlgebraObligationReceipt =
  record
    { status =
        selectedNonFlatScalarAlgebraSurfaceObligationOnly
    ; carrierScalarOperationsInterface =
        "GRCarrierScalarOperations"
    ; nonFlatMetricDependencyInterface =
        "GRSelectedNonFlatMetricDependency"
    ; exactLawInterface =
        "GRSelectedNonFlatMetricAlgebraLaws"
    ; conditionalDependencySurfaceInterface =
        "GRSelectedNonFlatConditionalDependencySurface"
    ; firstMissingInterface =
        "GRSelectedNonFlatMetricDependency for canonicalGRFiniteRCarrierScalarOperations"
    ; noNonFlatLeviCivitaInhabitant =
        "No carrierConnectionIsLeviCivita inhabitant is produced for a selected non-flat carrier"
    ; receiptBoundary =
        "CarrierScalar operations are concretely typed as a four-residue finite table before any non-flat metric law is consumed"
        ∷ "The metric dependency separates metric components, inverse metric, coordinate derivative, finite contraction, Christoffel symbols, trace, and Ricci contraction"
        ∷ "The exact laws require inverse-metric left/right contraction, Christoffel-from-metric, metric-compatibility expansion, trace=4, and six-term Ricci cancellation"
        ∷ "The conditional dependency surface names metric, inverse law, derivative, contraction, Christoffel, trace, and Ricci cancellation inputs while scalar state bump remains unavailable"
        ∷ "This receipt is non-promoting: it does not instantiate the selected non-flat carrier, metric, connection, or Levi-Civita witness"
        ∷ []
    }

canonicalGRSelectedNonFlatConditionalDependencySurface :
  GRSelectedNonFlatConditionalDependencySurface
canonicalGRSelectedNonFlatConditionalDependencySurface =
  record
    { scalarOperationsState =
        "canonicalGRFiniteRCarrierScalarOperations available for the selected finite-r scalar surface"
    ; scalarStateBump =
        "No scalar/state bump from finite scalar operations to selected non-flat finite-r metric state"
    ; metricInputName =
        "metric: GRSelectedNonFlatMetricDependency.metricAt plus metricComponent"
    ; inverseLawInputName =
        "inverse law: GRSelectedNonFlatMetricAlgebraLaws.inverseMetricLeftLaw and inverseMetricRightLaw"
    ; derivativeInputName =
        "derivative: GRSelectedNonFlatMetricDependency.coordinateDerivativeOfMetric"
    ; contractionInputName =
        "contraction: GRSelectedNonFlatMetricDependency.finiteContract and metricContractionForRicci"
    ; christoffelInputName =
        "Christoffel: GRSelectedNonFlatMetricDependency.christoffelSymbol plus christoffelFromMetricLaw"
    ; traceInputName =
        "trace: GRSelectedNonFlatMetricDependency.traceOfMetric plus traceEqualsFourLaw"
    ; ricciCancellationInputName =
        "Ricci cancellation: GRSelectedNonFlatMetricAlgebraLaws.sixTermRicciCancellationLaw"
    ; noPromotionBoundary =
        "This conditional surface is an input list, not an inhabitant of GRSelectedNonFlatMetricAlgebraLaws"
        ∷ "It does not construct a selected non-flat Levi-Civita connection"
        ∷ "It does not assert Ricci contraction, contracted Bianchi, vacuum Ricci-zero, or Einstein closure"
        ∷ []
    }

selectedNonFlatScalarAlgebraReceiptFirstMissing :
  GRSelectedNonFlatScalarAlgebraObligationReceipt.firstMissingInterface
    canonicalGRSelectedNonFlatScalarAlgebraObligationReceipt
  ≡
  "GRSelectedNonFlatMetricDependency for canonicalGRFiniteRCarrierScalarOperations"
selectedNonFlatScalarAlgebraReceiptFirstMissing = refl
