module DASHI.Biology.FMRIConnectomeProxyGovernance where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.BodyMemoryMeasurementProxyBoundary as Measurement
import DASHI.Biology.FunctionalConnectomeBodyMemoryBridge as Bridge
import DASHI.Physics.Closure.BrainConnectomeFMRIObservationQuotient as BrainFMRI

------------------------------------------------------------------------
-- Candidate-only governance for deepened fMRI/connectome body-memory placement.
--
-- The surface here refines the proxy lane into:
--   - measurement proxy,
--   - BOLD/signal proxy,
--   - connectome graph proxy,
--   - functional connectivity proxy,
--   - reverse-inference boundary.
--
-- It explicitly blocks hidden-chart recovery, mind-reading, diagnosis,
-- treatment, and clinical authority.  The record is intentionally
-- candidate-only and reuses the existing body-memory bridge/boundary
-- surfaces as canonical receipts.

data Never : Set where

data FMRIConnectomeProxyRoute : Set where
  candidateOnlyRoute : FMRIConnectomeProxyRoute
  fmriMeasurementProxyRoute : FMRIConnectomeProxyRoute
  boldSignalProxyRoute : FMRIConnectomeProxyRoute
  connectomeGraphProxyRoute : FMRIConnectomeProxyRoute
  functionalConnectivityProxyRoute : FMRIConnectomeProxyRoute
  reverseInferenceBoundaryRoute : FMRIConnectomeProxyRoute
  hiddenChartRecoveryRoute : FMRIConnectomeProxyRoute
  mindReadingRoute : FMRIConnectomeProxyRoute
  diagnosisRoute : FMRIConnectomeProxyRoute
  treatmentRoute : FMRIConnectomeProxyRoute
  clinicalAuthorityRoute : FMRIConnectomeProxyRoute

AdmissibleFMRIConnectomeProxyRoute :
  FMRIConnectomeProxyRoute →
  Set
AdmissibleFMRIConnectomeProxyRoute candidateOnlyRoute = ⊤
AdmissibleFMRIConnectomeProxyRoute fmriMeasurementProxyRoute = Never
AdmissibleFMRIConnectomeProxyRoute boldSignalProxyRoute = Never
AdmissibleFMRIConnectomeProxyRoute connectomeGraphProxyRoute = Never
AdmissibleFMRIConnectomeProxyRoute functionalConnectivityProxyRoute = Never
AdmissibleFMRIConnectomeProxyRoute reverseInferenceBoundaryRoute = Never
AdmissibleFMRIConnectomeProxyRoute hiddenChartRecoveryRoute = Never
AdmissibleFMRIConnectomeProxyRoute mindReadingRoute = Never
AdmissibleFMRIConnectomeProxyRoute diagnosisRoute = Never
AdmissibleFMRIConnectomeProxyRoute treatmentRoute = Never
AdmissibleFMRIConnectomeProxyRoute clinicalAuthorityRoute = Never

fmriMeasurementProxyRouteRejected :
  AdmissibleFMRIConnectomeProxyRoute fmriMeasurementProxyRoute →
  Never
fmriMeasurementProxyRouteRejected impossible = impossible

boldSignalProxyRouteRejected :
  AdmissibleFMRIConnectomeProxyRoute boldSignalProxyRoute →
  Never
boldSignalProxyRouteRejected impossible = impossible

connectomeGraphProxyRouteRejected :
  AdmissibleFMRIConnectomeProxyRoute connectomeGraphProxyRoute →
  Never
connectomeGraphProxyRouteRejected impossible = impossible

functionalConnectivityProxyRouteRejected :
  AdmissibleFMRIConnectomeProxyRoute functionalConnectivityProxyRoute →
  Never
functionalConnectivityProxyRouteRejected impossible = impossible

reverseInferenceBoundaryRouteRejected :
  AdmissibleFMRIConnectomeProxyRoute reverseInferenceBoundaryRoute →
  Never
reverseInferenceBoundaryRouteRejected impossible = impossible

hiddenChartRecoveryRouteRejected :
  AdmissibleFMRIConnectomeProxyRoute hiddenChartRecoveryRoute →
  Never
hiddenChartRecoveryRouteRejected impossible = impossible

mindReadingRouteRejected :
  AdmissibleFMRIConnectomeProxyRoute mindReadingRoute →
  Never
mindReadingRouteRejected impossible = impossible

diagnosisRouteRejected :
  AdmissibleFMRIConnectomeProxyRoute diagnosisRoute →
  Never
diagnosisRouteRejected impossible = impossible

treatmentRouteRejected :
  AdmissibleFMRIConnectomeProxyRoute treatmentRoute →
  Never
treatmentRouteRejected impossible = impossible

clinicalAuthorityRouteRejected :
  AdmissibleFMRIConnectomeProxyRoute clinicalAuthorityRoute →
  Never
clinicalAuthorityRouteRejected impossible = impossible

data ProxyDomain : Set where
  fMRIDomain : ProxyDomain
  connectomeDomain : ProxyDomain
  functionalConnectivityDomain : ProxyDomain
  governanceBoundaryDomain : ProxyDomain

data ProxySurfaceKind : Set where
  measurementProxySurface : ProxySurfaceKind
  boldSignalProxySurface : ProxySurfaceKind
  connectomeGraphProxySurface : ProxySurfaceKind
  functionalConnectivityProxySurface : ProxySurfaceKind
  reverseInferenceBoundarySurface : ProxySurfaceKind

data ProxyRowTag : Set where
  fmriMeasurementRowTag : ProxyRowTag
  boldSignalRowTag : ProxyRowTag
  connectomeGraphRowTag : ProxyRowTag
  functionalConnectivityRowTag : ProxyRowTag
  reverseInferenceBoundaryRowTag : ProxyRowTag

data BoundaryClaimKind : Set where
  proxyIsNotHiddenChartClaim : BoundaryClaimKind
  measurementIsNotDiagnosisClaim : BoundaryClaimKind
  reverseInferenceBlockedClaim : BoundaryClaimKind
  hiddenChartRecoveryBlockedClaim : BoundaryClaimKind
  mindReadingBlockedClaim : BoundaryClaimKind
  clinicalAuthorityBlockedClaim : BoundaryClaimKind
  treatmentAuthorityBlockedClaim : BoundaryClaimKind

record ProxyPlacementRow : Set where
  constructor proxyPlacementRow
  field
    rowTag :
      ProxyRowTag

    rowDomain :
      ProxyDomain

    rowSurfaceKind :
      ProxySurfaceKind

    rowProxyIsNotHiddenChart :
      Bool

    rowProxyIsNotHiddenChartIsTrue :
      rowProxyIsNotHiddenChart ≡ true

    rowMeasurementIsNotDiagnosis :
      Bool

    rowMeasurementIsNotDiagnosisIsTrue :
      rowMeasurementIsNotDiagnosis ≡ true

    rowReverseInferenceBlocked :
      Bool

    rowReverseInferenceBlockedIsFalse :
      rowReverseInferenceBlocked ≡ false

    rowHiddenChartRecoveryBlocked :
      Bool

    rowHiddenChartRecoveryBlockedIsFalse :
      rowHiddenChartRecoveryBlocked ≡ false

    rowMindReadingBlocked :
      Bool

    rowMindReadingBlockedIsFalse :
      rowMindReadingBlocked ≡ false

    rowClinicalAuthorityBlocked :
      Bool

    rowClinicalAuthorityBlockedIsFalse :
      rowClinicalAuthorityBlocked ≡ false

    rowTreatmentAuthorityBlocked :
      Bool

    rowTreatmentAuthorityBlockedIsFalse :
      rowTreatmentAuthorityBlocked ≡ false

    rowReading :
      String

open ProxyPlacementRow public

record BOLDSignalProxySurface : Set₁ where
  constructor boldSignalProxySurface
  field
    SignalContext : Set
    BOLDField : Set
    HemodynamicTrace : Set
    AcquisitionProtocol : Set
    PreprocessingPipeline : Set
    ProxyMap : Set
    ResidualAudit : Set

    sample :
      SignalContext →
      BOLDField

    preprocess :
      BOLDField →
      BOLDField

    projectToProxy :
      BOLDField →
      ProxyMap

    auditResidual :
      BOLDField →
      ResidualAudit

    surfaceKind :
      ProxySurfaceKind

    measurementProxyOnly :
      Bool

    measurementProxyOnlyIsTrue :
      measurementProxyOnly ≡ true

    hiddenChartRecoveryBlocked :
      Bool

    hiddenChartRecoveryBlockedIsFalse :
      hiddenChartRecoveryBlocked ≡ false

    reverseInferenceBlocked :
      Bool

    reverseInferenceBlockedIsFalse :
      reverseInferenceBlocked ≡ false

    mindReadingBlocked :
      Bool

    mindReadingBlockedIsFalse :
      mindReadingBlocked ≡ false

    clinicalAuthorityBlocked :
      Bool

    clinicalAuthorityBlockedIsFalse :
      clinicalAuthorityBlocked ≡ false

    signalReading :
      String

open BOLDSignalProxySurface public

record FunctionalConnectivityProxyCarrier : Set₁ where
  constructor functionalConnectivityProxyCarrier
  field
    Node : Set
    Edge : Set
    Weight : Set
    StructuralGraph : Set
    FunctionalGraph : Set
    ConnectivityMap : Set
    GraphAlignment : Set

    structuralNode :
      StructuralGraph →
      Node

    structuralEdge :
      StructuralGraph →
      Node →
      Node →
      Edge

    structuralWeight :
      StructuralGraph →
      Edge →
      Weight

    functionalEdge :
      FunctionalGraph →
      Node →
      Node →
      Edge

    functionalWeight :
      FunctionalGraph →
      Edge →
      Weight

    functionalConnectivity :
      StructuralGraph →
      FunctionalGraph →
      ConnectivityMap

    graphAlignment :
      StructuralGraph →
      FunctionalGraph →
      GraphAlignment

    graphProxyOnly :
      Bool

    graphProxyOnlyIsTrue :
      graphProxyOnly ≡ true

    hiddenChartRecoveryBlocked :
      Bool

    hiddenChartRecoveryBlockedIsFalse :
      hiddenChartRecoveryBlocked ≡ false

    reverseInferenceBlocked :
      Bool

    reverseInferenceBlockedIsFalse :
      reverseInferenceBlocked ≡ false

    mindReadingBlocked :
      Bool

    mindReadingBlockedIsFalse :
      mindReadingBlocked ≡ false

    clinicalAuthorityBlocked :
      Bool

    clinicalAuthorityBlockedIsFalse :
      clinicalAuthorityBlocked ≡ false

    connectivityReading :
      String

open FunctionalConnectivityProxyCarrier public

record FMRIConnectomeProxyGovernance : Setω where
  field
    fMRIObservationBoundary :
      BrainFMRI.BrainConnectomeFMRIObservationBoundary

    fMRIObservationBoundaryIsCanonical :
      fMRIObservationBoundary ≡
      BrainFMRI.canonicalBrainConnectomeFMRIObservationBoundary

    measurementProxyBoundary :
      Measurement.BodyMemoryMeasurementProxyBoundary

    measurementProxyBoundaryIsCanonical :
      measurementProxyBoundary ≡
      Measurement.canonicalBodyMemoryMeasurementProxyBoundary

    functionalConnectomeBridge :
      Bridge.FunctionalConnectomeBodyMemoryBridge

    functionalConnectomeBridgeCanonicalReceipt :
      Bool

    functionalConnectomeBridgeCanonicalReceiptIsTrue :
      functionalConnectomeBridgeCanonicalReceipt ≡ true

    route :
      FMRIConnectomeProxyRoute

    routeIsCandidateOnly :
      route ≡ candidateOnlyRoute

    routeAdmissible :
      AdmissibleFMRIConnectomeProxyRoute route

    boldSignalSurface :
      BOLDSignalProxySurface

    connectivitySurface :
      FunctionalConnectivityProxyCarrier

    fmriMeasurementRow :
      ProxyPlacementRow

    boldSignalRow :
      ProxyPlacementRow

    connectomeGraphRow :
      ProxyPlacementRow

    functionalConnectivityRow :
      ProxyPlacementRow

    reverseInferenceBoundaryRow :
      ProxyPlacementRow

    canonicalRows :
      List ProxyPlacementRow

    canonicalRowsAreExact :
      canonicalRows ≡ canonicalRows

    proxyIsNotHiddenChart :
      Bool

    proxyIsNotHiddenChartIsTrue :
      proxyIsNotHiddenChart ≡ true

    measurementIsNotDiagnosis :
      Bool

    measurementIsNotDiagnosisIsTrue :
      measurementIsNotDiagnosis ≡ true

    reverseInferenceBlocked :
      Bool

    reverseInferenceBlockedIsFalse :
      reverseInferenceBlocked ≡ false

    hiddenChartRecoveryBlocked :
      Bool

    hiddenChartRecoveryBlockedIsFalse :
      hiddenChartRecoveryBlocked ≡ false

    mindReadingBlocked :
      Bool

    mindReadingBlockedIsFalse :
      mindReadingBlocked ≡ false

    clinicalAuthorityBlocked :
      Bool

    clinicalAuthorityBlockedIsFalse :
      clinicalAuthorityBlocked ≡ false

    treatmentAuthorityBlocked :
      Bool

    treatmentAuthorityBlockedIsFalse :
      treatmentAuthorityBlocked ≡ false

    boundaryClaims :
      List BoundaryClaimKind

    boundaryClaimsAreExact :
      boundaryClaims ≡ boundaryClaims

    governanceReading :
      String

open FMRIConnectomeProxyGovernance public

canonicalBOLDSignalProxySurface : BOLDSignalProxySurface
canonicalBOLDSignalProxySurface =
  boldSignalProxySurface
    ⊤
    ⊤
    ⊤
    ⊤
    ⊤
    ⊤
    ⊤
    (λ _ → tt)
    (λ signal → signal)
    (λ _ → tt)
    (λ _ → tt)
    measurementProxySurface
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "BOLD is treated as a signal proxy for measurement and not as hidden-chart recovery, reverse inference, mind-reading, diagnosis, or clinical authority."

canonicalFunctionalConnectivityProxyCarrier : FunctionalConnectivityProxyCarrier
canonicalFunctionalConnectivityProxyCarrier =
  functionalConnectivityProxyCarrier
    ⊤
    ⊤
    ⊤
    ⊤
    ⊤
    ⊤
    ⊤
    (λ _ → tt)
    (λ _ _ _ → tt)
    (λ _ _ → tt)
    (λ _ _ _ → tt)
    (λ _ _ → tt)
    (λ _ _ → tt)
    (λ _ _ → tt)
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "Functional connectivity is retained as a graph proxy carrier only: structural and functional graphs can be aligned, but alignment is not reverse inference, mind-reading, or clinical authority."

canonicalFMRIMeasurementRow : ProxyPlacementRow
canonicalFMRIMeasurementRow =
  proxyPlacementRow
    fmriMeasurementRowTag
    fMRIDomain
    measurementProxySurface
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "fMRI measurement is a proxy surface, not a hidden chart."

canonicalBOLDSignalRow : ProxyPlacementRow
canonicalBOLDSignalRow =
  proxyPlacementRow
    boldSignalRowTag
    fMRIDomain
    boldSignalProxySurface
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "BOLD is a signal proxy over hemodynamic change, not an inference engine."

canonicalConnectomeGraphRow : ProxyPlacementRow
canonicalConnectomeGraphRow =
  proxyPlacementRow
    connectomeGraphRowTag
    connectomeDomain
    connectomeGraphProxySurface
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "The connectome is a graph proxy carrier for structure/function coupling, not hidden-chart recovery."

canonicalFunctionalConnectivityRow : ProxyPlacementRow
canonicalFunctionalConnectivityRow =
  proxyPlacementRow
    functionalConnectivityRowTag
    functionalConnectivityDomain
    functionalConnectivityProxySurface
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "Functional connectivity is a proxy relation over observed coupling, not mind-reading or clinical authority."

canonicalReverseInferenceBoundaryRow : ProxyPlacementRow
canonicalReverseInferenceBoundaryRow =
  proxyPlacementRow
    reverseInferenceBoundaryRowTag
    governanceBoundaryDomain
    reverseInferenceBoundarySurface
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "Reverse inference remains a boundary, not a promoted authority."

canonicalFMRIConnectomeProxyRows :
  List ProxyPlacementRow
canonicalFMRIConnectomeProxyRows =
  canonicalFMRIMeasurementRow
  ∷ canonicalBOLDSignalRow
  ∷ canonicalConnectomeGraphRow
  ∷ canonicalFunctionalConnectivityRow
  ∷ canonicalReverseInferenceBoundaryRow
  ∷ []

canonicalBoundaryClaims : List BoundaryClaimKind
canonicalBoundaryClaims =
  proxyIsNotHiddenChartClaim
  ∷ measurementIsNotDiagnosisClaim
  ∷ reverseInferenceBlockedClaim
  ∷ hiddenChartRecoveryBlockedClaim
  ∷ mindReadingBlockedClaim
  ∷ clinicalAuthorityBlockedClaim
  ∷ treatmentAuthorityBlockedClaim
  ∷ []

canonicalFMRIConnectomeProxyGovernance :
  FMRIConnectomeProxyGovernance
canonicalFMRIConnectomeProxyGovernance =
  record
    { fMRIObservationBoundary =
        BrainFMRI.canonicalBrainConnectomeFMRIObservationBoundary
    ; fMRIObservationBoundaryIsCanonical =
        refl
    ; measurementProxyBoundary =
        Measurement.canonicalBodyMemoryMeasurementProxyBoundary
    ; measurementProxyBoundaryIsCanonical =
        refl
    ; functionalConnectomeBridge =
        Bridge.canonicalFunctionalConnectomeBodyMemoryBridge
    ; functionalConnectomeBridgeCanonicalReceipt =
        true
    ; functionalConnectomeBridgeCanonicalReceiptIsTrue =
        refl
    ; route =
        candidateOnlyRoute
    ; routeIsCandidateOnly =
        refl
    ; routeAdmissible =
        tt
    ; boldSignalSurface =
        canonicalBOLDSignalProxySurface
    ; connectivitySurface =
        canonicalFunctionalConnectivityProxyCarrier
    ; fmriMeasurementRow =
        canonicalFMRIMeasurementRow
    ; boldSignalRow =
        canonicalBOLDSignalRow
    ; connectomeGraphRow =
        canonicalConnectomeGraphRow
    ; functionalConnectivityRow =
        canonicalFunctionalConnectivityRow
    ; reverseInferenceBoundaryRow =
        canonicalReverseInferenceBoundaryRow
    ; canonicalRows =
        canonicalFMRIConnectomeProxyRows
    ; canonicalRowsAreExact =
        refl
    ; proxyIsNotHiddenChart =
        true
    ; proxyIsNotHiddenChartIsTrue =
        refl
    ; measurementIsNotDiagnosis =
        true
    ; measurementIsNotDiagnosisIsTrue =
        refl
    ; reverseInferenceBlocked =
        false
    ; reverseInferenceBlockedIsFalse =
        refl
    ; hiddenChartRecoveryBlocked =
        false
    ; hiddenChartRecoveryBlockedIsFalse =
        refl
    ; mindReadingBlocked =
        false
    ; mindReadingBlockedIsFalse =
        refl
    ; clinicalAuthorityBlocked =
        false
    ; clinicalAuthorityBlockedIsFalse =
        refl
    ; treatmentAuthorityBlocked =
        false
    ; treatmentAuthorityBlockedIsFalse =
        refl
    ; boundaryClaims =
        canonicalBoundaryClaims
    ; boundaryClaimsAreExact =
        refl
    ; governanceReading =
        "Candidate-only governance for fMRI, BOLD, connectome graph, and functional connectivity placement: the surface remains a proxy and boundary layer, not hidden-chart recovery, reverse inference authority, mind-reading, diagnosis, treatment, or clinical authority."
    }
