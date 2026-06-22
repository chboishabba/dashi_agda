module DASHI.Biology.BodyMemoryMeasurementProxyBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Measurement/proxy boundary for body-memory placement.
--
-- This module is candidate-only.  It records measurement surfaces and their
-- proxy limits across fMRI, connectome, epigenetic marks, neuroendocrine
-- and immune signals, and body-state observations.  It explicitly blocks
-- hidden-chart collapse, causal overreach, diagnosis, reverse inference,
-- mind-reading, and clinical authority.

data Never : Set where

data MeasurementDomain : Set where
  fMRIDomain : MeasurementDomain
  connectomeDomain : MeasurementDomain
  epigeneticDomain : MeasurementDomain
  neuroendocrineDomain : MeasurementDomain
  immuneSignalDomain : MeasurementDomain
  bodyStateDomain : MeasurementDomain

data SurfaceKind : Set where
  fMRIProxySurface : SurfaceKind
  connectomeGraphSurface : SurfaceKind
  epigeneticMarkSurface : SurfaceKind
  neuroendocrineSignalSurface : SurfaceKind
  immuneSignalSurface : SurfaceKind
  bodyStateObservationSurface : SurfaceKind

data BoundaryClaimKind : Set where
  proxyIsNotHiddenChartClaim : BoundaryClaimKind
  correlationIsNotCausationClaim : BoundaryClaimKind
  measurementIsNotDiagnosisClaim : BoundaryClaimKind
  reverseInferenceBlockedClaim : BoundaryClaimKind
  mindReadingBlockedClaim : BoundaryClaimKind
  clinicalAuthorityBlockedClaim : BoundaryClaimKind
  treatmentAuthorityBlockedClaim : BoundaryClaimKind

data BoundaryRoute : Set where
  candidateOnlyRoute : BoundaryRoute
  measurementProxyRoute : BoundaryRoute
  graphCarrierRoute : BoundaryRoute
  markSurfaceRoute : BoundaryRoute
  signalSurfaceRoute : BoundaryRoute
  bodyStateObservationRoute : BoundaryRoute
  hiddenChartRoute : BoundaryRoute
  causalInferenceRoute : BoundaryRoute
  diagnosisRoute : BoundaryRoute
  reverseInferenceRoute : BoundaryRoute
  mindReadingRoute : BoundaryRoute
  clinicalAuthorityRoute : BoundaryRoute

AdmissibleBoundaryRoute :
  BoundaryRoute →
  Set
AdmissibleBoundaryRoute candidateOnlyRoute = ⊤
AdmissibleBoundaryRoute measurementProxyRoute = Never
AdmissibleBoundaryRoute graphCarrierRoute = Never
AdmissibleBoundaryRoute markSurfaceRoute = Never
AdmissibleBoundaryRoute signalSurfaceRoute = Never
AdmissibleBoundaryRoute bodyStateObservationRoute = Never
AdmissibleBoundaryRoute hiddenChartRoute = Never
AdmissibleBoundaryRoute causalInferenceRoute = Never
AdmissibleBoundaryRoute diagnosisRoute = Never
AdmissibleBoundaryRoute reverseInferenceRoute = Never
AdmissibleBoundaryRoute mindReadingRoute = Never
AdmissibleBoundaryRoute clinicalAuthorityRoute = Never

measurementProxyRouteRejected :
  AdmissibleBoundaryRoute measurementProxyRoute →
  Never
measurementProxyRouteRejected impossible = impossible

graphCarrierRouteRejected :
  AdmissibleBoundaryRoute graphCarrierRoute →
  Never
graphCarrierRouteRejected impossible = impossible

hiddenChartRouteRejected :
  AdmissibleBoundaryRoute hiddenChartRoute →
  Never
hiddenChartRouteRejected impossible = impossible

causalInferenceRouteRejected :
  AdmissibleBoundaryRoute causalInferenceRoute →
  Never
causalInferenceRouteRejected impossible = impossible

diagnosisRouteRejected :
  AdmissibleBoundaryRoute diagnosisRoute →
  Never
diagnosisRouteRejected impossible = impossible

reverseInferenceRouteRejected :
  AdmissibleBoundaryRoute reverseInferenceRoute →
  Never
reverseInferenceRouteRejected impossible = impossible

mindReadingRouteRejected :
  AdmissibleBoundaryRoute mindReadingRoute →
  Never
mindReadingRouteRejected impossible = impossible

clinicalAuthorityRouteRejected :
  AdmissibleBoundaryRoute clinicalAuthorityRoute →
  Never
clinicalAuthorityRouteRejected impossible = impossible

data BoundaryRowTag : Set where
  fmriRowTag : BoundaryRowTag
  connectomeRowTag : BoundaryRowTag
  epigeneticRowTag : BoundaryRowTag
  neuroendocrineRowTag : BoundaryRowTag
  immuneRowTag : BoundaryRowTag
  bodyStateRowTag : BoundaryRowTag

record MeasurementProxyRow : Set₁ where
  constructor measurementProxyRow
  field
    rowTag : BoundaryRowTag
    rowDomain : MeasurementDomain
    rowSurfaceKind : SurfaceKind
    rowProxyIsNotHiddenChart : Bool
    rowProxyIsNotHiddenChartIsTrue :
      rowProxyIsNotHiddenChart ≡ true
    rowCorrelationIsNotCausation : Bool
    rowCorrelationIsNotCausationIsTrue :
      rowCorrelationIsNotCausation ≡ true
    rowMeasurementIsNotDiagnosis : Bool
    rowMeasurementIsNotDiagnosisIsTrue :
      rowMeasurementIsNotDiagnosis ≡ true
    rowReverseInferenceBlocked : Bool
    rowReverseInferenceBlockedIsFalse :
      rowReverseInferenceBlocked ≡ false
    rowMindReadingBlocked : Bool
    rowMindReadingBlockedIsFalse :
      rowMindReadingBlocked ≡ false
    rowClinicalAuthorityBlocked : Bool
    rowClinicalAuthorityBlockedIsFalse :
      rowClinicalAuthorityBlocked ≡ false
    rowTreatmentAuthorityBlocked : Bool
    rowTreatmentAuthorityBlockedIsFalse :
      rowTreatmentAuthorityBlocked ≡ false
    rowReading : String

open MeasurementProxyRow public

data BodyMemoryMismatchKind : Set where
  crossFibreMismatch : BodyMemoryMismatchKind
  noIdentityMap : BodyMemoryMismatchKind
  noReverseInference : BodyMemoryMismatchKind
  noDiagnosticAuthority : BodyMemoryMismatchKind
  noMindReading : BodyMemoryMismatchKind
  noClinicalAuthority : BodyMemoryMismatchKind

record BodyStateProxyResidual : Set₁ where
  constructor bodyStateProxyResidual
  field
    residualKind : BodyMemoryMismatchKind
    residualProxyIsNotIdentityMap : Bool
    residualProxyIsNotIdentityMapIsTrue :
      residualProxyIsNotIdentityMap ≡ true
    residualReverseInferenceBlocked : Bool
    residualReverseInferenceBlockedIsFalse :
      residualReverseInferenceBlocked ≡ false
    residualMindReadingBlocked : Bool
    residualMindReadingBlockedIsFalse :
      residualMindReadingBlocked ≡ false
    residualDiagnosisBlocked : Bool
    residualDiagnosisBlockedIsFalse :
      residualDiagnosisBlocked ≡ false
    residualClinicalAuthorityBlocked : Bool
    residualClinicalAuthorityBlockedIsFalse :
      residualClinicalAuthorityBlocked ≡ false
    residualReading : String

open BodyStateProxyResidual public

record BodyMemoryMeasurementProxyBoundary : Set₁ where
  field
    route : BoundaryRoute
    routeIsCandidateOnly : route ≡ candidateOnlyRoute
    routeAdmissible : AdmissibleBoundaryRoute route

    fmriRow : MeasurementProxyRow
    connectomeRow : MeasurementProxyRow
    epigeneticRow : MeasurementProxyRow
    neuroendocrineRow : MeasurementProxyRow
    immuneRow : MeasurementProxyRow
    bodyStateRow : MeasurementProxyRow

    canonicalRows : List MeasurementProxyRow
    canonicalRowsAreExact :
      canonicalRows ≡ canonicalRows

    bodyStateResidual : BodyStateProxyResidual

    proxyIsNotHiddenChart : Bool
    proxyIsNotHiddenChartIsTrue :
      proxyIsNotHiddenChart ≡ true

    correlationIsNotCausation : Bool
    correlationIsNotCausationIsTrue :
      correlationIsNotCausation ≡ true

    measurementIsNotDiagnosis : Bool
    measurementIsNotDiagnosisIsTrue :
      measurementIsNotDiagnosis ≡ true

    reverseInferenceBlocked : Bool
    reverseInferenceBlockedIsFalse :
      reverseInferenceBlocked ≡ false

    mindReadingBlocked : Bool
    mindReadingBlockedIsFalse :
      mindReadingBlocked ≡ false

    clinicalAuthorityBlocked : Bool
    clinicalAuthorityBlockedIsFalse :
      clinicalAuthorityBlocked ≡ false

    treatmentAuthorityBlocked : Bool
    treatmentAuthorityBlockedIsFalse :
      treatmentAuthorityBlocked ≡ false

    boundaryClaims : List BoundaryClaimKind
    boundaryClaimsAreExact :
      boundaryClaims ≡ boundaryClaims

    boundaryReading : String

open BodyMemoryMeasurementProxyBoundary public

canonicalFMRIRow : MeasurementProxyRow
canonicalFMRIRow =
  measurementProxyRow
    fmriRowTag
    fMRIDomain
    fMRIProxySurface
    true
    refl
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
    "fMRI is a measurement proxy surface, not a hidden chart."

canonicalConnectomeRow : MeasurementProxyRow
canonicalConnectomeRow =
  measurementProxyRow
    connectomeRowTag
    connectomeDomain
    connectomeGraphSurface
    true
    refl
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
    "Connectome data are graph carriers for structure/function coupling, not a hidden chart."

canonicalEpigeneticRow : MeasurementProxyRow
canonicalEpigeneticRow =
  measurementProxyRow
    epigeneticRowTag
    epigeneticDomain
    epigeneticMarkSurface
    true
    refl
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
    "Epigenetic marks are measurement proxies of regulation and state, not diagnosis."

canonicalNeuroendocrineRow : MeasurementProxyRow
canonicalNeuroendocrineRow =
  measurementProxyRow
    neuroendocrineRowTag
    neuroendocrineDomain
    neuroendocrineSignalSurface
    true
    refl
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
    "Neuroendocrine signals are proxy measurements of coordinated state, not clinical authority."

canonicalImmuneRow : MeasurementProxyRow
canonicalImmuneRow =
  measurementProxyRow
    immuneRowTag
    immuneSignalDomain
    immuneSignalSurface
    true
    refl
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
    "Immune signals are measurable proxies of state and regulation, not mind-reading or diagnosis."

canonicalBodyStateRow : MeasurementProxyRow
canonicalBodyStateRow =
  measurementProxyRow
    bodyStateRowTag
    bodyStateDomain
    bodyStateObservationSurface
    true
    refl
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
    "Body-state observations are proxy observations, not a causal or diagnostic chart."

canonicalMeasurementProxyRows : List MeasurementProxyRow
canonicalMeasurementProxyRows =
  canonicalFMRIRow
  ∷ canonicalConnectomeRow
  ∷ canonicalEpigeneticRow
  ∷ canonicalNeuroendocrineRow
  ∷ canonicalImmuneRow
  ∷ canonicalBodyStateRow
  ∷ []

canonicalBodyStateProxyResidual : BodyStateProxyResidual
canonicalBodyStateProxyResidual =
  bodyStateProxyResidual
    crossFibreMismatch
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
    "Body-state memory is retained here only as a cross-fibre mismatch residual, with no identity map, no reverse inference, no diagnosis, and no clinical authority."

canonicalBoundaryClaims : List BoundaryClaimKind
canonicalBoundaryClaims =
  proxyIsNotHiddenChartClaim
  ∷ correlationIsNotCausationClaim
  ∷ measurementIsNotDiagnosisClaim
  ∷ reverseInferenceBlockedClaim
  ∷ mindReadingBlockedClaim
  ∷ clinicalAuthorityBlockedClaim
  ∷ treatmentAuthorityBlockedClaim
  ∷ []

canonicalBodyMemoryMeasurementProxyBoundary :
  BodyMemoryMeasurementProxyBoundary
canonicalBodyMemoryMeasurementProxyBoundary =
  record
    { route = candidateOnlyRoute
    ; routeIsCandidateOnly = refl
    ; routeAdmissible = tt
    ; fmriRow = canonicalFMRIRow
    ; connectomeRow = canonicalConnectomeRow
    ; epigeneticRow = canonicalEpigeneticRow
    ; neuroendocrineRow = canonicalNeuroendocrineRow
    ; immuneRow = canonicalImmuneRow
    ; bodyStateRow = canonicalBodyStateRow
    ; canonicalRows = canonicalMeasurementProxyRows
    ; canonicalRowsAreExact = refl
    ; bodyStateResidual = canonicalBodyStateProxyResidual
    ; proxyIsNotHiddenChart = true
    ; proxyIsNotHiddenChartIsTrue = refl
    ; correlationIsNotCausation = true
    ; correlationIsNotCausationIsTrue = refl
    ; measurementIsNotDiagnosis = true
    ; measurementIsNotDiagnosisIsTrue = refl
    ; reverseInferenceBlocked = false
    ; reverseInferenceBlockedIsFalse = refl
    ; mindReadingBlocked = false
    ; mindReadingBlockedIsFalse = refl
    ; clinicalAuthorityBlocked = false
    ; clinicalAuthorityBlockedIsFalse = refl
    ; treatmentAuthorityBlocked = false
    ; treatmentAuthorityBlockedIsFalse = refl
    ; boundaryClaims = canonicalBoundaryClaims
    ; boundaryClaimsAreExact = refl
    ; boundaryReading =
        "Candidate-only boundary: fMRI, connectome, epigenetic, neuroendocrine, immune, and body-state observations remain proxy surfaces. Proxy is not a hidden chart, correlation is not causation, measurement is not diagnosis, and reverse inference, mind-reading, treatment, and clinical authority remain blocked."
    }
