module DASHI.Biology.PopulationLongitudinalBOLDResidualBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.BodyMemoryBiologyRegression as Regression
import DASHI.Biology.FMRIConnectomeProxyGovernance as Governance

------------------------------------------------------------------------
-- Population / longitudinal BOLD residual bridge.
--
-- Candidate-only surface:
--   - BOLDSignal witnesses neural/vascular proxy variation
--   - population and longitudinal strata support bounded drift and cohort
--     association rows
--   - the lane does not promote individual diagnosis, hidden chart recovery,
--     causal closure, or mind-reading
--
-- This module is intentionally standalone apart from the existing governance
-- import.  It keeps the BOLD proxy lane fail-closed and reuses the canonical
-- fMRI/connectome governance record as an imported boundary witness.

data Never : Set where

------------------------------------------------------------------------
-- Routes and admissibility.

data PopulationLongitudinalRoute : Set where
  candidateOnlyRoute : PopulationLongitudinalRoute
  boldProxyRoute : PopulationLongitudinalRoute
  neuralVascularProxyRoute : PopulationLongitudinalRoute
  populationCohortRoute : PopulationLongitudinalRoute
  boundedDriftRoute : PopulationLongitudinalRoute
  individualDiagnosisRoute : PopulationLongitudinalRoute
  hiddenChartRecoveryRoute : PopulationLongitudinalRoute
  causalClosureRoute : PopulationLongitudinalRoute
  mindReadingRoute : PopulationLongitudinalRoute
  treatmentRoute : PopulationLongitudinalRoute

AdmissiblePopulationLongitudinalRoute :
  PopulationLongitudinalRoute →
  Set
AdmissiblePopulationLongitudinalRoute candidateOnlyRoute = ⊤
AdmissiblePopulationLongitudinalRoute boldProxyRoute = Never
AdmissiblePopulationLongitudinalRoute neuralVascularProxyRoute = Never
AdmissiblePopulationLongitudinalRoute populationCohortRoute = Never
AdmissiblePopulationLongitudinalRoute boundedDriftRoute = Never
AdmissiblePopulationLongitudinalRoute individualDiagnosisRoute = Never
AdmissiblePopulationLongitudinalRoute hiddenChartRecoveryRoute = Never
AdmissiblePopulationLongitudinalRoute causalClosureRoute = Never
AdmissiblePopulationLongitudinalRoute mindReadingRoute = Never
AdmissiblePopulationLongitudinalRoute treatmentRoute = Never

boldProxyRouteRejected :
  AdmissiblePopulationLongitudinalRoute boldProxyRoute →
  Never
boldProxyRouteRejected impossible = impossible

neuralVascularProxyRouteRejected :
  AdmissiblePopulationLongitudinalRoute neuralVascularProxyRoute →
  Never
neuralVascularProxyRouteRejected impossible = impossible

populationCohortRouteRejected :
  AdmissiblePopulationLongitudinalRoute populationCohortRoute →
  Never
populationCohortRouteRejected impossible = impossible

boundedDriftRouteRejected :
  AdmissiblePopulationLongitudinalRoute boundedDriftRoute →
  Never
boundedDriftRouteRejected impossible = impossible

individualDiagnosisRouteRejected :
  AdmissiblePopulationLongitudinalRoute individualDiagnosisRoute →
  Never
individualDiagnosisRouteRejected impossible = impossible

hiddenChartRecoveryRouteRejected :
  AdmissiblePopulationLongitudinalRoute hiddenChartRecoveryRoute →
  Never
hiddenChartRecoveryRouteRejected impossible = impossible

causalClosureRouteRejected :
  AdmissiblePopulationLongitudinalRoute causalClosureRoute →
  Never
causalClosureRouteRejected impossible = impossible

mindReadingRouteRejected :
  AdmissiblePopulationLongitudinalRoute mindReadingRoute →
  Never
mindReadingRouteRejected impossible = impossible

treatmentRouteRejected :
  AdmissiblePopulationLongitudinalRoute treatmentRoute →
  Never
treatmentRouteRejected impossible = impossible

------------------------------------------------------------------------
-- Temporal and population vocabularies.

data SamplingWindow : Set where
  baselineWindow : SamplingWindow
  earlyWindow : SamplingWindow
  midWindow : SamplingWindow
  lateWindow : SamplingWindow
  driftWindow : SamplingWindow

data CohortStratum : Set where
  populationBaselineStratum : CohortStratum
  ageBandStratum : CohortStratum
  siteStratum : CohortStratum
  scannerStratum : CohortStratum
  conditionStratum : CohortStratum
  treatmentExposureStratum : CohortStratum
  longitudinalFollowUpStratum : CohortStratum

data DriftBoundKind : Set where
  boundedMeanShift : DriftBoundKind
  boundedVarianceShift : DriftBoundKind
  boundedSignalOffset : DriftBoundKind
  boundedCohortDifference : DriftBoundKind
  boundedResidualSlope : DriftBoundKind

data AssociationKind : Set where
  cohortAssociationKind : AssociationKind
  temporalAssociationKind : AssociationKind
  crossSectionalAssociationKind : AssociationKind
  driftAssociationKind : AssociationKind
  boundedResidualAssociationKind : AssociationKind

canonicalSamplingWindows :
  List SamplingWindow
canonicalSamplingWindows =
  baselineWindow
  ∷ earlyWindow
  ∷ midWindow
  ∷ lateWindow
  ∷ driftWindow
  ∷ []

canonicalCohortStrata :
  List CohortStratum
canonicalCohortStrata =
  populationBaselineStratum
  ∷ ageBandStratum
  ∷ siteStratum
  ∷ scannerStratum
  ∷ conditionStratum
  ∷ treatmentExposureStratum
  ∷ longitudinalFollowUpStratum
  ∷ []

canonicalDriftBoundKinds :
  List DriftBoundKind
canonicalDriftBoundKinds =
  boundedMeanShift
  ∷ boundedVarianceShift
  ∷ boundedSignalOffset
  ∷ boundedCohortDifference
  ∷ boundedResidualSlope
  ∷ []

canonicalAssociationKinds :
  List AssociationKind
canonicalAssociationKinds =
  cohortAssociationKind
  ∷ temporalAssociationKind
  ∷ crossSectionalAssociationKind
  ∷ driftAssociationKind
  ∷ boundedResidualAssociationKind
  ∷ []

samplingWindowName :
  SamplingWindow →
  String
samplingWindowName baselineWindow =
  "baseline window"
samplingWindowName earlyWindow =
  "early window"
samplingWindowName midWindow =
  "mid window"
samplingWindowName lateWindow =
  "late window"
samplingWindowName driftWindow =
  "drift window"

cohortStratumName :
  CohortStratum →
  String
cohortStratumName populationBaselineStratum =
  "population baseline stratum"
cohortStratumName ageBandStratum =
  "age-band stratum"
cohortStratumName siteStratum =
  "site stratum"
cohortStratumName scannerStratum =
  "scanner stratum"
cohortStratumName conditionStratum =
  "condition stratum"
cohortStratumName treatmentExposureStratum =
  "treatment-exposure stratum"
cohortStratumName longitudinalFollowUpStratum =
  "longitudinal follow-up stratum"

driftBoundKindName :
  DriftBoundKind →
  String
driftBoundKindName boundedMeanShift =
  "bounded mean shift"
driftBoundKindName boundedVarianceShift =
  "bounded variance shift"
driftBoundKindName boundedSignalOffset =
  "bounded signal offset"
driftBoundKindName boundedCohortDifference =
  "bounded cohort difference"
driftBoundKindName boundedResidualSlope =
  "bounded residual slope"

associationKindName :
  AssociationKind →
  String
associationKindName cohortAssociationKind =
  "cohort association"
associationKindName temporalAssociationKind =
  "temporal association"
associationKindName crossSectionalAssociationKind =
  "cross-sectional association"
associationKindName driftAssociationKind =
  "drift association"
associationKindName boundedResidualAssociationKind =
  "bounded residual association"

------------------------------------------------------------------------
-- Typed rows.

record PopulationBOLDResidualRow : Set where
  constructor mkPopulationBOLDResidualRow
  field
    rowIndex :
      Nat

    rowWindow :
      SamplingWindow

    rowCohort :
      CohortStratum

    rowDriftBound :
      DriftBoundKind

    rowAssociation :
      AssociationKind

    rowLabel :
      String

    rowClaim :
      String

    rowBOLDSignalWitness :
      Bool

    rowBOLDSignalWitnessIsTrue :
      rowBOLDSignalWitness ≡ true

    rowNeuralVascularProxyWitness :
      Bool

    rowNeuralVascularProxyWitnessIsTrue :
      rowNeuralVascularProxyWitness ≡ true

    rowNoIndividualDiagnosis :
      Bool

    rowNoIndividualDiagnosisIsFalse :
      rowNoIndividualDiagnosis ≡ false

    rowNoTraumaMechanism :
      Bool

    rowNoTraumaMechanismIsFalse :
      rowNoTraumaMechanism ≡ false

    rowNoHiddenChartRecovery :
      Bool

    rowNoHiddenChartRecoveryIsFalse :
      rowNoHiddenChartRecovery ≡ false

    rowNoCausalClosure :
      Bool

    rowNoCausalClosureIsFalse :
      rowNoCausalClosure ≡ false

    rowNoMindReading :
      Bool

    rowNoMindReadingIsFalse :
      rowNoMindReading ≡ false

    rowNotes :
      List String

open PopulationBOLDResidualRow public

record PopulationLongitudinalBOLDResidualCertificate : Set where
  constructor mkPopulationLongitudinalBOLDResidualCertificate
  field
    certificateLabel :
      String

    certificateRoute :
      PopulationLongitudinalRoute

    certificateRouteIsCandidateOnly :
      certificateRoute ≡ candidateOnlyRoute

    certificateBOLDProxy :
      Bool

    certificateBOLDProxyIsTrue :
      certificateBOLDProxy ≡ true

    certificateNoIndividualDiagnosis :
      Bool

    certificateNoIndividualDiagnosisIsFalse :
      certificateNoIndividualDiagnosis ≡ false

    certificateNoTraumaMechanism :
      Bool

    certificateNoTraumaMechanismIsFalse :
      certificateNoTraumaMechanism ≡ false

    certificateNoHiddenChartRecovery :
      Bool

    certificateNoHiddenChartRecoveryIsFalse :
      certificateNoHiddenChartRecovery ≡ false

    certificateNoCausalClosure :
      Bool

    certificateNoCausalClosureIsFalse :
      certificateNoCausalClosure ≡ false

    certificateNoMindReading :
      Bool

    certificateNoMindReadingIsFalse :
      certificateNoMindReading ≡ false

    certificateSummary :
      String

open PopulationLongitudinalBOLDResidualCertificate public

record PopulationLongitudinalBOLDResidualBridge : Setω where
  field
    governance :
      Governance.FMRIConnectomeProxyGovernance

    governanceIsCanonical :
      Bool

    regressionReceipt :
      Regression.BodyMemoryRegressionReceipt

    regressionReceiptIsCanonical :
      Bool

    route :
      PopulationLongitudinalRoute

    routeIsCandidateOnly :
      route ≡ candidateOnlyRoute

    routeAdmissible :
      AdmissiblePopulationLongitudinalRoute route

    samplingWindows :
      List SamplingWindow

    samplingWindowsAreCanonical :
      samplingWindows ≡ canonicalSamplingWindows

    cohortStrata :
      List CohortStratum

    cohortStrataAreCanonical :
      cohortStrata ≡ canonicalCohortStrata

    driftBoundKinds :
      List DriftBoundKind

    driftBoundKindsAreCanonical :
      driftBoundKinds ≡ canonicalDriftBoundKinds

    associationKinds :
      List AssociationKind

    associationKindsAreCanonical :
      associationKinds ≡ canonicalAssociationKinds

    rows :
      List PopulationBOLDResidualRow

    rowsAreCanonical :
      rows ≡ rows

    nonPromotionCertificate :
      PopulationLongitudinalBOLDResidualCertificate

    bridgeReading :
      String

open PopulationLongitudinalBOLDResidualBridge public

------------------------------------------------------------------------
-- Canonical rows.

canonicalPopulationBaselineRow :
  PopulationBOLDResidualRow
canonicalPopulationBaselineRow =
  mkPopulationBOLDResidualRow
    zero
    baselineWindow
    populationBaselineStratum
    boundedMeanShift
    cohortAssociationKind
    "population baseline row"
    "BOLDSignal witnesses neural/vascular proxy variation at population baseline, not a longitudinal trauma mechanism."
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
    ( "population baseline"
    ∷ "candidate-only proxy variation"
    ∷ "no diagnosis, hidden chart recovery, causal closure, or mind-reading"
    ∷ []
    )

canonicalAgeBandDriftRow :
  PopulationBOLDResidualRow
canonicalAgeBandDriftRow =
  mkPopulationBOLDResidualRow
    (suc zero)
    earlyWindow
    ageBandStratum
    boundedVarianceShift
    temporalAssociationKind
    "age-band drift row"
    "Longitudinal drift is bounded and cohort-linked, not individual diagnosis."
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
    ( "age-band cohort view"
    ∷ "drift stays bounded and proxy-only"
    ∷ "no mind-reading, no treatment, no causal closure"
    ∷ []
    )

canonicalSiteStratumAssociationRow :
  PopulationBOLDResidualRow
canonicalSiteStratumAssociationRow =
  mkPopulationBOLDResidualRow
    (suc (suc zero))
    midWindow
    siteStratum
    boundedCohortDifference
    crossSectionalAssociationKind
    "site stratum association row"
    "Site-level association is retained as a cohort proxy, not hidden chart recovery."
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
    ( "site stratum"
    ∷ "cohort association only"
    ∷ "no reverse inference or hidden chart recovery"
    ∷ []
    )

canonicalScannerDriftRow :
  PopulationBOLDResidualRow
canonicalScannerDriftRow =
  mkPopulationBOLDResidualRow
    (suc (suc (suc zero)))
    lateWindow
    scannerStratum
    boundedSignalOffset
    driftAssociationKind
    "scanner drift row"
    "Scanner drift is treated as bounded signal offset, not causal closure."
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
    ( "scanner stratum"
    ∷ "bounded signal offset only"
    ∷ "no causal closure or diagnosis"
    ∷ []
    )

canonicalConditionFollowUpRow :
  PopulationBOLDResidualRow
canonicalConditionFollowUpRow =
  mkPopulationBOLDResidualRow
    (suc (suc (suc (suc zero))))
    driftWindow
    conditionStratum
    boundedResidualSlope
    boundedResidualAssociationKind
    "condition follow-up row"
    "Condition-linked follow-up remains a bounded residual association, not a diagnosis."
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
    ( "condition follow-up"
    ∷ "residual slope remains bounded"
    ∷ "no hidden chart recovery or treatment authority"
    ∷ []
    )

canonicalTreatmentExposureGuardRow :
  PopulationBOLDResidualRow
canonicalTreatmentExposureGuardRow =
  mkPopulationBOLDResidualRow
    (suc (suc (suc (suc (suc zero)))))
    driftWindow
    treatmentExposureStratum
    boundedResidualSlope
    cohortAssociationKind
    "treatment-exposure guard row"
    "Treatment exposure is only a candidate cohort marker, not treatment authority."
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
    ( "treatment-exposure stratum"
    ∷ "exposure is not treatment authority"
    ∷ "no individual diagnosis or causal closure"
    ∷ []
    )

canonicalFollowUpResidualRow :
  PopulationBOLDResidualRow
canonicalFollowUpResidualRow =
  mkPopulationBOLDResidualRow
    (suc (suc (suc (suc (suc (suc zero))))))
    driftWindow
    longitudinalFollowUpStratum
    boundedVarianceShift
    temporalAssociationKind
    "longitudinal follow-up row"
    "Longitudinal follow-up tracks bounded drift over time, not mind-reading."
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
    ( "longitudinal follow-up"
    ∷ "bounded over time"
    ∷ "not mind-reading, causal closure, or diagnosis"
    ∷ []
    )

canonicalPopulationBOLDResidualRows :
  List PopulationBOLDResidualRow
canonicalPopulationBOLDResidualRows =
  canonicalPopulationBaselineRow
  ∷ canonicalAgeBandDriftRow
  ∷ canonicalSiteStratumAssociationRow
  ∷ canonicalScannerDriftRow
  ∷ canonicalConditionFollowUpRow
  ∷ canonicalTreatmentExposureGuardRow
  ∷ canonicalFollowUpResidualRow
  ∷ []

------------------------------------------------------------------------
-- Canonical certificate.

canonicalPopulationLongitudinalBOLDResidualCertificate :
  PopulationLongitudinalBOLDResidualCertificate
canonicalPopulationLongitudinalBOLDResidualCertificate =
  mkPopulationLongitudinalBOLDResidualCertificate
    "population longitudinal BOLD residual certificate"
    candidateOnlyRoute
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
    "Candidate-only certificate: BOLDSignal witnesses neural/vascular proxy variation across population and time; the lane does not promote individual diagnosis, trauma mechanism recovery, hidden chart recovery, causal closure, or mind-reading."

------------------------------------------------------------------------
-- Canonical bridge.

canonicalPopulationLongitudinalBOLDResidualBridge :
  PopulationLongitudinalBOLDResidualBridge
canonicalPopulationLongitudinalBOLDResidualBridge =
  record
    { governance =
        Governance.canonicalFMRIConnectomeProxyGovernance
    ; governanceIsCanonical =
        true
    ; regressionReceipt =
        Regression.canonicalBodyMemoryRegressionReceipt
    ; regressionReceiptIsCanonical =
        true
    ; route =
        candidateOnlyRoute
    ; routeIsCandidateOnly =
        refl
    ; routeAdmissible =
        tt
    ; samplingWindows =
        canonicalSamplingWindows
    ; samplingWindowsAreCanonical =
        refl
    ; cohortStrata =
        canonicalCohortStrata
    ; cohortStrataAreCanonical =
        refl
    ; driftBoundKinds =
        canonicalDriftBoundKinds
    ; driftBoundKindsAreCanonical =
        refl
    ; associationKinds =
        canonicalAssociationKinds
    ; associationKindsAreCanonical =
        refl
    ; rows =
        canonicalPopulationBOLDResidualRows
    ; rowsAreCanonical =
        refl
    ; nonPromotionCertificate =
        canonicalPopulationLongitudinalBOLDResidualCertificate
    ; bridgeReading =
        "Candidate-only population longitudinal BOLD residual bridge: BOLDSignal witnesses neural/vascular proxy variation, and the module only permits bounded drift and cohort association rows while blocking individual diagnosis, trauma mechanism recovery, hidden chart recovery, causal closure, and mind-reading."
    }

canonicalPopulationLongitudinalBOLDResidualBridgeIsCandidateOnly :
  route canonicalPopulationLongitudinalBOLDResidualBridge ≡ candidateOnlyRoute
canonicalPopulationLongitudinalBOLDResidualBridgeIsCandidateOnly =
  routeIsCandidateOnly canonicalPopulationLongitudinalBOLDResidualBridge

canonicalPopulationLongitudinalBOLDResidualBridgeNoDiagnosis :
  rowNoIndividualDiagnosis canonicalPopulationBaselineRow ≡ false
canonicalPopulationLongitudinalBOLDResidualBridgeNoDiagnosis =
  rowNoIndividualDiagnosisIsFalse canonicalPopulationBaselineRow

canonicalPopulationLongitudinalBOLDResidualBridgeNoTraumaMechanism :
  rowNoTraumaMechanism canonicalPopulationBaselineRow ≡ false
canonicalPopulationLongitudinalBOLDResidualBridgeNoTraumaMechanism =
  rowNoTraumaMechanismIsFalse canonicalPopulationBaselineRow

canonicalPopulationLongitudinalBOLDResidualBridgeNoHiddenChartRecovery :
  rowNoHiddenChartRecovery canonicalSiteStratumAssociationRow ≡ false
canonicalPopulationLongitudinalBOLDResidualBridgeNoHiddenChartRecovery =
  rowNoHiddenChartRecoveryIsFalse canonicalSiteStratumAssociationRow

canonicalPopulationLongitudinalBOLDResidualBridgeNoCausalClosure :
  rowNoCausalClosure canonicalScannerDriftRow ≡ false
canonicalPopulationLongitudinalBOLDResidualBridgeNoCausalClosure =
  rowNoCausalClosureIsFalse canonicalScannerDriftRow

canonicalPopulationLongitudinalBOLDResidualBridgeNoMindReading :
  rowNoMindReading canonicalConditionFollowUpRow ≡ false
canonicalPopulationLongitudinalBOLDResidualBridgeNoMindReading =
  rowNoMindReadingIsFalse canonicalConditionFollowUpRow
