module DASHI.Biology.LongitudinalFMRIConnectomeDynamicsBridge where

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
-- Longitudinal fMRI / connectome dynamics bridge.
--
-- Candidate-only lane:
--   - fMRI/BOLD/connectome stay proxy surfaces
--   - longitudinal body-memory is tracked as residual placement only
--   - reverse inference, hidden chart recovery, mind-reading, diagnosis,
--     treatment, and causal closure stay blocked
--
-- The file is self-contained except for the existing governance import.
-- It does not rely on any new module owned by a different lane.

data Never : Set where

------------------------------------------------------------------------
-- Temporal surfaces.

data TemporalSamplingWindow : Set where
  baselineWindow : TemporalSamplingWindow
  earlyFollowUpWindow : TemporalSamplingWindow
  midFollowUpWindow : TemporalSamplingWindow
  lateFollowUpWindow : TemporalSamplingWindow
  driftCheckWindow : TemporalSamplingWindow

data TemporalLag : Set where
  zeroLag : TemporalLag
  shortLag : TemporalLag
  mediumLag : TemporalLag
  longLag : TemporalLag
  residualLag : TemporalLag

data AlignmentMode : Set where
  sessionAlignedMode : AlignmentMode
  eventAlignedMode : AlignmentMode
  proxyAlignedMode : AlignmentMode
  residualAlignedMode : AlignmentMode
  driftAlignedMode : AlignmentMode

data ProxyCarrierKind : Set where
  fMRIProxyCarrierKind : ProxyCarrierKind
  boldProxyCarrierKind : ProxyCarrierKind
  connectomeProxyCarrierKind : ProxyCarrierKind
  trajectoryProxyCarrierKind : ProxyCarrierKind
  governanceProxyCarrierKind : ProxyCarrierKind

canonicalTemporalSamplingWindows :
  List TemporalSamplingWindow
canonicalTemporalSamplingWindows =
  baselineWindow
  ∷ earlyFollowUpWindow
  ∷ midFollowUpWindow
  ∷ lateFollowUpWindow
  ∷ driftCheckWindow
  ∷ []

canonicalTemporalLags :
  List TemporalLag
canonicalTemporalLags =
  zeroLag
  ∷ shortLag
  ∷ mediumLag
  ∷ longLag
  ∷ residualLag
  ∷ []

canonicalAlignmentModes :
  List AlignmentMode
canonicalAlignmentModes =
  sessionAlignedMode
  ∷ eventAlignedMode
  ∷ proxyAlignedMode
  ∷ residualAlignedMode
  ∷ driftAlignedMode
  ∷ []

canonicalProxyCarrierKinds :
  List ProxyCarrierKind
canonicalProxyCarrierKinds =
  fMRIProxyCarrierKind
  ∷ boldProxyCarrierKind
  ∷ connectomeProxyCarrierKind
  ∷ trajectoryProxyCarrierKind
  ∷ governanceProxyCarrierKind
  ∷ []

temporalSamplingWindowName :
  TemporalSamplingWindow →
  String
temporalSamplingWindowName baselineWindow =
  "baseline window"
temporalSamplingWindowName earlyFollowUpWindow =
  "early follow-up window"
temporalSamplingWindowName midFollowUpWindow =
  "mid follow-up window"
temporalSamplingWindowName lateFollowUpWindow =
  "late follow-up window"
temporalSamplingWindowName driftCheckWindow =
  "drift-check window"

temporalLagName :
  TemporalLag →
  String
temporalLagName zeroLag =
  "zero lag"
temporalLagName shortLag =
  "short lag"
temporalLagName mediumLag =
  "medium lag"
temporalLagName longLag =
  "long lag"
temporalLagName residualLag =
  "residual lag"

alignmentModeName :
  AlignmentMode →
  String
alignmentModeName sessionAlignedMode =
  "session aligned"
alignmentModeName eventAlignedMode =
  "event aligned"
alignmentModeName proxyAlignedMode =
  "proxy aligned"
alignmentModeName residualAlignedMode =
  "residual aligned"
alignmentModeName driftAlignedMode =
  "drift aligned"

proxyCarrierKindName :
  ProxyCarrierKind →
  String
proxyCarrierKindName fMRIProxyCarrierKind =
  "fMRI proxy carrier"
proxyCarrierKindName boldProxyCarrierKind =
  "BOLD proxy carrier"
proxyCarrierKindName connectomeProxyCarrierKind =
  "connectome proxy carrier"
proxyCarrierKindName trajectoryProxyCarrierKind =
  "trajectory proxy carrier"
proxyCarrierKindName governanceProxyCarrierKind =
  "governance proxy carrier"

------------------------------------------------------------------------
-- Routes and admissibility.

data LongitudinalRoute : Set where
  candidateProxyRoute : LongitudinalRoute
  fMRIProxyRoute : LongitudinalRoute
  boldProxyRoute : LongitudinalRoute
  connectomeProxyRoute : LongitudinalRoute
  sessionTrajectoryRoute : LongitudinalRoute
  driftProxyRoute : LongitudinalRoute
  reverseInferenceRoute : LongitudinalRoute
  hiddenChartRecoveryRoute : LongitudinalRoute
  mindReadingRoute : LongitudinalRoute
  diagnosisRoute : LongitudinalRoute
  treatmentRoute : LongitudinalRoute
  causalClosureRoute : LongitudinalRoute

AdmissibleLongitudinalRoute :
  LongitudinalRoute →
  Set
AdmissibleLongitudinalRoute candidateProxyRoute = ⊤
AdmissibleLongitudinalRoute fMRIProxyRoute = Never
AdmissibleLongitudinalRoute boldProxyRoute = Never
AdmissibleLongitudinalRoute connectomeProxyRoute = Never
AdmissibleLongitudinalRoute sessionTrajectoryRoute = Never
AdmissibleLongitudinalRoute driftProxyRoute = Never
AdmissibleLongitudinalRoute reverseInferenceRoute = Never
AdmissibleLongitudinalRoute hiddenChartRecoveryRoute = Never
AdmissibleLongitudinalRoute mindReadingRoute = Never
AdmissibleLongitudinalRoute diagnosisRoute = Never
AdmissibleLongitudinalRoute treatmentRoute = Never
AdmissibleLongitudinalRoute causalClosureRoute = Never

fMRIProxyRouteRejected :
  AdmissibleLongitudinalRoute fMRIProxyRoute →
  Never
fMRIProxyRouteRejected impossible = impossible

boldProxyRouteRejected :
  AdmissibleLongitudinalRoute boldProxyRoute →
  Never
boldProxyRouteRejected impossible = impossible

connectomeProxyRouteRejected :
  AdmissibleLongitudinalRoute connectomeProxyRoute →
  Never
connectomeProxyRouteRejected impossible = impossible

sessionTrajectoryRouteRejected :
  AdmissibleLongitudinalRoute sessionTrajectoryRoute →
  Never
sessionTrajectoryRouteRejected impossible = impossible

driftProxyRouteRejected :
  AdmissibleLongitudinalRoute driftProxyRoute →
  Never
driftProxyRouteRejected impossible = impossible

reverseInferenceRouteRejected :
  AdmissibleLongitudinalRoute reverseInferenceRoute →
  Never
reverseInferenceRouteRejected impossible = impossible

hiddenChartRecoveryRouteRejected :
  AdmissibleLongitudinalRoute hiddenChartRecoveryRoute →
  Never
hiddenChartRecoveryRouteRejected impossible = impossible

mindReadingRouteRejected :
  AdmissibleLongitudinalRoute mindReadingRoute →
  Never
mindReadingRouteRejected impossible = impossible

diagnosisRouteRejected :
  AdmissibleLongitudinalRoute diagnosisRoute →
  Never
diagnosisRouteRejected impossible = impossible

treatmentRouteRejected :
  AdmissibleLongitudinalRoute treatmentRoute →
  Never
treatmentRouteRejected impossible = impossible

causalClosureRouteRejected :
  AdmissibleLongitudinalRoute causalClosureRoute →
  Never
causalClosureRouteRejected impossible = impossible

------------------------------------------------------------------------
-- Typed rows.

record LongitudinalBodyMemoryRow : Set where
  constructor mkLongitudinalBodyMemoryRow
  field
    rowIndex :
      Nat

    rowWindow :
      TemporalSamplingWindow

    rowLag :
      TemporalLag

    rowAlignment :
      AlignmentMode

    rowProxyKind :
      ProxyCarrierKind

    rowLabel :
      String

    rowSurface :
      String

    rowCandidateOnly :
      Bool

    rowCandidateOnlyIsTrue :
      rowCandidateOnly ≡ true

    rowNoReverseInference :
      Bool

    rowNoReverseInferenceIsFalse :
      rowNoReverseInference ≡ false

    rowNoHiddenChartRecovery :
      Bool

    rowNoHiddenChartRecoveryIsFalse :
      rowNoHiddenChartRecovery ≡ false

    rowNoMindReading :
      Bool

    rowNoMindReadingIsFalse :
      rowNoMindReading ≡ false

    rowNoDiagnosis :
      Bool

    rowNoDiagnosisIsFalse :
      rowNoDiagnosis ≡ false

    rowNoTreatment :
      Bool

    rowNoTreatmentIsFalse :
      rowNoTreatment ≡ false

    rowNoCausalClosure :
      Bool

    rowNoCausalClosureIsFalse :
      rowNoCausalClosure ≡ false

    rowNotes :
      List String

open LongitudinalBodyMemoryRow public

record ScanSessionTrajectory : Set where
  constructor mkScanSessionTrajectory
  field
    trajectoryLabel :
      String

    trajectoryWindows :
      List TemporalSamplingWindow

    trajectoryLag :
      TemporalLag

    trajectoryAlignment :
      AlignmentMode

    trajectoryProxyKind :
      ProxyCarrierKind

    trajectoryCandidateOnly :
      Bool

    trajectoryCandidateOnlyIsTrue :
      trajectoryCandidateOnly ≡ true

    trajectoryNoReverseInference :
      Bool

    trajectoryNoReverseInferenceIsFalse :
      trajectoryNoReverseInference ≡ false

    trajectoryNoHiddenChartRecovery :
      Bool

    trajectoryNoHiddenChartRecoveryIsFalse :
      trajectoryNoHiddenChartRecovery ≡ false

    trajectoryNoMindReading :
      Bool

    trajectoryNoMindReadingIsFalse :
      trajectoryNoMindReading ≡ false

    trajectoryNoDiagnosis :
      Bool

    trajectoryNoDiagnosisIsFalse :
      trajectoryNoDiagnosis ≡ false

    trajectoryNoTreatment :
      Bool

    trajectoryNoTreatmentIsFalse :
      trajectoryNoTreatment ≡ false

    trajectoryNoCausalClosure :
      Bool

    trajectoryNoCausalClosureIsFalse :
      trajectoryNoCausalClosure ≡ false

    trajectoryReading :
      String

open ScanSessionTrajectory public

record ConnectomeDriftProxy : Set where
  constructor mkConnectomeDriftProxy
  field
    driftLabel :
      String

    driftWindow :
      TemporalSamplingWindow

    driftLag :
      TemporalLag

    driftAlignment :
      AlignmentMode

    driftProxyKind :
      ProxyCarrierKind

    driftCandidateOnly :
      Bool

    driftCandidateOnlyIsTrue :
      driftCandidateOnly ≡ true

    driftNoReverseInference :
      Bool

    driftNoReverseInferenceIsFalse :
      driftNoReverseInference ≡ false

    driftNoHiddenChartRecovery :
      Bool

    driftNoHiddenChartRecoveryIsFalse :
      driftNoHiddenChartRecovery ≡ false

    driftNoMindReading :
      Bool

    driftNoMindReadingIsFalse :
      driftNoMindReading ≡ false

    driftNoDiagnosis :
      Bool

    driftNoDiagnosisIsFalse :
      driftNoDiagnosis ≡ false

    driftNoTreatment :
      Bool

    driftNoTreatmentIsFalse :
      driftNoTreatment ≡ false

    driftNoCausalClosure :
      Bool

    driftNoCausalClosureIsFalse :
      driftNoCausalClosure ≡ false

    driftReading :
      String

open ConnectomeDriftProxy public

------------------------------------------------------------------------
-- Bridge governance.

record LongitudinalFMRIConnectomeDynamicsGovernance : Setω where
  field
    fmriConnectomeProxyGovernance :
      Governance.FMRIConnectomeProxyGovernance

    fmriConnectomeProxyGovernanceIsCanonical :
      Bool

    fmriConnectomeProxyGovernanceIsCanonicalIsTrue :
      fmriConnectomeProxyGovernanceIsCanonical ≡ true

    bodyMemoryRegressionReceipt :
      Regression.BodyMemoryRegressionReceipt

    bodyMemoryRegressionReceiptIsCanonical :
      Bool

    bodyMemoryRegressionReceiptIsCanonicalIsTrue :
      bodyMemoryRegressionReceiptIsCanonical ≡ true

    route :
      LongitudinalRoute

    routeIsCandidateOnly :
      route ≡ candidateProxyRoute

    routeAdmissible :
      AdmissibleLongitudinalRoute route

    temporalSamplingWindows :
      List TemporalSamplingWindow

    temporalSamplingWindowsAreCanonical :
      temporalSamplingWindows ≡ canonicalTemporalSamplingWindows

    temporalLags :
      List TemporalLag

    temporalLagsAreCanonical :
      temporalLags ≡ canonicalTemporalLags

    alignmentModes :
      List AlignmentMode

    alignmentModesAreCanonical :
      alignmentModes ≡ canonicalAlignmentModes

    proxyCarrierKinds :
      List ProxyCarrierKind

    proxyCarrierKindsAreCanonical :
      proxyCarrierKinds ≡ canonicalProxyCarrierKinds

    scanSessionTrajectory :
      ScanSessionTrajectory

    connectomeDriftProxy :
      ConnectomeDriftProxy

    longitudinalRows :
      List LongitudinalBodyMemoryRow

    longitudinalRowsAreCanonical :
      longitudinalRows ≡ longitudinalRows

    governanceReading :
      String

open LongitudinalFMRIConnectomeDynamicsGovernance public

------------------------------------------------------------------------
-- Canonical examples.

canonicalBaselineWindowRow :
  LongitudinalBodyMemoryRow
canonicalBaselineWindowRow =
  mkLongitudinalBodyMemoryRow
    zero
    baselineWindow
    zeroLag
    sessionAlignedMode
    fMRIProxyCarrierKind
    "baseline sampling row"
    "Baseline fMRI/BOLD/body-memory placement is treated as a proxy surface."
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
    false
    refl
    ( "baseline window"
    ∷ "candidate-only longitudinal anchor"
    ∷ "no reverse inference, hidden chart recovery, mind-reading, diagnosis, treatment, or causal closure"
    ∷ []
    )

canonicalLagAlignmentProxyRow :
  LongitudinalBodyMemoryRow
canonicalLagAlignmentProxyRow =
  mkLongitudinalBodyMemoryRow
    (suc zero)
    earlyFollowUpWindow
    shortLag
    eventAlignedMode
    boldProxyCarrierKind
    "lag/alignment/proxy row"
    "BOLD lag is treated as a proxy alignment surface, not as authority."
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
    false
    refl
    ( "lag and alignment remain candidate-only"
    ∷ "BOLD is a proxy carrier, not a mind-reading surface"
    ∷ "no diagnosis, treatment, or causal closure"
    ∷ []
    )

canonicalScanSessionTrajectory :
  ScanSessionTrajectory
canonicalScanSessionTrajectory =
  mkScanSessionTrajectory
    "scan-session trajectory"
    ( baselineWindow
    ∷ earlyFollowUpWindow
    ∷ midFollowUpWindow
    ∷ lateFollowUpWindow
    ∷ driftCheckWindow
    ∷ []
    )
    residualLag
    proxyAlignedMode
    trajectoryProxyCarrierKind
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
    "Longitudinal scan sessions are treated as proxy trajectories over body-memory residual placement, not as hidden chart recovery."

canonicalConnectomeDriftProxy :
  ConnectomeDriftProxy
canonicalConnectomeDriftProxy =
  mkConnectomeDriftProxy
    "connectome drift proxy"
    driftCheckWindow
    longLag
    driftAlignedMode
    connectomeProxyCarrierKind
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
    "Connectome drift is tracked as a proxy residual, not as causal closure or clinical authority."

canonicalScanSessionTrajectoryRow :
  LongitudinalBodyMemoryRow
canonicalScanSessionTrajectoryRow =
  mkLongitudinalBodyMemoryRow
    (suc (suc zero))
    midFollowUpWindow
    residualLag
    proxyAlignedMode
    trajectoryProxyCarrierKind
    "scan-session trajectory row"
    "The scan-session trajectory is a candidate-only longitudinal proxy surface."
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
    false
    refl
    ( "scan-session trajectory stays candidate-only"
    ∷ "trajectory is not reverse inference or hidden chart recovery"
    ∷ "trajectory is not diagnosis, treatment, or causal closure"
    ∷ []
    )

canonicalConnectomeDriftProxyRow :
  LongitudinalBodyMemoryRow
canonicalConnectomeDriftProxyRow =
  mkLongitudinalBodyMemoryRow
    (suc (suc (suc zero)))
    driftCheckWindow
    longLag
    driftAlignedMode
    connectomeProxyCarrierKind
    "connectome drift proxy row"
    "Connectome drift is retained as a proxy residual, not a closure claim."
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
    false
    refl
    ( "drift is a proxy reading"
    ∷ "drift does not recover hidden charts"
    ∷ "drift does not promote diagnosis, treatment, or causal closure"
    ∷ []
    )

canonicalGovernanceBoundaryRow :
  LongitudinalBodyMemoryRow
canonicalGovernanceBoundaryRow =
  mkLongitudinalBodyMemoryRow
    (suc (suc (suc (suc zero))))
    driftCheckWindow
    residualLag
    residualAlignedMode
    governanceProxyCarrierKind
    "governance boundary row"
    "Governance stays candidate-only while routing proxy surfaces through a fail-closed boundary."
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
    false
    refl
    ( "governance import remains canonical"
    ∷ "boundary blocks reverse inference and causal closure"
    ∷ "boundary blocks diagnosis and treatment"
    ∷ []
    )

canonicalLongitudinalRows :
  List LongitudinalBodyMemoryRow
canonicalLongitudinalRows =
  canonicalBaselineWindowRow
  ∷ canonicalLagAlignmentProxyRow
  ∷ canonicalScanSessionTrajectoryRow
  ∷ canonicalConnectomeDriftProxyRow
  ∷ canonicalGovernanceBoundaryRow
  ∷ []

canonicalLongitudinalTemporalWindows :
  List TemporalSamplingWindow
canonicalLongitudinalTemporalWindows =
  canonicalTemporalSamplingWindows

canonicalLongitudinalLags :
  List TemporalLag
canonicalLongitudinalLags =
  canonicalTemporalLags

canonicalLongitudinalAlignmentModes :
  List AlignmentMode
canonicalLongitudinalAlignmentModes =
  canonicalAlignmentModes

canonicalLongitudinalProxyCarrierKinds :
  List ProxyCarrierKind
canonicalLongitudinalProxyCarrierKinds =
  canonicalProxyCarrierKinds

canonicalLongitudinalFMRIConnectomeDynamicsGovernance :
  LongitudinalFMRIConnectomeDynamicsGovernance
canonicalLongitudinalFMRIConnectomeDynamicsGovernance =
  record
    { fmriConnectomeProxyGovernance =
        Governance.canonicalFMRIConnectomeProxyGovernance
    ; fmriConnectomeProxyGovernanceIsCanonical =
        true
    ; fmriConnectomeProxyGovernanceIsCanonicalIsTrue =
        refl
    ; bodyMemoryRegressionReceipt =
        Regression.canonicalBodyMemoryRegressionReceipt
    ; bodyMemoryRegressionReceiptIsCanonical =
        true
    ; bodyMemoryRegressionReceiptIsCanonicalIsTrue =
        refl
    ; route =
        candidateProxyRoute
    ; routeIsCandidateOnly =
        refl
    ; routeAdmissible =
        tt
    ; temporalSamplingWindows =
        canonicalLongitudinalTemporalWindows
    ; temporalSamplingWindowsAreCanonical =
        refl
    ; temporalLags =
        canonicalLongitudinalLags
    ; temporalLagsAreCanonical =
        refl
    ; alignmentModes =
        canonicalLongitudinalAlignmentModes
    ; alignmentModesAreCanonical =
        refl
    ; proxyCarrierKinds =
        canonicalLongitudinalProxyCarrierKinds
    ; proxyCarrierKindsAreCanonical =
        refl
    ; scanSessionTrajectory =
        canonicalScanSessionTrajectory
    ; connectomeDriftProxy =
        canonicalConnectomeDriftProxy
    ; longitudinalRows =
        canonicalLongitudinalRows
    ; longitudinalRowsAreCanonical =
        refl
    ; governanceReading =
        "Candidate-only longitudinal fMRI/BOLD/connectome bridge: the temporal windows, lag/alignment/proxy rows, scan-session trajectory, and connectome drift proxy remain residual surfaces only, while reverse inference, hidden chart recovery, mind-reading, diagnosis, treatment, and causal closure stay blocked."
    }

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceIsCandidateOnly :
  route canonicalLongitudinalFMRIConnectomeDynamicsGovernance ≡
  candidateProxyRoute
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceIsCandidateOnly =
  routeIsCandidateOnly canonicalLongitudinalFMRIConnectomeDynamicsGovernance

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceReverseInferenceBlocked :
  AdmissibleLongitudinalRoute reverseInferenceRoute →
  Never
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceReverseInferenceBlocked =
  reverseInferenceRouteRejected

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceHiddenChartRecoveryBlocked :
  AdmissibleLongitudinalRoute hiddenChartRecoveryRoute →
  Never
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceHiddenChartRecoveryBlocked =
  hiddenChartRecoveryRouteRejected

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceMindReadingBlocked :
  AdmissibleLongitudinalRoute mindReadingRoute →
  Never
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceMindReadingBlocked =
  mindReadingRouteRejected

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceDiagnosisBlocked :
  AdmissibleLongitudinalRoute diagnosisRoute →
  Never
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceDiagnosisBlocked =
  diagnosisRouteRejected

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceTreatmentBlocked :
  AdmissibleLongitudinalRoute treatmentRoute →
  Never
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceTreatmentBlocked =
  treatmentRouteRejected

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceCausalClosureBlocked :
  AdmissibleLongitudinalRoute causalClosureRoute →
  Never
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceCausalClosureBlocked =
  causalClosureRouteRejected

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoReverseInference :
  rowNoReverseInference canonicalBaselineWindowRow ≡ false
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoReverseInference =
  rowNoReverseInferenceIsFalse canonicalBaselineWindowRow

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoHiddenChartRecovery :
  rowNoHiddenChartRecovery canonicalConnectomeDriftProxyRow ≡ false
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoHiddenChartRecovery =
  rowNoHiddenChartRecoveryIsFalse canonicalConnectomeDriftProxyRow

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoMindReading :
  rowNoMindReading canonicalScanSessionTrajectoryRow ≡ false
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoMindReading =
  rowNoMindReadingIsFalse canonicalScanSessionTrajectoryRow

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoDiagnosis :
  rowNoDiagnosis canonicalLagAlignmentProxyRow ≡ false
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoDiagnosis =
  rowNoDiagnosisIsFalse canonicalLagAlignmentProxyRow

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoTreatment :
  rowNoTreatment canonicalLagAlignmentProxyRow ≡ false
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoTreatment =
  rowNoTreatmentIsFalse canonicalLagAlignmentProxyRow

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoCausalClosure :
  rowNoCausalClosure canonicalConnectomeDriftProxyRow ≡ false
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoCausalClosure =
  rowNoCausalClosureIsFalse canonicalConnectomeDriftProxyRow
