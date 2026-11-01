module DASHI.Biology.LongitudinalFMRIConnectomeDynamicsBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

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

data PopulationScope : Set where
  singleCohortScope : PopulationScope
  multiCohortScope : PopulationScope
  populationAggregateScope : PopulationScope
  longitudinalPanelScope : PopulationScope

data CohortKind : Set where
  baselineCohortKind : CohortKind
  followUpCohortKind : CohortKind
  stratifiedCohortKind : CohortKind
  pooledPopulationCohortKind : CohortKind

data NeurovascularProxyKind : Set where
  boldHemodynamicProxyKind : NeurovascularProxyKind
  vascularCouplingProxyKind : NeurovascularProxyKind
  neurovascularLagProxyKind : NeurovascularProxyKind
  populationBOLDProxyKind : NeurovascularProxyKind

data LongitudinalGateKind : Set where
  populationScopeGate : LongitudinalGateKind
  cohortCompositionGate : LongitudinalGateKind
  neurovascularProxyGate : LongitudinalGateKind
  timeSeriesProxyGate : LongitudinalGateKind
  individualMechanismGate : LongitudinalGateKind
  traumaProofGate : LongitudinalGateKind
  hiddenChartRecoveryGate : LongitudinalGateKind
  mindReadingGate : LongitudinalGateKind
  diagnosisGate : LongitudinalGateKind
  treatmentGate : LongitudinalGateKind
  clinicalAuthorityGate : LongitudinalGateKind

canonicalPopulationScopes :
  List PopulationScope
canonicalPopulationScopes =
  singleCohortScope
  ∷ multiCohortScope
  ∷ populationAggregateScope
  ∷ longitudinalPanelScope
  ∷ []

canonicalCohortKinds :
  List CohortKind
canonicalCohortKinds =
  baselineCohortKind
  ∷ followUpCohortKind
  ∷ stratifiedCohortKind
  ∷ pooledPopulationCohortKind
  ∷ []

canonicalNeurovascularProxyKinds :
  List NeurovascularProxyKind
canonicalNeurovascularProxyKinds =
  boldHemodynamicProxyKind
  ∷ vascularCouplingProxyKind
  ∷ neurovascularLagProxyKind
  ∷ populationBOLDProxyKind
  ∷ []

canonicalLongitudinalGateKinds :
  List LongitudinalGateKind
canonicalLongitudinalGateKinds =
  populationScopeGate
  ∷ cohortCompositionGate
  ∷ neurovascularProxyGate
  ∷ timeSeriesProxyGate
  ∷ individualMechanismGate
  ∷ traumaProofGate
  ∷ hiddenChartRecoveryGate
  ∷ mindReadingGate
  ∷ diagnosisGate
  ∷ treatmentGate
  ∷ clinicalAuthorityGate
  ∷ []

populationScopeName :
  PopulationScope →
  String
populationScopeName singleCohortScope =
  "single cohort scope"
populationScopeName multiCohortScope =
  "multi cohort scope"
populationScopeName populationAggregateScope =
  "population aggregate scope"
populationScopeName longitudinalPanelScope =
  "longitudinal panel scope"

cohortKindName :
  CohortKind →
  String
cohortKindName baselineCohortKind =
  "baseline cohort"
cohortKindName followUpCohortKind =
  "follow-up cohort"
cohortKindName stratifiedCohortKind =
  "stratified cohort"
cohortKindName pooledPopulationCohortKind =
  "pooled population cohort"

neurovascularProxyKindName :
  NeurovascularProxyKind →
  String
neurovascularProxyKindName boldHemodynamicProxyKind =
  "BOLD hemodynamic proxy"
neurovascularProxyKindName vascularCouplingProxyKind =
  "vascular coupling proxy"
neurovascularProxyKindName neurovascularLagProxyKind =
  "neurovascular lag proxy"
neurovascularProxyKindName populationBOLDProxyKind =
  "population BOLD proxy"

longitudinalGateKindName :
  LongitudinalGateKind →
  String
longitudinalGateKindName populationScopeGate =
  "population scope gate"
longitudinalGateKindName cohortCompositionGate =
  "cohort composition gate"
longitudinalGateKindName neurovascularProxyGate =
  "neurovascular proxy gate"
longitudinalGateKindName timeSeriesProxyGate =
  "time series proxy gate"
longitudinalGateKindName individualMechanismGate =
  "individual mechanism gate"
longitudinalGateKindName traumaProofGate =
  "trauma proof gate"
longitudinalGateKindName hiddenChartRecoveryGate =
  "hidden chart recovery gate"
longitudinalGateKindName mindReadingGate =
  "mind reading gate"
longitudinalGateKindName diagnosisGate =
  "diagnosis gate"
longitudinalGateKindName treatmentGate =
  "treatment gate"
longitudinalGateKindName clinicalAuthorityGate =
  "clinical authority gate"

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

    rowPopulationScope :
      PopulationScope

    rowCohortKind :
      CohortKind

    rowNeurovascularProxyKind :
      NeurovascularProxyKind

    rowGateKind :
      LongitudinalGateKind

    rowLabel :
      String

    rowSurface :
      String

    rowCandidateOnly :
      Bool

    rowCandidateOnlyIsTrue :
      rowCandidateOnly ≡ true

    rowPopulationAssociation :
      Bool

    rowPopulationAssociationIsTrue :
      rowPopulationAssociation ≡ true

    rowCohortAssociation :
      Bool

    rowCohortAssociationIsTrue :
      rowCohortAssociation ≡ true

    rowNeurovascularProxyAssociation :
      Bool

    rowNeurovascularProxyAssociationIsTrue :
      rowNeurovascularProxyAssociation ≡ true

    rowNoIndividualMechanism :
      Bool

    rowNoIndividualMechanismIsFalse :
      rowNoIndividualMechanism ≡ false

    rowNoTraumaMechanism :
      Bool

    rowNoTraumaMechanismIsFalse :
      rowNoTraumaMechanism ≡ false

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

    trajectoryPopulationScope :
      PopulationScope

    trajectoryCohortKind :
      CohortKind

    trajectoryNeurovascularProxyKind :
      NeurovascularProxyKind

    trajectoryGateKind :
      LongitudinalGateKind

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

    trajectoryPopulationAssociation :
      Bool

    trajectoryPopulationAssociationIsTrue :
      trajectoryPopulationAssociation ≡ true

    trajectoryCohortAssociation :
      Bool

    trajectoryCohortAssociationIsTrue :
      trajectoryCohortAssociation ≡ true

    trajectoryNeurovascularProxyAssociation :
      Bool

    trajectoryNeurovascularProxyAssociationIsTrue :
      trajectoryNeurovascularProxyAssociation ≡ true

    trajectoryNoIndividualMechanism :
      Bool

    trajectoryNoIndividualMechanismIsFalse :
      trajectoryNoIndividualMechanism ≡ false

    trajectoryNoTraumaMechanism :
      Bool

    trajectoryNoTraumaMechanismIsFalse :
      trajectoryNoTraumaMechanism ≡ false

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

    driftPopulationScope :
      PopulationScope

    driftCohortKind :
      CohortKind

    driftNeurovascularProxyKind :
      NeurovascularProxyKind

    driftGateKind :
      LongitudinalGateKind

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

    driftPopulationAssociation :
      Bool

    driftPopulationAssociationIsTrue :
      driftPopulationAssociation ≡ true

    driftCohortAssociation :
      Bool

    driftCohortAssociationIsTrue :
      driftCohortAssociation ≡ true

    driftNeurovascularProxyAssociation :
      Bool

    driftNeurovascularProxyAssociationIsTrue :
      driftNeurovascularProxyAssociation ≡ true

    driftNoIndividualMechanism :
      Bool

    driftNoIndividualMechanismIsFalse :
      driftNoIndividualMechanism ≡ false

    driftNoTraumaMechanism :
      Bool

    driftNoTraumaMechanismIsFalse :
      driftNoTraumaMechanism ≡ false

    driftReading :
      String

record PopulationCohortNeurovascularGate : Set where
  constructor mkPopulationCohortNeurovascularGate
  field
    gateLabel :
      String

    gatePopulationScope :
      PopulationScope

    gateCohortKind :
      CohortKind

    gateNeurovascularProxyKind :
      NeurovascularProxyKind

    gateKind :
      LongitudinalGateKind

    gatePopulationIsAggregate :
      Bool

    gatePopulationIsAggregateIsTrue :
      gatePopulationIsAggregate ≡ true

    gateCohortIsStratifiedOrPooled :
      Bool

    gateCohortIsStratifiedOrPooledIsTrue :
      gateCohortIsStratifiedOrPooled ≡ true

    gateNeurovascularProxyIsBOLD :
      Bool

    gateNeurovascularProxyIsBOLDIsTrue :
      gateNeurovascularProxyIsBOLD ≡ true

    gateNoIndividualMechanism :
      Bool

    gateNoIndividualMechanismIsFalse :
      gateNoIndividualMechanism ≡ false

    gateNoTraumaMechanism :
      Bool

    gateNoTraumaMechanismIsFalse :
      gateNoTraumaMechanism ≡ false

    gateNoTraumaProof :
      Bool

    gateNoTraumaProofIsFalse :
      gateNoTraumaProof ≡ false

    gateNoHiddenChartRecovery :
      Bool

    gateNoHiddenChartRecoveryIsFalse :
      gateNoHiddenChartRecovery ≡ false

    gateNoMindReading :
      Bool

    gateNoMindReadingIsFalse :
      gateNoMindReading ≡ false

    gateNoClinicalAuthority :
      Bool

    gateNoClinicalAuthorityIsFalse :
      gateNoClinicalAuthority ≡ false

    gateReading :
      String

open PopulationCohortNeurovascularGate public

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

    bodyMemoryRegressionReceiptLabel :
      String

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

    populationScopes :
      List PopulationScope

    populationScopesAreCanonical :
      populationScopes ≡ canonicalPopulationScopes

    cohortKinds :
      List CohortKind

    cohortKindsAreCanonical :
      cohortKinds ≡ canonicalCohortKinds

    neurovascularProxyKinds :
      List NeurovascularProxyKind

    neurovascularProxyKindsAreCanonical :
      neurovascularProxyKinds ≡ canonicalNeurovascularProxyKinds

    longitudinalGateKinds :
      List LongitudinalGateKind

    longitudinalGateKindsAreCanonical :
      longitudinalGateKinds ≡ canonicalLongitudinalGateKinds

    populationCohortNeurovascularGate :
      PopulationCohortNeurovascularGate

    populationCohortNeurovascularGateIsCanonical :
      Bool

    populationCohortNeurovascularGateIsCanonicalIsTrue :
      populationCohortNeurovascularGateIsCanonical ≡ true

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
    singleCohortScope
    baselineCohortKind
    boldHemodynamicProxyKind
    populationScopeGate
    "baseline sampling row"
    "Baseline fMRI/BOLD/body-memory placement is treated as a proxy surface."
    true
    refl
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
    multiCohortScope
    stratifiedCohortKind
    vascularCouplingProxyKind
    neurovascularProxyGate
    "lag/alignment/proxy row"
    "BOLD lag is treated as a proxy alignment surface, not as authority."
    true
    refl
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
    longitudinalPanelScope
    followUpCohortKind
    populationBOLDProxyKind
    timeSeriesProxyGate
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
    "Longitudinal scan sessions are treated as proxy trajectories over body-memory residual placement, not as hidden chart recovery or trauma mechanism."

canonicalConnectomeDriftProxy :
  ConnectomeDriftProxy
canonicalConnectomeDriftProxy =
  mkConnectomeDriftProxy
    "connectome drift proxy"
    driftCheckWindow
    longLag
    driftAlignedMode
    connectomeProxyCarrierKind
    populationAggregateScope
    pooledPopulationCohortKind
    neurovascularLagProxyKind
    neurovascularProxyGate
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
    "Connectome drift is tracked as a proxy residual, not as causal closure, trauma mechanism, or clinical authority."

canonicalScanSessionTrajectoryRow :
  LongitudinalBodyMemoryRow
canonicalScanSessionTrajectoryRow =
  mkLongitudinalBodyMemoryRow
    (suc (suc zero))
    midFollowUpWindow
    residualLag
    proxyAlignedMode
    trajectoryProxyCarrierKind
    longitudinalPanelScope
    followUpCohortKind
    populationBOLDProxyKind
    timeSeriesProxyGate
    "scan-session trajectory row"
    "The scan-session trajectory is a candidate-only longitudinal proxy surface."
    true
    refl
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
    populationAggregateScope
    pooledPopulationCohortKind
    neurovascularLagProxyKind
    neurovascularProxyGate
    "connectome drift proxy row"
    "Connectome drift is retained as a proxy residual, not a closure claim."
    true
    refl
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
    populationAggregateScope
    stratifiedCohortKind
    populationBOLDProxyKind
    clinicalAuthorityGate
    "governance boundary row"
    "Governance stays candidate-only while routing proxy surfaces through a fail-closed boundary."
    true
    refl
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

canonicalLongitudinalPopulationScopes :
  List PopulationScope
canonicalLongitudinalPopulationScopes =
  canonicalPopulationScopes

canonicalLongitudinalCohortKinds :
  List CohortKind
canonicalLongitudinalCohortKinds =
  canonicalCohortKinds

canonicalLongitudinalNeurovascularProxyKinds :
  List NeurovascularProxyKind
canonicalLongitudinalNeurovascularProxyKinds =
  canonicalNeurovascularProxyKinds

canonicalPopulationCohortNeurovascularGate :
  PopulationCohortNeurovascularGate
canonicalPopulationCohortNeurovascularGate =
  mkPopulationCohortNeurovascularGate
    "population-cohort-neurovascular-gate"
    populationAggregateScope
    pooledPopulationCohortKind
    populationBOLDProxyKind
    neurovascularProxyGate
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
    false
    refl
    false
    refl
    "Population and cohort structure are routed through a neurovascular proxy gate; the surface is longitudinal association over cohort time, not individual mechanism, trauma proof, hidden chart recovery, trauma mechanism, mind-reading, or clinical authority."

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
    ; bodyMemoryRegressionReceiptLabel =
        "body-memory biology regression receipt"
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
    ; populationScopes =
        canonicalLongitudinalPopulationScopes
    ; populationScopesAreCanonical =
        refl
    ; cohortKinds =
        canonicalLongitudinalCohortKinds
    ; cohortKindsAreCanonical =
        refl
    ; neurovascularProxyKinds =
        canonicalLongitudinalNeurovascularProxyKinds
    ; neurovascularProxyKindsAreCanonical =
        refl
    ; longitudinalGateKinds =
        canonicalLongitudinalGateKinds
    ; longitudinalGateKindsAreCanonical =
        refl
    ; populationCohortNeurovascularGate =
        canonicalPopulationCohortNeurovascularGate
    ; populationCohortNeurovascularGateIsCanonical =
        true
    ; populationCohortNeurovascularGateIsCanonicalIsTrue =
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
        "Candidate-only longitudinal fMRI/BOLD/connectome bridge: the temporal windows, lag/alignment/proxy rows, population/cohort gates, scan-session trajectory, and connectome drift proxy remain bounded association surfaces only, while reverse inference, hidden chart recovery, trauma mechanism recovery, mind-reading, diagnosis, treatment, causal closure, and individual mechanism promotion stay blocked."
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

canonicalLongitudinalPopulationScopesAreCanonical :
  canonicalLongitudinalPopulationScopes ≡ canonicalPopulationScopes
canonicalLongitudinalPopulationScopesAreCanonical =
  refl

canonicalLongitudinalCohortKindsAreCanonical :
  canonicalLongitudinalCohortKinds ≡ canonicalCohortKinds
canonicalLongitudinalCohortKindsAreCanonical =
  refl

canonicalLongitudinalNeurovascularProxyKindsAreCanonical :
  canonicalLongitudinalNeurovascularProxyKinds ≡ canonicalNeurovascularProxyKinds
canonicalLongitudinalNeurovascularProxyKindsAreCanonical =
  refl

canonicalLongitudinalGateKindsAreCanonical :
  canonicalLongitudinalGateKinds ≡ canonicalLongitudinalGateKinds
canonicalLongitudinalGateKindsAreCanonical =
  refl

canonicalPopulationCohortNeurovascularGateIsCanonical :
  populationCohortNeurovascularGateIsCanonical
    canonicalLongitudinalFMRIConnectomeDynamicsGovernance
  ≡
  true
canonicalPopulationCohortNeurovascularGateIsCanonical =
  refl

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoReverseInference :
  rowNoReverseInference canonicalBaselineWindowRow ≡ false
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoReverseInference =
  rowNoReverseInferenceIsFalse canonicalBaselineWindowRow

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoTraumaMechanism :
  rowNoTraumaMechanism canonicalBaselineWindowRow ≡ false
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoTraumaMechanism =
  rowNoTraumaMechanismIsFalse canonicalBaselineWindowRow

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoHiddenChartRecovery :
  rowNoHiddenChartRecovery canonicalConnectomeDriftProxyRow ≡ false
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceNoHiddenChartRecovery =
  rowNoHiddenChartRecoveryIsFalse canonicalConnectomeDriftProxyRow

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceTrajectoryNoTraumaMechanism :
  trajectoryNoTraumaMechanism canonicalScanSessionTrajectory ≡ false
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceTrajectoryNoTraumaMechanism =
  trajectoryNoTraumaMechanismIsFalse canonicalScanSessionTrajectory

canonicalLongitudinalFMRIConnectomeDynamicsGovernanceDriftNoTraumaMechanism :
  driftNoTraumaMechanism canonicalConnectomeDriftProxy ≡ false
canonicalLongitudinalFMRIConnectomeDynamicsGovernanceDriftNoTraumaMechanism =
  driftNoTraumaMechanismIsFalse canonicalConnectomeDriftProxy

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

canonicalPopulationCohortNeurovascularGateNoTraumaMechanism :
  gateNoTraumaMechanism canonicalPopulationCohortNeurovascularGate ≡ false
canonicalPopulationCohortNeurovascularGateNoTraumaMechanism =
  gateNoTraumaMechanismIsFalse canonicalPopulationCohortNeurovascularGate
