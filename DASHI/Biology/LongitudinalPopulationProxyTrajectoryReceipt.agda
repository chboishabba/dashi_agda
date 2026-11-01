module DASHI.Biology.LongitudinalPopulationProxyTrajectoryReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.BodyMemoryBiologyRegression as Regression
import DASHI.Biology.FMRIConnectomeProxyGovernance as Governance
import DASHI.Biology.LongitudinalFMRIConnectomeDynamicsBridge as Longitudinal
import DASHI.Biology.PopulationLongitudinalBOLDResidualBridge as Population

------------------------------------------------------------------------
-- Longitudinal population proxy trajectory receipt.
--
-- Candidate-only surface:
--   - population longitudinal BOLD / connectome / fMRI trajectories can
--     constrain trajectory models only relative to axis bundle, confound
--     model, longitudinal design, and multimodal witnesses;
--   - trajectory candidate is not causal mechanism;
--   - no diagnosis, no mind reading, no trauma mechanism proof,
--     no treatment, no hidden chart recovery, no clinical authority.
------------------------------------------------------------------------

data Never : Set where

data PopulationTrajectoryRoute : Set where
  candidateOnlyRoute : PopulationTrajectoryRoute
  populationBOLDTrajectoryRoute : PopulationTrajectoryRoute
  connectomeTrajectoryRoute : PopulationTrajectoryRoute
  fMRITrajectoryRoute : PopulationTrajectoryRoute
  axisBundleConstraintRoute : PopulationTrajectoryRoute
  confoundModelConstraintRoute : PopulationTrajectoryRoute
  longitudinalDesignRoute : PopulationTrajectoryRoute
  multimodalWitnessRoute : PopulationTrajectoryRoute
  causalMechanismRoute : PopulationTrajectoryRoute
  individualDiagnosisRoute : PopulationTrajectoryRoute
  mindReadingRoute : PopulationTrajectoryRoute
  traumaMechanismProofRoute : PopulationTrajectoryRoute
  treatmentRoute : PopulationTrajectoryRoute
  hiddenChartRecoveryRoute : PopulationTrajectoryRoute
  clinicalAuthorityRoute : PopulationTrajectoryRoute

AdmissiblePopulationTrajectoryRoute :
  PopulationTrajectoryRoute →
  Set
AdmissiblePopulationTrajectoryRoute candidateOnlyRoute = ⊤
AdmissiblePopulationTrajectoryRoute populationBOLDTrajectoryRoute = Never
AdmissiblePopulationTrajectoryRoute connectomeTrajectoryRoute = Never
AdmissiblePopulationTrajectoryRoute fMRITrajectoryRoute = Never
AdmissiblePopulationTrajectoryRoute axisBundleConstraintRoute = Never
AdmissiblePopulationTrajectoryRoute confoundModelConstraintRoute = Never
AdmissiblePopulationTrajectoryRoute longitudinalDesignRoute = Never
AdmissiblePopulationTrajectoryRoute multimodalWitnessRoute = Never
AdmissiblePopulationTrajectoryRoute causalMechanismRoute = Never
AdmissiblePopulationTrajectoryRoute individualDiagnosisRoute = Never
AdmissiblePopulationTrajectoryRoute mindReadingRoute = Never
AdmissiblePopulationTrajectoryRoute traumaMechanismProofRoute = Never
AdmissiblePopulationTrajectoryRoute treatmentRoute = Never
AdmissiblePopulationTrajectoryRoute hiddenChartRecoveryRoute = Never
AdmissiblePopulationTrajectoryRoute clinicalAuthorityRoute = Never

populationBOLDTrajectoryRouteRejected :
  AdmissiblePopulationTrajectoryRoute populationBOLDTrajectoryRoute →
  Never
populationBOLDTrajectoryRouteRejected impossible = impossible

connectomeTrajectoryRouteRejected :
  AdmissiblePopulationTrajectoryRoute connectomeTrajectoryRoute →
  Never
connectomeTrajectoryRouteRejected impossible = impossible

fMRITrajectoryRouteRejected :
  AdmissiblePopulationTrajectoryRoute fMRITrajectoryRoute →
  Never
fMRITrajectoryRouteRejected impossible = impossible

axisBundleConstraintRouteRejected :
  AdmissiblePopulationTrajectoryRoute axisBundleConstraintRoute →
  Never
axisBundleConstraintRouteRejected impossible = impossible

confoundModelConstraintRouteRejected :
  AdmissiblePopulationTrajectoryRoute confoundModelConstraintRoute →
  Never
confoundModelConstraintRouteRejected impossible = impossible

longitudinalDesignRouteRejected :
  AdmissiblePopulationTrajectoryRoute longitudinalDesignRoute →
  Never
longitudinalDesignRouteRejected impossible = impossible

multimodalWitnessRouteRejected :
  AdmissiblePopulationTrajectoryRoute multimodalWitnessRoute →
  Never
multimodalWitnessRouteRejected impossible = impossible

causalMechanismRouteRejected :
  AdmissiblePopulationTrajectoryRoute causalMechanismRoute →
  Never
causalMechanismRouteRejected impossible = impossible

individualDiagnosisRouteRejected :
  AdmissiblePopulationTrajectoryRoute individualDiagnosisRoute →
  Never
individualDiagnosisRouteRejected impossible = impossible

mindReadingRouteRejected :
  AdmissiblePopulationTrajectoryRoute mindReadingRoute →
  Never
mindReadingRouteRejected impossible = impossible

traumaMechanismProofRouteRejected :
  AdmissiblePopulationTrajectoryRoute traumaMechanismProofRoute →
  Never
traumaMechanismProofRouteRejected impossible = impossible

treatmentRouteRejected :
  AdmissiblePopulationTrajectoryRoute treatmentRoute →
  Never
treatmentRouteRejected impossible = impossible

hiddenChartRecoveryRouteRejected :
  AdmissiblePopulationTrajectoryRoute hiddenChartRecoveryRoute →
  Never
hiddenChartRecoveryRouteRejected impossible = impossible

clinicalAuthorityRouteRejected :
  AdmissiblePopulationTrajectoryRoute clinicalAuthorityRoute →
  Never
clinicalAuthorityRouteRejected impossible = impossible

data TrajectoryAxisBundle : Set where
  populationAxisBundle : TrajectoryAxisBundle
  cohortAxisBundle : TrajectoryAxisBundle
  scannerAxisBundle : TrajectoryAxisBundle
  siteAxisBundle : TrajectoryAxisBundle
  conditionAxisBundle : TrajectoryAxisBundle
  treatmentExposureAxisBundle : TrajectoryAxisBundle
  longitudinalFollowUpAxisBundle : TrajectoryAxisBundle

data TrajectoryConfoundModel : Set where
  ageBandConfoundModel : TrajectoryConfoundModel
  siteConfoundModel : TrajectoryConfoundModel
  scannerConfoundModel : TrajectoryConfoundModel
  conditionConfoundModel : TrajectoryConfoundModel
  treatmentExposureConfoundModel : TrajectoryConfoundModel
  boundedDriftConfoundModel : TrajectoryConfoundModel

data LongitudinalDesignKind : Set where
  baselineFollowUpDesign : LongitudinalDesignKind
  panelTrajectoryDesign : LongitudinalDesignKind
  boundedDriftDesign : LongitudinalDesignKind
  populationAggregationDesign : LongitudinalDesignKind
  proxyCarryForwardDesign : LongitudinalDesignKind

data MultimodalWitnessKind : Set where
  boldWitnessKind : MultimodalWitnessKind
  connectomeWitnessKind : MultimodalWitnessKind
  fMRIWitnessKind : MultimodalWitnessKind
  residualWitnessKind : MultimodalWitnessKind
  populationWitnessKind : MultimodalWitnessKind
  longitudinalWitnessKind : MultimodalWitnessKind

data TrajectorySurfaceKind : Set where
  populationBOLDSurface : TrajectorySurfaceKind
  connectomeSurface : TrajectorySurfaceKind
  fMRISurface : TrajectorySurfaceKind
  axisBundleSurface : TrajectorySurfaceKind
  confoundModelSurface : TrajectorySurfaceKind
  longitudinalDesignSurface : TrajectorySurfaceKind
  multimodalWitnessSurface : TrajectorySurfaceKind
  causalMechanismSurface : TrajectorySurfaceKind
  boundarySurface : TrajectorySurfaceKind

data TrajectoryBoundaryClaim : Set where
  candidateOnlyBoundaryClaim : TrajectoryBoundaryClaim
  noCausalMechanismClaim : TrajectoryBoundaryClaim
  noDiagnosisClaim : TrajectoryBoundaryClaim
  noMindReadingClaim : TrajectoryBoundaryClaim
  noTraumaMechanismProofClaim : TrajectoryBoundaryClaim
  noTreatmentClaim : TrajectoryBoundaryClaim
  noHiddenChartRecoveryClaim : TrajectoryBoundaryClaim
  noClinicalAuthorityClaim : TrajectoryBoundaryClaim

canonicalTrajectoryAxisBundles :
  List TrajectoryAxisBundle
canonicalTrajectoryAxisBundles =
  populationAxisBundle
  ∷ cohortAxisBundle
  ∷ scannerAxisBundle
  ∷ siteAxisBundle
  ∷ conditionAxisBundle
  ∷ treatmentExposureAxisBundle
  ∷ longitudinalFollowUpAxisBundle
  ∷ []

canonicalTrajectoryConfoundModels :
  List TrajectoryConfoundModel
canonicalTrajectoryConfoundModels =
  ageBandConfoundModel
  ∷ siteConfoundModel
  ∷ scannerConfoundModel
  ∷ conditionConfoundModel
  ∷ treatmentExposureConfoundModel
  ∷ boundedDriftConfoundModel
  ∷ []

canonicalLongitudinalDesignKinds :
  List LongitudinalDesignKind
canonicalLongitudinalDesignKinds =
  baselineFollowUpDesign
  ∷ panelTrajectoryDesign
  ∷ boundedDriftDesign
  ∷ populationAggregationDesign
  ∷ proxyCarryForwardDesign
  ∷ []

canonicalMultimodalWitnessKinds :
  List MultimodalWitnessKind
canonicalMultimodalWitnessKinds =
  boldWitnessKind
  ∷ connectomeWitnessKind
  ∷ fMRIWitnessKind
  ∷ residualWitnessKind
  ∷ populationWitnessKind
  ∷ longitudinalWitnessKind
  ∷ []

canonicalTrajectoryBoundaryClaims :
  List TrajectoryBoundaryClaim
canonicalTrajectoryBoundaryClaims =
  candidateOnlyBoundaryClaim
  ∷ noCausalMechanismClaim
  ∷ noDiagnosisClaim
  ∷ noMindReadingClaim
  ∷ noTraumaMechanismProofClaim
  ∷ noTreatmentClaim
  ∷ noHiddenChartRecoveryClaim
  ∷ noClinicalAuthorityClaim
  ∷ []

data TrajectoryModelKind : Set where
  populationBOLDTrajectoryModel : TrajectoryModelKind
  connectomeTrajectoryModel : TrajectoryModelKind
  fMRITrajectoryModel : TrajectoryModelKind
  axisBundleRelativeModel : TrajectoryModelKind
  confoundRelativeModel : TrajectoryModelKind
  longitudinalDesignRelativeModel : TrajectoryModelKind
  multimodalWitnessRelativeModel : TrajectoryModelKind
  failClosedBoundaryModel : TrajectoryModelKind

record PopulationTrajectoryRow : Set where
  constructor mkPopulationTrajectoryRow
  field
    rowIndex : Nat
    rowLabel : String
    rowClaim : String
    rowSurfaceKind : TrajectorySurfaceKind
    rowModelKind : TrajectoryModelKind
    rowAxisBundle : TrajectoryAxisBundle
    rowConfoundModel : TrajectoryConfoundModel
    rowLongitudinalDesign : LongitudinalDesignKind
    rowMultimodalWitness : MultimodalWitnessKind
    rowCandidateOnly : Bool
    rowCandidateOnlyIsTrue : rowCandidateOnly ≡ true
    rowCausalMechanismClaim : Bool
    rowCausalMechanismClaimIsFalse : rowCausalMechanismClaim ≡ false
    rowDiagnosisClaim : Bool
    rowDiagnosisClaimIsFalse : rowDiagnosisClaim ≡ false
    rowMindReadingClaim : Bool
    rowMindReadingClaimIsFalse : rowMindReadingClaim ≡ false
    rowTraumaMechanismProofClaim : Bool
    rowTraumaMechanismProofClaimIsFalse :
      rowTraumaMechanismProofClaim ≡ false
    rowTreatmentClaim : Bool
    rowTreatmentClaimIsFalse : rowTreatmentClaim ≡ false
    rowHiddenChartRecoveryClaim : Bool
    rowHiddenChartRecoveryClaimIsFalse :
      rowHiddenChartRecoveryClaim ≡ false
    rowClinicalAuthorityClaim : Bool
    rowClinicalAuthorityClaimIsFalse :
      rowClinicalAuthorityClaim ≡ false
    rowNotes : List String

open PopulationTrajectoryRow public

canonicalPopulationLongitudinalTrajectoryRows :
  List PopulationTrajectoryRow
canonicalPopulationLongitudinalTrajectoryRows =
  mkPopulationTrajectoryRow
    zero
    "population BOLD trajectory row"
    "population longitudinal BOLD trajectories constrain models as proxy variation, not mechanism"
    populationBOLDSurface
    populationBOLDTrajectoryModel
    populationAxisBundle
    ageBandConfoundModel
    panelTrajectoryDesign
    populationWitnessKind
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
    ( "population longitudinal BOLD proxy variation"
    ∷ "candidate-only constraint relative to axis bundle and confounds"
    ∷ "no diagnosis, mind reading, trauma mechanism proof, treatment, or hidden chart recovery"
    ∷ []
    )
  ∷ mkPopulationTrajectoryRow
    (suc zero)
    "connectome trajectory row"
    "connectome trajectories constrain model placement only as a proxy surface"
    connectomeSurface
    connectomeTrajectoryModel
    cohortAxisBundle
    siteConfoundModel
    populationAggregationDesign
    connectomeWitnessKind
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
    ( "connectome is a trajectory witness, not a causal mechanism"
    ∷ "trajectory interpretation remains candidate-only"
    ∷ "no diagnosis, no hidden chart recovery"
    ∷ []
    )
  ∷ mkPopulationTrajectoryRow
    (suc (suc zero))
    "fMRI trajectory row"
    "fMRI trajectories support bounded proxy drift under longitudinal design"
    fMRISurface
    fMRITrajectoryModel
    scannerAxisBundle
    scannerConfoundModel
    baselineFollowUpDesign
    fMRIWitnessKind
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
    ( "fMRI is retained as multimodal witness material"
    ∷ "bounded drift stays separate from mechanism or clinical inference"
    ∷ "no treatment or mind reading"
    ∷ []
    )
  ∷ mkPopulationTrajectoryRow
    (suc (suc (suc zero)))
    "axis-bundle constraint row"
    "trajectory models are constrained relative to the axis bundle"
    axisBundleSurface
    axisBundleRelativeModel
    siteAxisBundle
    boundedDriftConfoundModel
    proxyCarryForwardDesign
    multimodalWitnessKind
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
    ( "axis bundle remains explicit and non-collapsed"
    ∷ "relative constraint only"
    ∷ "no causal mechanism claim"
    ∷ []
    )
  ∷ mkPopulationTrajectoryRow
    (suc (suc (suc (suc zero))))
    "confound model row"
    "confound models remain explicit so trajectories are not mistaken for mechanism"
    confoundModelSurface
    confoundRelativeModel
    conditionAxisBundle
    conditionConfoundModel
    boundedDriftDesign
    residualWitnessKind
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
    ( "confound model is part of the candidate reading"
    ∷ "trajectory candidate != causal mechanism"
    ∷ "no diagnosis or trauma mechanism proof"
    ∷ []
    )
  ∷ mkPopulationTrajectoryRow
    (suc (suc (suc (suc (suc zero)))))
    "longitudinal design row"
    "longitudinal design carries the time-structured constraint surface"
    longitudinalDesignSurface
    longitudinalDesignRelativeModel
    longitudinalFollowUpAxisBundle
    treatmentExposureConfoundModel
    panelTrajectoryDesign
    longitudinalWitnessKind
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
    ( "longitudinal design stays explicit"
    ∷ "treatment exposure is only a confound model element"
    ∷ "no treatment authority or hidden-chart recovery"
    ∷ []
    )
  ∷ mkPopulationTrajectoryRow
    (suc (suc (suc (suc (suc (suc zero))))))
    "multimodal witness row"
    "multimodal witnesses are the final support for trajectory constraint, not proof"
    multimodalWitnessSurface
    multimodalWitnessRelativeModel
    populationAxisBundle
    boundedDriftConfoundModel
    panelTrajectoryDesign
    boldWitnessKind
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
    ( "multimodal witnesses include population, BOLD, connectome, and fMRI placement"
    ∷ "the row is a proxy carrier, not evidence of mechanism"
    ∷ "no clinical authority is promoted"
    ∷ []
    )
  ∷ mkPopulationTrajectoryRow
    (suc (suc (suc (suc (suc (suc (suc zero)))))))
    "boundary row"
    "candidate-only boundary row collects the explicit non-promotion claims"
    boundarySurface
    failClosedBoundaryModel
    cohortAxisBundle
    boundedDriftConfoundModel
    proxyCarryForwardDesign
    longitudinalWitnessKind
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
    ( "trajectory candidate is not causal mechanism"
    ∷ "no diagnosis, mind reading, trauma mechanism proof, treatment, hidden chart recovery, or clinical authority"
    ∷ []
    )
  ∷ []

record PopulationLongitudinalProxyTrajectoryAggregate : Setω where
  field
    populationLongitudinalBOLDResidualBridge :
      Population.PopulationLongitudinalBOLDResidualBridge

    populationLongitudinalBOLDResidualBridgeIsCanonical :
      populationLongitudinalBOLDResidualBridge ≡
      Population.canonicalPopulationLongitudinalBOLDResidualBridge

    longitudinalFMRIConnectomeDynamicsBridge :
      Longitudinal.LongitudinalFMRIConnectomeDynamicsBridge

    longitudinalFMRIConnectomeDynamicsBridgeIsCanonical :
      longitudinalFMRIConnectomeDynamicsBridge ≡
      Longitudinal.canonicalLongitudinalFMRIConnectomeDynamicsBridge

    fMRIConnectomeProxyGovernance :
      Governance.FMRIConnectomeProxyGovernance

    fMRIConnectomeProxyGovernanceIsCanonical :
      fMRIConnectomeProxyGovernance ≡
      Governance.canonicalFMRIConnectomeProxyGovernance

    regressionReceipt :
      Regression.BodyMemoryRegressionReceipt

    regressionReceiptIsCanonical :
      regressionReceipt ≡ Regression.canonicalBodyMemoryRegressionReceipt

    route :
      PopulationTrajectoryRoute

    routeIsCandidateOnly :
      route ≡ candidateOnlyRoute

    routeAdmissible :
      AdmissiblePopulationTrajectoryRoute route

    axisBundles :
      List TrajectoryAxisBundle

    axisBundlesAreCanonical :
      axisBundles ≡ canonicalTrajectoryAxisBundles

    confoundModels :
      List TrajectoryConfoundModel

    confoundModelsAreCanonical :
      confoundModels ≡ canonicalTrajectoryConfoundModels

    longitudinalDesigns :
      List LongitudinalDesignKind

    longitudinalDesignsAreCanonical :
      longitudinalDesigns ≡ canonicalLongitudinalDesignKinds

    multimodalWitnessKinds :
      List MultimodalWitnessKind

    multimodalWitnessKindsAreCanonical :
      multimodalWitnessKinds ≡ canonicalMultimodalWitnessKinds

    boundaryClaims :
      List TrajectoryBoundaryClaim

    boundaryClaimsAreCanonical :
      boundaryClaims ≡ canonicalTrajectoryBoundaryClaims

    rows :
      List PopulationTrajectoryRow

    rowsAreCanonical :
      rows ≡ canonicalPopulationLongitudinalTrajectoryRows

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    trajectoryCandidateNotCausalMechanism :
      Bool

    trajectoryCandidateNotCausalMechanismIsTrue :
      trajectoryCandidateNotCausalMechanism ≡ true

    noDiagnosis :
      Bool

    noDiagnosisIsFalse :
      noDiagnosis ≡ false

    noMindReading :
      Bool

    noMindReadingIsFalse :
      noMindReading ≡ false

    noTraumaMechanismProof :
      Bool

    noTraumaMechanismProofIsFalse :
      noTraumaMechanismProof ≡ false

    noTreatment :
      Bool

    noTreatmentIsFalse :
      noTreatment ≡ false

    noHiddenChartRecovery :
      Bool

    noHiddenChartRecoveryIsFalse :
      noHiddenChartRecovery ≡ false

    noClinicalAuthority :
      Bool

    noClinicalAuthorityIsFalse :
      noClinicalAuthority ≡ false

    axisBundleRelativeConstraint :
      Bool

    axisBundleRelativeConstraintIsTrue :
      axisBundleRelativeConstraint ≡ true

    confoundModelRelativeConstraint :
      Bool

    confoundModelRelativeConstraintIsTrue :
      confoundModelRelativeConstraint ≡ true

    longitudinalDesignRelativeConstraint :
      Bool

    longitudinalDesignRelativeConstraintIsTrue :
      longitudinalDesignRelativeConstraint ≡ true

    multimodalWitnessRelativeConstraint :
      Bool

    multimodalWitnessRelativeConstraintIsTrue :
      multimodalWitnessRelativeConstraint ≡ true

    aggregateReading :
      String

open PopulationLongitudinalProxyTrajectoryAggregate public

record PopulationLongitudinalProxyTrajectoryReceipt
    (aggregate : PopulationLongitudinalProxyTrajectoryAggregate) : Setω where
  field
    receiptRoute :
      route aggregate ≡ candidateOnlyRoute

    receiptCandidateOnly :
      candidateOnly aggregate ≡ true

    receiptTrajectoryCandidateNotCausalMechanism :
      trajectoryCandidateNotCausalMechanism aggregate ≡ true

    receiptNoDiagnosis :
      noDiagnosis aggregate ≡ false

    receiptNoMindReading :
      noMindReading aggregate ≡ false

    receiptNoTraumaMechanismProof :
      noTraumaMechanismProof aggregate ≡ false

    receiptNoTreatment :
      noTreatment aggregate ≡ false

    receiptNoHiddenChartRecovery :
      noHiddenChartRecovery aggregate ≡ false

    receiptNoClinicalAuthority :
      noClinicalAuthority aggregate ≡ false

    receiptAxisBundleRelativeConstraint :
      axisBundleRelativeConstraint aggregate ≡ true

    receiptConfoundModelRelativeConstraint :
      confoundModelRelativeConstraint aggregate ≡ true

    receiptLongitudinalDesignRelativeConstraint :
      longitudinalDesignRelativeConstraint aggregate ≡ true

    receiptMultimodalWitnessRelativeConstraint :
      multimodalWitnessRelativeConstraint aggregate ≡ true

    receiptReading :
      String

open PopulationLongitudinalProxyTrajectoryReceipt public

canonicalPopulationLongitudinalProxyTrajectoryAggregate :
  PopulationLongitudinalProxyTrajectoryAggregate
canonicalPopulationLongitudinalProxyTrajectoryAggregate =
  record
    { populationLongitudinalBOLDResidualBridge =
        Population.canonicalPopulationLongitudinalBOLDResidualBridge
    ; populationLongitudinalBOLDResidualBridgeIsCanonical =
        refl
    ; longitudinalFMRIConnectomeDynamicsBridge =
        Longitudinal.canonicalLongitudinalFMRIConnectomeDynamicsBridge
    ; longitudinalFMRIConnectomeDynamicsBridgeIsCanonical =
        refl
    ; fMRIConnectomeProxyGovernance =
        Governance.canonicalFMRIConnectomeProxyGovernance
    ; fMRIConnectomeProxyGovernanceIsCanonical =
        refl
    ; regressionReceipt =
        Regression.canonicalBodyMemoryRegressionReceipt
    ; regressionReceiptIsCanonical =
        refl
    ; route =
        candidateOnlyRoute
    ; routeIsCandidateOnly =
        refl
    ; routeAdmissible =
        tt
    ; axisBundles =
        canonicalTrajectoryAxisBundles
    ; axisBundlesAreCanonical =
        refl
    ; confoundModels =
        canonicalTrajectoryConfoundModels
    ; confoundModelsAreCanonical =
        refl
    ; longitudinalDesigns =
        canonicalLongitudinalDesignKinds
    ; longitudinalDesignsAreCanonical =
        refl
    ; multimodalWitnessKinds =
        canonicalMultimodalWitnessKinds
    ; multimodalWitnessKindsAreCanonical =
        refl
    ; boundaryClaims =
        canonicalTrajectoryBoundaryClaims
    ; boundaryClaimsAreCanonical =
        refl
    ; rows =
        canonicalPopulationLongitudinalTrajectoryRows
    ; rowsAreCanonical =
        refl
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; trajectoryCandidateNotCausalMechanism =
        true
    ; trajectoryCandidateNotCausalMechanismIsTrue =
        refl
    ; noDiagnosis =
        false
    ; noDiagnosisIsFalse =
        refl
    ; noMindReading =
        false
    ; noMindReadingIsFalse =
        refl
    ; noTraumaMechanismProof =
        false
    ; noTraumaMechanismProofIsFalse =
        refl
    ; noTreatment =
        false
    ; noTreatmentIsFalse =
        refl
    ; noHiddenChartRecovery =
        false
    ; noHiddenChartRecoveryIsFalse =
        refl
    ; noClinicalAuthority =
        false
    ; noClinicalAuthorityIsFalse =
        refl
    ; axisBundleRelativeConstraint =
        true
    ; axisBundleRelativeConstraintIsTrue =
        refl
    ; confoundModelRelativeConstraint =
        true
    ; confoundModelRelativeConstraintIsTrue =
        refl
    ; longitudinalDesignRelativeConstraint =
        true
    ; longitudinalDesignRelativeConstraintIsTrue =
        refl
    ; multimodalWitnessRelativeConstraint =
        true
    ; multimodalWitnessRelativeConstraintIsTrue =
        refl
    ; aggregateReading =
        "Population longitudinal BOLD/connectome/fMRI trajectories constrain trajectory models only relative to axis bundle, confound model, longitudinal design, and multimodal witnesses; the trajectory candidate is not a causal mechanism, and diagnosis, mind reading, trauma mechanism proof, treatment, hidden chart recovery, and clinical authority are blocked."
    }

canonicalPopulationLongitudinalProxyTrajectoryReceipt :
  PopulationLongitudinalProxyTrajectoryReceipt
    canonicalPopulationLongitudinalProxyTrajectoryAggregate
canonicalPopulationLongitudinalProxyTrajectoryReceipt =
  record
    { receiptRoute =
        refl
    ; receiptCandidateOnly =
        refl
    ; receiptTrajectoryCandidateNotCausalMechanism =
        refl
    ; receiptNoDiagnosis =
        refl
    ; receiptNoMindReading =
        refl
    ; receiptNoTraumaMechanismProof =
        refl
    ; receiptNoTreatment =
        refl
    ; receiptNoHiddenChartRecovery =
        refl
    ; receiptNoClinicalAuthority =
        refl
    ; receiptAxisBundleRelativeConstraint =
        refl
    ; receiptConfoundModelRelativeConstraint =
        refl
    ; receiptLongitudinalDesignRelativeConstraint =
        refl
    ; receiptMultimodalWitnessRelativeConstraint =
        refl
    ; receiptReading =
        "Candidate-only receipt for population longitudinal trajectory constraints."
    }

------------------------------------------------------------------------
-- Canonical lemmas.
------------------------------------------------------------------------

canonicalRouteIsCandidateOnly :
  route canonicalPopulationLongitudinalProxyTrajectoryAggregate ≡
  candidateOnlyRoute
canonicalRouteIsCandidateOnly =
  routeIsCandidateOnly canonicalPopulationLongitudinalProxyTrajectoryAggregate

canonicalCandidateOnlyIsTrue :
  candidateOnly canonicalPopulationLongitudinalProxyTrajectoryAggregate ≡ true
canonicalCandidateOnlyIsTrue =
  candidateOnlyIsTrue canonicalPopulationLongitudinalProxyTrajectoryAggregate

canonicalTrajectoryCandidateNotCausalMechanismIsTrue :
  trajectoryCandidateNotCausalMechanism
    canonicalPopulationLongitudinalProxyTrajectoryAggregate
  ≡
  true
canonicalTrajectoryCandidateNotCausalMechanismIsTrue =
  trajectoryCandidateNotCausalMechanismIsTrue
    canonicalPopulationLongitudinalProxyTrajectoryAggregate

canonicalNoDiagnosisIsFalse :
  noDiagnosis canonicalPopulationLongitudinalProxyTrajectoryAggregate ≡ false
canonicalNoDiagnosisIsFalse =
  noDiagnosisIsFalse canonicalPopulationLongitudinalProxyTrajectoryAggregate

canonicalNoMindReadingIsFalse :
  noMindReading canonicalPopulationLongitudinalProxyTrajectoryAggregate ≡ false
canonicalNoMindReadingIsFalse =
  noMindReadingIsFalse canonicalPopulationLongitudinalProxyTrajectoryAggregate

canonicalNoTraumaMechanismProofIsFalse :
  noTraumaMechanismProof canonicalPopulationLongitudinalProxyTrajectoryAggregate
  ≡
  false
canonicalNoTraumaMechanismProofIsFalse =
  noTraumaMechanismProofIsFalse canonicalPopulationLongitudinalProxyTrajectoryAggregate

canonicalNoTreatmentIsFalse :
  noTreatment canonicalPopulationLongitudinalProxyTrajectoryAggregate ≡ false
canonicalNoTreatmentIsFalse =
  noTreatmentIsFalse canonicalPopulationLongitudinalProxyTrajectoryAggregate

canonicalNoHiddenChartRecoveryIsFalse :
  noHiddenChartRecovery canonicalPopulationLongitudinalProxyTrajectoryAggregate
  ≡
  false
canonicalNoHiddenChartRecoveryIsFalse =
  noHiddenChartRecoveryIsFalse canonicalPopulationLongitudinalProxyTrajectoryAggregate

canonicalNoClinicalAuthorityIsFalse :
  noClinicalAuthority canonicalPopulationLongitudinalProxyTrajectoryAggregate
  ≡
  false
canonicalNoClinicalAuthorityIsFalse =
  noClinicalAuthorityIsFalse canonicalPopulationLongitudinalProxyTrajectoryAggregate

canonicalAxisBundlesAreCanonical :
  axisBundles canonicalPopulationLongitudinalProxyTrajectoryAggregate ≡
  canonicalTrajectoryAxisBundles
canonicalAxisBundlesAreCanonical =
  axisBundlesAreCanonical canonicalPopulationLongitudinalProxyTrajectoryAggregate

canonicalConfoundModelsAreCanonical :
  confoundModels canonicalPopulationLongitudinalProxyTrajectoryAggregate ≡
  canonicalTrajectoryConfoundModels
canonicalConfoundModelsAreCanonical =
  confoundModelsAreCanonical canonicalPopulationLongitudinalProxyTrajectoryAggregate

canonicalLongitudinalDesignsAreCanonical :
  longitudinalDesigns canonicalPopulationLongitudinalProxyTrajectoryAggregate ≡
  canonicalLongitudinalDesignKinds
canonicalLongitudinalDesignsAreCanonical =
  longitudinalDesignsAreCanonical
    canonicalPopulationLongitudinalProxyTrajectoryAggregate

canonicalMultimodalWitnessKindsAreCanonical :
  multimodalWitnessKinds canonicalPopulationLongitudinalProxyTrajectoryAggregate ≡
  canonicalMultimodalWitnessKinds
canonicalMultimodalWitnessKindsAreCanonical =
  multimodalWitnessKindsAreCanonical
    canonicalPopulationLongitudinalProxyTrajectoryAggregate

canonicalBoundaryClaimsAreCanonical :
  boundaryClaims canonicalPopulationLongitudinalProxyTrajectoryAggregate ≡
  canonicalTrajectoryBoundaryClaims
canonicalBoundaryClaimsAreCanonical =
  boundaryClaimsAreCanonical canonicalPopulationLongitudinalProxyTrajectoryAggregate

canonicalRowsAreCanonical :
  rows canonicalPopulationLongitudinalProxyTrajectoryAggregate ≡
  canonicalPopulationLongitudinalTrajectoryRows
canonicalRowsAreCanonical =
  rowsAreCanonical canonicalPopulationLongitudinalProxyTrajectoryAggregate
