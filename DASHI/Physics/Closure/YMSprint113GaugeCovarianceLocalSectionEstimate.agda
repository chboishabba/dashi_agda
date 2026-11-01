module DASHI.Physics.Closure.YMSprint113GaugeCovarianceLocalSectionEstimate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint112RenormalizedInterpolationMapCandidate
  as Interp112
import DASHI.Physics.Closure.YMSprint112ContinuumSamplingProjectionMapCandidate
  as Sampling112
import DASHI.Physics.Closure.YMSprint112QuotientIndependenceDiagramLedger
  as Quotient112

------------------------------------------------------------------------
-- Sprint 113 gauge-covariance/local-section estimate package.
--
-- This module records the local-section transition controls needed to make
-- the Sprint112 interpolation and sampling candidates gauge natural.  It is
-- a fail-closed estimate package: the analytic estimates and theorem flags
-- are recorded as absent, while the receipts, lanes, and exact blockers are
-- inhabited and explicit.

gaugeCovarianceLocalSectionEstimateRecorded : Bool
gaugeCovarianceLocalSectionEstimateRecorded = true

localSectionTransitionControlRecorded : Bool
localSectionTransitionControlRecorded = true

holonomyGaugeNaturalityRecorded : Bool
holonomyGaugeNaturalityRecorded = true

mollifierRenormalizationCovarianceRecorded : Bool
mollifierRenormalizationCovarianceRecorded = true

physicalProjectionQuotientCompatibilityRecorded : Bool
physicalProjectionQuotientCompatibilityRecorded = true

exactBlockerLedgerRecorded : Bool
exactBlockerLedgerRecorded = true

localSectionTransitionEstimateProvedHere : Bool
localSectionTransitionEstimateProvedHere = false

holonomyGaugeNaturalityProvedHere : Bool
holonomyGaugeNaturalityProvedHere = false

mollifierRenormalizationCovarianceProvedHere : Bool
mollifierRenormalizationCovarianceProvedHere = false

physicalProjectionQuotientCompatibilityProvedHere : Bool
physicalProjectionQuotientCompatibilityProvedHere = false

gaugeCovarianceEstimateClosedHere : Bool
gaugeCovarianceEstimateClosedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

sprintNumber : Nat
sprintNumber = 113

moduleSourcePath : String
moduleSourcePath =
  "DASHI/Physics/Closure/YMSprint113GaugeCovarianceLocalSectionEstimate.agda"

interpolation112SourcePath : String
interpolation112SourcePath =
  "DASHI/Physics/Closure/YMSprint112RenormalizedInterpolationMapCandidate.agda"

sampling112SourcePath : String
sampling112SourcePath =
  "DASHI/Physics/Closure/YMSprint112ContinuumSamplingProjectionMapCandidate.agda"

quotient112SourcePath : String
quotient112SourcePath =
  "DASHI/Physics/Closure/YMSprint112QuotientIndependenceDiagramLedger.agda"

packageStatementText : String
packageStatementText =
  "Sprint113 records the gauge-covariance/local-section estimate package required before the Sprint112 E_a and P_a candidates can descend through finite and continuum gauge quotients."

localSectionTransitionStatementText : String
localSectionTransitionStatementText =
  "Local section transition control: on chart overlaps, transition functions must transport local representatives with a uniform C_transition(a) window and bounded commutator defect before mollification or sampling is compared."

holonomyGaugeNaturalityStatementText : String
holonomyGaugeNaturalityStatementText =
  "Holonomy gauge naturality: edge and plaquette holonomy samples for gauge-related representatives must be related by endpoint conjugation, so the finite quotient class is unchanged after physical projection."

mollifierRenormalizationCovarianceStatementText : String
mollifierRenormalizationCovarianceStatementText =
  "Mollifier and renormalization covariance: the local smoothing kernel, field-strength normalization Z(a), coupling normalization g(a), volume normalization, and section-patching convention must commute with finite and continuum gauge changes up to a controlled quotient-null error."

physicalProjectionQuotientCompatibilityStatementText : String
physicalProjectionQuotientCompatibilityStatementText =
  "Physical projection quotient compatibility: Pi_a,phys and Pi_phys must preserve the gauge quotient comparison classes used by E_a and P_a, and all gauge-sector leakage terms must vanish in the recorded quotient norm surface."

importSurfaceStatementText : String
importSurfaceStatementText =
  "Imported Sprint112 surfaces: renormalized interpolation candidate E_a, continuum sampling/projection candidate P_a, and quotient-independence diagram ledger."

localSectionTransitionBlockerText : String
localSectionTransitionBlockerText =
  "Exact blocker A: no chart-overlap estimate proves a uniform transition-function bound, local representative independence, or controlled commutator defect for the chosen section atlas."

holonomyGaugeNaturalityBlockerText : String
holonomyGaugeNaturalityBlockerText =
  "Exact blocker B: no proof shows that the Sprint112 edge and plaquette holonomy sampling recipe is gauge-natural under endpoint conjugation before finite quotienting."

mollifierRenormalizationCovarianceBlockerText : String
mollifierRenormalizationCovarianceBlockerText =
  "Exact blocker C: no proof shows that parallel-transport smoothing, mollification, Z(a), g(a), finite-volume normalization, and patching commute with gauge transformations in the comparison window."

physicalProjectionQuotientCompatibilityBlockerText : String
physicalProjectionQuotientCompatibilityBlockerText =
  "Exact blocker D: no proof shows Pi_a,phys and Pi_phys commute with quotient descent for the Sprint112 E_a and P_a candidate surfaces while excluding gauge-sector leakage."

packageClosureBlockerText : String
packageClosureBlockerText =
  "Exact blocker E: the local-section package does not close gauge covariance for E_a or P_a because transition control, holonomy naturality, mollifier covariance, renormalization covariance, and physical projection quotient compatibility remain unproved."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint113 records gauge-covariance/local-section estimate data and exact blockers only; it proves no gauge-covariance theorem, no quotient descent theorem, no Mosco passage, no spectral gap, and no Clay Yang-Mills promotion."

data EstimateLane : Set where
  local-section-transition-lane :
    EstimateLane
  holonomy-gauge-naturality-lane :
    EstimateLane
  mollifier-renormalization-covariance-lane :
    EstimateLane
  physical-projection-quotient-lane :
    EstimateLane
  sprint112-import-surface-lane :
    EstimateLane
  exact-blocker-ledger-lane :
    EstimateLane
  theorem-boundary-lane :
    EstimateLane
  receipt-lane :
    EstimateLane

data EstimateStatus : Set where
  recorded-inhabited :
    EstimateStatus
  imported-sprint112-interpolation :
    EstimateStatus
  imported-sprint112-sampling :
    EstimateStatus
  imported-sprint112-quotient :
    EstimateStatus
  estimate-obligation-recorded :
    EstimateStatus
  exact-blocked-gap :
    EstimateStatus
  theorem-open :
    EstimateStatus
  fail-closed-nonpromotion :
    EstimateStatus

data GaugeCovarianceBlockerKind : Set where
  transition-control-missing :
    GaugeCovarianceBlockerKind
  holonomy-naturality-missing :
    GaugeCovarianceBlockerKind
  mollifier-renormalization-covariance-missing :
    GaugeCovarianceBlockerKind
  physical-projection-quotient-compatibility-missing :
    GaugeCovarianceBlockerKind
  package-closure-missing :
    GaugeCovarianceBlockerKind
  clay-promotion-forbidden :
    GaugeCovarianceBlockerKind

canonicalEstimateLanes : List EstimateLane
canonicalEstimateLanes =
  local-section-transition-lane
  ∷ holonomy-gauge-naturality-lane
  ∷ mollifier-renormalization-covariance-lane
  ∷ physical-projection-quotient-lane
  ∷ sprint112-import-surface-lane
  ∷ exact-blocker-ledger-lane
  ∷ theorem-boundary-lane
  ∷ receipt-lane
  ∷ []

record LaneStatus : Set where
  constructor mkLaneStatus
  field
    lane :
      EstimateLane
    status :
      EstimateStatus
    statement :
      String
    recorded :
      Bool
    proofFlag :
      Bool
    proofFlagIsFalse :
      proofFlag ≡ false

record Sprint112ImportSurface : Setω where
  constructor mkSprint112ImportSurface
  field
    laneStatus :
      LaneStatus
    interpolationReceipt :
      Interp112.YMSprint112RenormalizedInterpolationMapCandidateReceipt
    samplingReceipt :
      Sampling112.SamplingProjectionCandidateReceipt
    quotientReceipt :
      Quotient112.YMSprint112QuotientIndependenceDiagramLedgerReceipt
    interpolationSourcePath :
      String
    samplingSourcePath :
      String
    quotientSourcePath :
      String
    interpolationCandidateRecordedHere :
      Bool
    samplingProjectionCandidateRecordedHere :
      Bool
    quotientDiagramRecordedHere :
      Bool
    importedSurfaceRecorded :
      Bool

record LocalSectionTransitionControl : Set where
  constructor mkLocalSectionTransitionControl
  field
    laneStatus :
      LaneStatus
    statement :
      String
    chartOverlapSymbol :
      String
    transitionFunctionSymbol :
      String
    transitionBoundSymbol :
      String
    commutatorDefectSymbol :
      String
    uniformWindowSymbol :
      String
    interpolationConsumer :
      String
    samplingConsumer :
      String
    recorded :
      Bool
    estimateProvedHere :
      Bool
    estimateProvedHereIsFalse :
      estimateProvedHere ≡ false

record HolonomyGaugeNaturalityControl : Set where
  constructor mkHolonomyGaugeNaturalityControl
  field
    laneStatus :
      LaneStatus
    statement :
      String
    edgeHolonomySymbol :
      String
    plaquetteHolonomySymbol :
      String
    gaugeEndpointConjugationSymbol :
      String
    quotientOutputSymbol :
      String
    sampling112CandidateRecorded :
      Bool
    quotient112DiagramRecorded :
      Bool
    recorded :
      Bool
    naturalityProvedHere :
      Bool
    naturalityProvedHereIsFalse :
      naturalityProvedHere ≡ false

record MollifierRenormalizationCovarianceControl : Setω where
  constructor mkMollifierRenormalizationCovarianceControl
  field
    laneStatus :
      LaneStatus
    statement :
      String
    interpolationReceipt :
      Interp112.YMSprint112RenormalizedInterpolationMapCandidateReceipt
    smoothingKernelSymbol :
      String
    fieldStrengthNormalizationSymbol :
      String
    couplingNormalizationSymbol :
      String
    volumeNormalizationSymbol :
      String
    quotientNullErrorSymbol :
      String
    recorded :
      Bool
    covarianceProvedHere :
      Bool
    covarianceProvedHereIsFalse :
      covarianceProvedHere ≡ false

record PhysicalProjectionQuotientCompatibilityControl : Setω where
  constructor mkPhysicalProjectionQuotientCompatibilityControl
  field
    laneStatus :
      LaneStatus
    statement :
      String
    quotientReceipt :
      Quotient112.YMSprint112QuotientIndependenceDiagramLedgerReceipt
    finiteProjectionSymbol :
      String
    continuumProjectionSymbol :
      String
    embeddingCandidateSymbol :
      String
    projectionCandidateSymbol :
      String
    leakageTermSymbol :
      String
    recorded :
      Bool
    compatibilityProvedHere :
      Bool
    compatibilityProvedHereIsFalse :
      compatibilityProvedHere ≡ false

record ExactBlocker : Set where
  constructor mkExactBlocker
  field
    kind :
      GaugeCovarianceBlockerKind
    lane :
      EstimateLane
    blockerText :
      String
    importedSurfacePath :
      String
    recorded :
      Bool
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    status :
      EstimateStatus

record ExactBlockerLedger : Set where
  constructor mkExactBlockerLedger
  field
    laneStatus :
      LaneStatus
    transitionBlocker :
      ExactBlocker
    holonomyBlocker :
      ExactBlocker
    mollifierRenormalizationBlocker :
      ExactBlocker
    physicalProjectionQuotientBlocker :
      ExactBlocker
    packageClosureBlocker :
      ExactBlocker
    nonPromotionBlocker :
      ExactBlocker
    blockerTexts :
      List String
    recorded :
      Bool
    allBlockersExact :
      Bool

record TheoremFlagBoundary : Set where
  constructor mkTheoremFlagBoundary
  field
    statement :
      String
    localSectionTransitionEstimateProvedHereFlag :
      Bool
    localSectionTransitionEstimateProvedHereFlagIsFalse :
      localSectionTransitionEstimateProvedHereFlag ≡ false
    holonomyGaugeNaturalityProvedHereFlag :
      Bool
    holonomyGaugeNaturalityProvedHereFlagIsFalse :
      holonomyGaugeNaturalityProvedHereFlag ≡ false
    mollifierRenormalizationCovarianceProvedHereFlag :
      Bool
    mollifierRenormalizationCovarianceProvedHereFlagIsFalse :
      mollifierRenormalizationCovarianceProvedHereFlag ≡ false
    physicalProjectionQuotientCompatibilityProvedHereFlag :
      Bool
    physicalProjectionQuotientCompatibilityProvedHereFlagIsFalse :
      physicalProjectionQuotientCompatibilityProvedHereFlag ≡ false
    gaugeCovarianceEstimateClosedHereFlag :
      Bool
    gaugeCovarianceEstimateClosedHereFlagIsFalse :
      gaugeCovarianceEstimateClosedHereFlag ≡ false
    clayYangMillsPromotedHereFlag :
      Bool
    clayYangMillsPromotedHereFlagIsFalse :
      clayYangMillsPromotedHereFlag ≡ false
    status :
      EstimateStatus

record YMSprint113GaugeCovarianceLocalSectionEstimateReceipt : Setω where
  constructor mkYMSprint113GaugeCovarianceLocalSectionEstimateReceipt
  field
    sprint :
      Nat
    sourcePath :
      String
    importSurface :
      Sprint112ImportSurface
    localSectionTransitionControl :
      LocalSectionTransitionControl
    holonomyGaugeNaturalityControl :
      HolonomyGaugeNaturalityControl
    mollifierRenormalizationCovarianceControl :
      MollifierRenormalizationCovarianceControl
    physicalProjectionQuotientCompatibilityControl :
      PhysicalProjectionQuotientCompatibilityControl
    exactBlockerLedger :
      ExactBlockerLedger
    theoremFlagBoundary :
      TheoremFlagBoundary
    lanes :
      List EstimateLane
    receiptStatements :
      List String
    gaugeCovarianceLocalSectionEstimateRecordedHere :
      Bool
    localSectionTransitionControlRecordedHere :
      Bool
    holonomyGaugeNaturalityRecordedHere :
      Bool
    mollifierRenormalizationCovarianceRecordedHere :
      Bool
    physicalProjectionQuotientCompatibilityRecordedHere :
      Bool
    exactBlockerLedgerRecordedHere :
      Bool
    gaugeCovarianceEstimateClosedHereReceipt :
      Bool
    gaugeCovarianceEstimateClosedHereReceiptIsFalse :
      gaugeCovarianceEstimateClosedHereReceipt ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open YMSprint113GaugeCovarianceLocalSectionEstimateReceipt public

canonicalLocalSectionLaneStatus : LaneStatus
canonicalLocalSectionLaneStatus =
  mkLaneStatus
    local-section-transition-lane
    estimate-obligation-recorded
    localSectionTransitionStatementText
    localSectionTransitionControlRecorded
    localSectionTransitionEstimateProvedHere
    refl

canonicalHolonomyLaneStatus : LaneStatus
canonicalHolonomyLaneStatus =
  mkLaneStatus
    holonomy-gauge-naturality-lane
    estimate-obligation-recorded
    holonomyGaugeNaturalityStatementText
    holonomyGaugeNaturalityRecorded
    holonomyGaugeNaturalityProvedHere
    refl

canonicalMollifierRenormalizationLaneStatus : LaneStatus
canonicalMollifierRenormalizationLaneStatus =
  mkLaneStatus
    mollifier-renormalization-covariance-lane
    estimate-obligation-recorded
    mollifierRenormalizationCovarianceStatementText
    mollifierRenormalizationCovarianceRecorded
    mollifierRenormalizationCovarianceProvedHere
    refl

canonicalPhysicalProjectionQuotientLaneStatus : LaneStatus
canonicalPhysicalProjectionQuotientLaneStatus =
  mkLaneStatus
    physical-projection-quotient-lane
    estimate-obligation-recorded
    physicalProjectionQuotientCompatibilityStatementText
    physicalProjectionQuotientCompatibilityRecorded
    physicalProjectionQuotientCompatibilityProvedHere
    refl

canonicalImportSurfaceLaneStatus : LaneStatus
canonicalImportSurfaceLaneStatus =
  mkLaneStatus
    sprint112-import-surface-lane
    imported-sprint112-interpolation
    importSurfaceStatementText
    true
    gaugeCovarianceEstimateClosedHere
    refl

canonicalBlockerLaneStatus : LaneStatus
canonicalBlockerLaneStatus =
  mkLaneStatus
    exact-blocker-ledger-lane
    exact-blocked-gap
    packageClosureBlockerText
    exactBlockerLedgerRecorded
    gaugeCovarianceEstimateClosedHere
    refl

canonicalTheoremBoundaryLaneStatus : LaneStatus
canonicalTheoremBoundaryLaneStatus =
  mkLaneStatus
    theorem-boundary-lane
    fail-closed-nonpromotion
    nonPromotionBoundaryText
    true
    clayYangMillsPromoted
    refl

canonicalSprint112ImportSurface : Sprint112ImportSurface
canonicalSprint112ImportSurface =
  mkSprint112ImportSurface
    canonicalImportSurfaceLaneStatus
    Interp112.canonicalReceipt
    Sampling112.canonicalReceipt
    Quotient112.canonicalReceipt
    interpolation112SourcePath
    sampling112SourcePath
    quotient112SourcePath
    Interp112.interpolationCandidateRecorded
    Sampling112.samplingProjectionCandidateRecorded
    Quotient112.quotientDiagramLedgerRecorded
    true

canonicalLocalSectionTransitionControl : LocalSectionTransitionControl
canonicalLocalSectionTransitionControl =
  mkLocalSectionTransitionControl
    canonicalLocalSectionLaneStatus
    localSectionTransitionStatementText
    "U_i cap U_j"
    "g_ij"
    "C_transition(a)"
    "[nabla_A , g_ij]"
    "0 < a <= a0"
    "E_a local-section smoothing"
    "P_a local representative sampling"
    localSectionTransitionControlRecorded
    localSectionTransitionEstimateProvedHere
    refl

canonicalHolonomyGaugeNaturalityControl : HolonomyGaugeNaturalityControl
canonicalHolonomyGaugeNaturalityControl =
  mkHolonomyGaugeNaturalityControl
    canonicalHolonomyLaneStatus
    holonomyGaugeNaturalityStatementText
    "U_e(A)"
    "U_p(A)"
    "h(t(e)) U_e(A) h(s(e))^{-1}"
    "[Pi_a,phys x_a(A)]"
    Sampling112.plaquetteHolonomySamplingRecorded
    Quotient112.quotientDiagramLedgerRecorded
    holonomyGaugeNaturalityRecorded
    holonomyGaugeNaturalityProvedHere
    refl

canonicalMollifierRenormalizationCovarianceControl :
  MollifierRenormalizationCovarianceControl
canonicalMollifierRenormalizationCovarianceControl =
  mkMollifierRenormalizationCovarianceControl
    canonicalMollifierRenormalizationLaneStatus
    mollifierRenormalizationCovarianceStatementText
    Interp112.canonicalReceipt
    "rho_a"
    "Z(a)"
    "g(a)"
    "Vol_Lambda(a)^{-1/2}"
    "epsilon_quot(a)"
    mollifierRenormalizationCovarianceRecorded
    mollifierRenormalizationCovarianceProvedHere
    refl

canonicalPhysicalProjectionQuotientCompatibilityControl :
  PhysicalProjectionQuotientCompatibilityControl
canonicalPhysicalProjectionQuotientCompatibilityControl =
  mkPhysicalProjectionQuotientCompatibilityControl
    canonicalPhysicalProjectionQuotientLaneStatus
    physicalProjectionQuotientCompatibilityStatementText
    Quotient112.canonicalReceipt
    "Pi_a,phys"
    "Pi_phys"
    "E_a"
    "P_a"
    "leak_gauge(a)"
    physicalProjectionQuotientCompatibilityRecorded
    physicalProjectionQuotientCompatibilityProvedHere
    refl

canonicalTransitionBlocker : ExactBlocker
canonicalTransitionBlocker =
  mkExactBlocker
    transition-control-missing
    local-section-transition-lane
    localSectionTransitionBlockerText
    interpolation112SourcePath
    true
    localSectionTransitionEstimateProvedHere
    refl
    exact-blocked-gap

canonicalHolonomyBlocker : ExactBlocker
canonicalHolonomyBlocker =
  mkExactBlocker
    holonomy-naturality-missing
    holonomy-gauge-naturality-lane
    holonomyGaugeNaturalityBlockerText
    sampling112SourcePath
    true
    holonomyGaugeNaturalityProvedHere
    refl
    exact-blocked-gap

canonicalMollifierRenormalizationBlocker : ExactBlocker
canonicalMollifierRenormalizationBlocker =
  mkExactBlocker
    mollifier-renormalization-covariance-missing
    mollifier-renormalization-covariance-lane
    mollifierRenormalizationCovarianceBlockerText
    interpolation112SourcePath
    true
    mollifierRenormalizationCovarianceProvedHere
    refl
    exact-blocked-gap

canonicalPhysicalProjectionQuotientBlocker : ExactBlocker
canonicalPhysicalProjectionQuotientBlocker =
  mkExactBlocker
    physical-projection-quotient-compatibility-missing
    physical-projection-quotient-lane
    physicalProjectionQuotientCompatibilityBlockerText
    quotient112SourcePath
    true
    physicalProjectionQuotientCompatibilityProvedHere
    refl
    exact-blocked-gap

canonicalPackageClosureBlocker : ExactBlocker
canonicalPackageClosureBlocker =
  mkExactBlocker
    package-closure-missing
    exact-blocker-ledger-lane
    packageClosureBlockerText
    moduleSourcePath
    true
    gaugeCovarianceEstimateClosedHere
    refl
    theorem-open

canonicalNonPromotionBlocker : ExactBlocker
canonicalNonPromotionBlocker =
  mkExactBlocker
    clay-promotion-forbidden
    theorem-boundary-lane
    nonPromotionBoundaryText
    moduleSourcePath
    true
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

canonicalExactBlockerLedger : ExactBlockerLedger
canonicalExactBlockerLedger =
  mkExactBlockerLedger
    canonicalBlockerLaneStatus
    canonicalTransitionBlocker
    canonicalHolonomyBlocker
    canonicalMollifierRenormalizationBlocker
    canonicalPhysicalProjectionQuotientBlocker
    canonicalPackageClosureBlocker
    canonicalNonPromotionBlocker
    (localSectionTransitionBlockerText
     ∷ holonomyGaugeNaturalityBlockerText
     ∷ mollifierRenormalizationCovarianceBlockerText
     ∷ physicalProjectionQuotientCompatibilityBlockerText
     ∷ packageClosureBlockerText
     ∷ nonPromotionBoundaryText
     ∷ Interp112.gaugeCovarianceBlockerText
     ∷ Sampling112.representativeIndependenceBlockerText
     ∷ Quotient112.exactBlockersText
     ∷ [])
    exactBlockerLedgerRecorded
    true

canonicalTheoremFlagBoundary : TheoremFlagBoundary
canonicalTheoremFlagBoundary =
  mkTheoremFlagBoundary
    nonPromotionBoundaryText
    localSectionTransitionEstimateProvedHere
    refl
    holonomyGaugeNaturalityProvedHere
    refl
    mollifierRenormalizationCovarianceProvedHere
    refl
    physicalProjectionQuotientCompatibilityProvedHere
    refl
    gaugeCovarianceEstimateClosedHere
    refl
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

canonicalYMSprint113GaugeCovarianceLocalSectionEstimateReceipt :
  YMSprint113GaugeCovarianceLocalSectionEstimateReceipt
canonicalYMSprint113GaugeCovarianceLocalSectionEstimateReceipt =
  mkYMSprint113GaugeCovarianceLocalSectionEstimateReceipt
    sprintNumber
    moduleSourcePath
    canonicalSprint112ImportSurface
    canonicalLocalSectionTransitionControl
    canonicalHolonomyGaugeNaturalityControl
    canonicalMollifierRenormalizationCovarianceControl
    canonicalPhysicalProjectionQuotientCompatibilityControl
    canonicalExactBlockerLedger
    canonicalTheoremFlagBoundary
    canonicalEstimateLanes
    (packageStatementText
     ∷ localSectionTransitionStatementText
     ∷ holonomyGaugeNaturalityStatementText
     ∷ mollifierRenormalizationCovarianceStatementText
     ∷ physicalProjectionQuotientCompatibilityStatementText
     ∷ importSurfaceStatementText
     ∷ localSectionTransitionBlockerText
     ∷ holonomyGaugeNaturalityBlockerText
     ∷ mollifierRenormalizationCovarianceBlockerText
     ∷ physicalProjectionQuotientCompatibilityBlockerText
     ∷ packageClosureBlockerText
     ∷ nonPromotionBoundaryText
     ∷ [])
    gaugeCovarianceLocalSectionEstimateRecorded
    localSectionTransitionControlRecorded
    holonomyGaugeNaturalityRecorded
    mollifierRenormalizationCovarianceRecorded
    physicalProjectionQuotientCompatibilityRecorded
    exactBlockerLedgerRecorded
    gaugeCovarianceEstimateClosedHere
    refl
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint113GaugeCovarianceLocalSectionEstimateReceipt
canonicalReceipt =
  canonicalYMSprint113GaugeCovarianceLocalSectionEstimateReceipt

canonicalReceiptLocalSectionTransitionEstimateProvedHereIsFalse :
  TheoremFlagBoundary.localSectionTransitionEstimateProvedHereFlag
    (theoremFlagBoundary canonicalReceipt) ≡ false
canonicalReceiptLocalSectionTransitionEstimateProvedHereIsFalse =
  refl

canonicalReceiptHolonomyGaugeNaturalityProvedHereIsFalse :
  TheoremFlagBoundary.holonomyGaugeNaturalityProvedHereFlag
    (theoremFlagBoundary canonicalReceipt) ≡ false
canonicalReceiptHolonomyGaugeNaturalityProvedHereIsFalse =
  refl

canonicalReceiptMollifierRenormalizationCovarianceProvedHereIsFalse :
  TheoremFlagBoundary.mollifierRenormalizationCovarianceProvedHereFlag
    (theoremFlagBoundary canonicalReceipt) ≡ false
canonicalReceiptMollifierRenormalizationCovarianceProvedHereIsFalse =
  refl

canonicalReceiptPhysicalProjectionQuotientCompatibilityProvedHereIsFalse :
  TheoremFlagBoundary.physicalProjectionQuotientCompatibilityProvedHereFlag
    (theoremFlagBoundary canonicalReceipt) ≡ false
canonicalReceiptPhysicalProjectionQuotientCompatibilityProvedHereIsFalse =
  refl

canonicalReceiptGaugeCovarianceEstimateClosedHereIsFalse :
  gaugeCovarianceEstimateClosedHereReceipt canonicalReceipt ≡ false
canonicalReceiptGaugeCovarianceEstimateClosedHereIsFalse =
  refl

canonicalReceiptClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalReceiptClayYangMillsPromotedIsFalse =
  refl

canonicalLocalSectionControlEstimateNotProved :
  LocalSectionTransitionControl.estimateProvedHere
    (localSectionTransitionControl canonicalReceipt) ≡ false
canonicalLocalSectionControlEstimateNotProved =
  refl

canonicalHolonomyNaturalityNotProved :
  HolonomyGaugeNaturalityControl.naturalityProvedHere
    (holonomyGaugeNaturalityControl canonicalReceipt) ≡ false
canonicalHolonomyNaturalityNotProved =
  refl

canonicalMollifierRenormalizationCovarianceNotProved :
  MollifierRenormalizationCovarianceControl.covarianceProvedHere
    (mollifierRenormalizationCovarianceControl canonicalReceipt) ≡ false
canonicalMollifierRenormalizationCovarianceNotProved =
  refl

canonicalPhysicalProjectionQuotientCompatibilityNotProved :
  PhysicalProjectionQuotientCompatibilityControl.compatibilityProvedHere
    (physicalProjectionQuotientCompatibilityControl canonicalReceipt) ≡ false
canonicalPhysicalProjectionQuotientCompatibilityNotProved =
  refl

canonicalReceiptSourcePaths : List String
canonicalReceiptSourcePaths =
  interpolation112SourcePath
  ∷ sampling112SourcePath
  ∷ quotient112SourcePath
  ∷ moduleSourcePath
  ∷ []
