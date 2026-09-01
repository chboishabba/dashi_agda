module DASHI.Chemistry.RegulatoryAssayExperimentProofSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Least
import DASHI.Core.ExperimentalCoordinateDesignExact as Coordinate
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Chemistry.RegulatoryAnalyteCoverageBidiExact as Coverage
import DASHI.Chemistry.AssayDetectionEnvelopeExact as Detection
import DASHI.Chemistry.DefensiveRegulatoryAssayStressAuditExact as Stress

------------------------------------------------------------------------
-- REGULATORY ASSAY EXPERIMENT x PROOF-SEARCH CROSS-POLLINATION
--
-- This is deliberately a thin chemistry adapter over canonical repository
-- owners.  Aristotle owns AND/OR proof-search semantics; least-privilege owns
-- theorem-route authority; ExperimentalCoordinateDesign and
-- DiscriminatorSynthesis own measurement-language refinement.  This module does
-- not create another generic search ontology.
--
-- The chemistry use is defensive: identify which empirical/provenance leaves
-- must be discharged before a real assay-robustness claim may be promoted, and
-- which additional validated observations can split a current assay collision.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Experiment coordinates for an assay-coverage audit.
------------------------------------------------------------------------

data AssayExperimentCoordinate : Set where
  regulatoryLimitRoute
  analyteIdentity
  matrixState
  extractionRecovery
  separationResponse
  signalOrIonisationYield
  detectorResponse
  lodMargin
  loqMargin
  complianceDecisionMargin
  orthogonalMethodDiscriminator
  : AssayExperimentCoordinate

assayCoordinateRole : AssayExperimentCoordinate → Coordinate.CoordinateRole
assayCoordinateRole regulatoryLimitRoute = Coordinate.referenceInvariant
assayCoordinateRole analyteIdentity = Coordinate.referenceInvariant
assayCoordinateRole matrixState = Coordinate.nuisanceCoordinate
assayCoordinateRole extractionRecovery = Coordinate.nuisanceCoordinate
assayCoordinateRole separationResponse = Coordinate.nuisanceCoordinate
assayCoordinateRole signalOrIonisationYield = Coordinate.nuisanceCoordinate
assayCoordinateRole detectorResponse = Coordinate.measuredObservable
assayCoordinateRole lodMargin = Coordinate.derivedDiscriminator
assayCoordinateRole loqMargin = Coordinate.derivedDiscriminator
assayCoordinateRole complianceDecisionMargin = Coordinate.derivedDiscriminator
assayCoordinateRole orthogonalMethodDiscriminator = Coordinate.derivedDiscriminator

lodMarginIsDerived :
  assayCoordinateRole lodMargin ≡ Coordinate.derivedDiscriminator
lodMarginIsDerived = refl

matrixStateIsNuisance :
  assayCoordinateRole matrixState ≡ Coordinate.nuisanceCoordinate
matrixStateIsNuisance = refl

detectorResponseIsMeasured :
  assayCoordinateRole detectorResponse ≡ Coordinate.measuredObservable
detectorResponseIsMeasured = refl

------------------------------------------------------------------------
-- Aristotle hypergraph for the real-world promotion cut.
--
-- The root is an AND action: a real assay-stress finding requires all of the
-- evidence leaves below.  Importantly, unresolved leaves are NOT encoded as
-- empty-target terminal actions.  In Aristotle, an empty target list is already
-- a successful proof leaf, so doing that would manufacture closure.
------------------------------------------------------------------------

data AssaySearchState : Set where
  realAssayStressFinding
  availabilityUseLeaf
  regulatoryRouteLeaf
  actualMethodScopeLeaf
  extractionMatrixLeaf
  signalDetectorLeaf
  lodLoqLeaf
  decisionRuleLeaf
  safetyRelevanceLeaf
  : AssaySearchState

data AssaySearchAction : Set where
  assembleRealFinding
  inspectAvailabilityUse
  inspectRegulatoryRoute
  inspectActualMethodScope
  inspectExtractionMatrix
  inspectSignalDetector
  inspectLodLoq
  inspectDecisionRule
  inspectSafetyRelevance
  : AssaySearchAction

assayActionSource : AssaySearchAction → AssaySearchState
assayActionSource assembleRealFinding = realAssayStressFinding
assayActionSource inspectAvailabilityUse = availabilityUseLeaf
assayActionSource inspectRegulatoryRoute = regulatoryRouteLeaf
assayActionSource inspectActualMethodScope = actualMethodScopeLeaf
assayActionSource inspectExtractionMatrix = extractionMatrixLeaf
assayActionSource inspectSignalDetector = signalDetectorLeaf
assayActionSource inspectLodLoq = lodLoqLeaf
assayActionSource inspectDecisionRule = decisionRuleLeaf
assayActionSource inspectSafetyRelevance = safetyRelevanceLeaf

assayActionTargets : AssaySearchAction → List AssaySearchState
assayActionTargets assembleRealFinding =
  availabilityUseLeaf ∷
  regulatoryRouteLeaf ∷
  actualMethodScopeLeaf ∷
  extractionMatrixLeaf ∷
  signalDetectorLeaf ∷
  lodLoqLeaf ∷
  decisionRuleLeaf ∷
  safetyRelevanceLeaf ∷ []
-- Self-blocking unresolved leaves: these are frontier obligations, not proved
-- terminal actions.  A later source/experiment adapter may replace a self-loop
-- with a genuinely discharged route carrying the appropriate authority.
assayActionTargets inspectAvailabilityUse = availabilityUseLeaf ∷ []
assayActionTargets inspectRegulatoryRoute = regulatoryRouteLeaf ∷ []
assayActionTargets inspectActualMethodScope = actualMethodScopeLeaf ∷ []
assayActionTargets inspectExtractionMatrix = extractionMatrixLeaf ∷ []
assayActionTargets inspectSignalDetector = signalDetectorLeaf ∷ []
assayActionTargets inspectLodLoq = lodLoqLeaf ∷ []
assayActionTargets inspectDecisionRule = decisionRuleLeaf ∷ []
assayActionTargets inspectSafetyRelevance = safetyRelevanceLeaf ∷ []

assaySearchGraph : Aristotle.SearchHypergraph
assaySearchGraph = record
  { State = AssaySearchState
  ; Action = AssaySearchAction
  ; source = assayActionSource
  ; targets = assayActionTargets
  }

realFindingRequiresEightLeaves :
  Aristotle.targets assaySearchGraph assembleRealFinding ≡
    availabilityUseLeaf ∷ regulatoryRouteLeaf ∷ actualMethodScopeLeaf ∷
    extractionMatrixLeaf ∷ signalDetectorLeaf ∷ lodLoqLeaf ∷
    decisionRuleLeaf ∷ safetyRelevanceLeaf ∷ []
realFindingRequiresEightLeaves = refl

------------------------------------------------------------------------
-- Search modalities and first-class route failures.
------------------------------------------------------------------------

data AssaySearchModality : Set where
  repositoryProofReuse
  sourceReconstruction
  analyticalMethodReview
  numericalOrCalibrationExperiment
  physicalMeasurement
  : AssaySearchModality

routeDisposition : AssaySearchModality → Least.RouteDisposition
routeDisposition repositoryProofReuse = Least.redirectedReuse
routeDisposition sourceReconstruction = Least.admitted
routeDisposition analyticalMethodReview = Least.admitted
routeDisposition numericalOrCalibrationExperiment = Least.admitted
routeDisposition physicalMeasurement = Least.admitted

-- Common invalid promotions are retained as explicit route errors rather than
-- disappearing from the search history.
tableMembershipAloneProvesLabScope : Least.RouteDisposition
tableMembershipAloneProvesLabScope = Least.rejected Least.scopeMismatch

nonDetectAloneProvesAbsence : Least.RouteDisposition
nonDetectAloneProvesAbsence = Least.rejected Least.strengthMismatch

sameMethodFamilyAloneFixesLOD : Least.RouteDisposition
sameMethodFamilyAloneFixesLOD = Least.rejected Least.carrierMismatch

screenshotAloneProvesBypass : Least.RouteDisposition
screenshotAloneProvesBypass = Least.rejected Least.consumerMismatch

------------------------------------------------------------------------
-- Numerical/physical information can resolve an empirical search obstruction,
-- but observation authority is not theorem-closing authority.
------------------------------------------------------------------------

experimentAuthority : Least.TheoremAuthority
experimentAuthority = Least.analogyOnly

experimentCannotDirectlyCloseProofLeaf :
  Least.ClosedLeafCapability experimentAuthority → ⊥
experimentCannotDirectlyCloseProofLeaf = Least.analogyCannotCloseLeaf

------------------------------------------------------------------------
-- Constructive observation refinement on the existing finite collision.
--
-- This reuses DiscriminatorSynthesis rather than inventing a chemistry-specific
-- notion of experiment.  The bundle measures the hidden synthetic coordinate,
-- so it separates the pair collapsed by the coarse compliance observer.
------------------------------------------------------------------------

expandedSyntheticBundle : Discriminator.ExperimentBundle Coverage.FineBatch
expandedSyntheticBundle = Discriminator.experimentBundle
  Coverage.Presence
  Coverage.offPanelPresence
  1
  "defensive expanded observation of the declared synthetic hidden coordinate"
  "finite DASHI calibration fixture; not a laboratory method validation"

syntheticComplianceCollision :
  Discriminator.CurrentObserverCollision Coverage.complianceSurface
syntheticComplianceCollision =
  Discriminator.currentObserverCollision
    Coverage.cleanPassingBatch
    Coverage.offPanelPresentPassingBatch
    refl

expandedBundleSeparatesSyntheticCollision :
  Discriminator.BundleSeparates
    expandedSyntheticBundle
    Coverage.cleanPassingBatch
    Coverage.offPanelPresentPassingBatch
expandedBundleSeparatesSyntheticCollision =
  Discriminator.bundleSeparates (λ ())

expandedBundleIsLanguageExtension :
  Discriminator.DiscriminatingLanguageExtension Coverage.complianceSurface
expandedBundleIsLanguageExtension =
  Discriminator.discriminatingLanguageExtension
    syntheticComplianceCollision
    expandedSyntheticBundle
    expandedBundleSeparatesSyntheticCollision

expandedBundleInformationMove : Choice.InformationMove
expandedBundleInformationMove =
  Discriminator.bundleInformationMove expandedSyntheticBundle

expandedBundleIsMeasurementMove :
  Choice.kind expandedBundleInformationMove ≡ Choice.takeMeasurement
expandedBundleIsMeasurementMove = refl

------------------------------------------------------------------------
-- Defensive action menu.  These are validation/measurement strategies, not
-- instructions for defeating a screen.
------------------------------------------------------------------------

broadenValidatedObservation : Choice.InformationMove
broadenValidatedObservation = Choice.informationMove
  Choice.takeMeasurement 2
  "broaden declared validated observation language"
  "requires analyte/matrix calibration and method validation"
  "defensive quality-assurance use only"

increaseValidatedSensitivity : Choice.InformationMove
increaseValidatedSensitivity = Choice.informationMove
  Choice.increaseFidelity 3
  "increase validated analytical sensitivity"
  "requires revised LOD/LOQ and matrix-validation receipts"
  "defensive quality-assurance use only"

orthogonalValidatedMeasurement : Choice.InformationMove
orthogonalValidatedMeasurement = Choice.informationMove
  Choice.perturbAndMeasure 4
  "orthogonal validated measurement or recovery challenge"
  "requires independent signal/recovery calibration"
  "defensive quality-assurance use only"

independentReplication : Choice.InformationMove
independentReplication = Choice.informationMove
  Choice.replicateMeasurement 5
  "independent replication"
  "requires declared comparison and reproducibility protocol"
  "defensive quality-assurance use only"

------------------------------------------------------------------------
-- Boundary: measurement can improve the observation language while all legal,
-- safety and proof-authority promotions remain separately gated.
------------------------------------------------------------------------

record RegulatoryAssayExperimentProofSearchBoundary : Set where
  constructor regulatoryAssayExperimentProofSearchBoundary
  field
    assayStressPromotionIsANDCut : Bool
    experimentMayResolveEmpiricalObstruction : Bool
    experimentAutomaticallyClosesFormalProofLeaf : Bool
    tableMembershipAutomaticallyEstablishesLabScope : Bool
    nonDetectAutomaticallyEstablishesAbsence : Bool
    richerValidatedObservationCanSeparateADeclaredCollision : Bool
    cheapestInformationMoveAutomaticallyEstablishesSafetyOrLegality : Bool

canonicalRegulatoryAssayExperimentProofSearchBoundary :
  RegulatoryAssayExperimentProofSearchBoundary
canonicalRegulatoryAssayExperimentProofSearchBoundary =
  regulatoryAssayExperimentProofSearchBoundary
    true true false false false true false
