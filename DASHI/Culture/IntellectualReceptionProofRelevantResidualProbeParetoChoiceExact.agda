module DASHI.Culture.IntellectualReceptionProofRelevantResidualProbeParetoChoiceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties as NatP using (≤-refl)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Core.StructuredResidualProductExact as Structured
import DASHI.Culture.IntellectualReceptionStructuredAuthorityResidualSelectiveReopeningExact as Residual

------------------------------------------------------------------------
-- PROOF-RELEVANT RESIDUAL PROBE PORTFOLIO
--
-- The previous owner used a fixed source -> scope -> admissibility ->
-- provenance priority.  This owner removes that priority from the semantics.
-- A probe is evaluated against the current live structured residual by four
-- independent receipts:
--
--   * which unresolved coordinate it can discriminate;
--   * its declared resource/search cost;
--   * provenance + independent authority to perform/read the measurement;
--   * the exact downstream certificate path that would reopen if the measured
--     residual coordinate changes.
--
-- Only after those hard receipts exist do MDL/Pareto coordinates rank probes.
------------------------------------------------------------------------

data ResidualCoordinate : Set where
  sourceCoordinate
  scopeCoordinate
  admissibilityCoordinate
  provenanceCoordinate
  : ResidualCoordinate

data UnresolvedAt : Residual.AuthorityResidual → ResidualCoordinate → Set where
  sourceStillUnresolved :
    ∀ {scope admissibility provenance} →
    UnresolvedAt
      (Structured.structuredResidual4
        Residual.sourceUnresolved scope admissibility provenance)
      sourceCoordinate

  scopeStillUnresolved :
    ∀ {source admissibility provenance} →
    UnresolvedAt
      (Structured.structuredResidual4
        source Residual.scopeUnresolved admissibility provenance)
      scopeCoordinate

  admissibilityStillUnresolved :
    ∀ {source scope provenance} →
    UnresolvedAt
      (Structured.structuredResidual4
        source scope Residual.admissibilityUnresolved provenance)
      admissibilityCoordinate

  provenanceStillUnresolved :
    ∀ {source scope admissibility} →
    UnresolvedAt
      (Structured.structuredResidual4
        source scope admissibility Residual.provenanceUnresolved)
      provenanceCoordinate

coordinateArtifact : ResidualCoordinate → Residual.AuthorityArtifact
coordinateArtifact sourceCoordinate = Residual.sourceResidualArtifact
coordinateArtifact scopeCoordinate = Residual.scopeResidualArtifact
coordinateArtifact admissibilityCoordinate = Residual.admissibilityResidualArtifact
coordinateArtifact provenanceCoordinate = Residual.provenanceResidualArtifact

------------------------------------------------------------------------
-- Finite candidate portfolio.
--
-- `cheapSourceLookup` is intentionally the raw cheapest candidate, but it has
-- no constructor for independent measurement authority.  `provenanceAudit`
-- and `authorityCoreReview` are independently authorised.  The latter can
-- discriminate three currently-live coordinates at once.
------------------------------------------------------------------------

data AuthorityProbeExperiment : Set where
  cheapSourceLookup
  provenanceAudit
  authorityCoreReview
  : AuthorityProbeExperiment

probeMove : AuthorityProbeExperiment → Choice.InformationMove
probeMove cheapSourceLookup =
  Choice.informationMove
    Choice.takeMeasurement
    0
    "cheap source-presence lookup"
    "one low-cost repository/source lookup"
    "candidate only; independent measurement authority absent"
probeMove provenanceAudit =
  Choice.informationMove
    Choice.takeMeasurement
    1
    "provenance audit"
    "source-lineage/provenance review"
    "independent audit authority supplied below"
probeMove authorityCoreReview =
  Choice.informationMove
    Choice.perturbAndMeasure
    2
    "joint authority-core review"
    "source + scope + admissibility review"
    "independent review authority supplied below"

probeCost : AuthorityProbeExperiment → Nat
probeCost probe = Choice.cost (probeMove probe)

rawCheapProbeIsNoMoreExpensiveThanAnyDeclaredProbe :
  (probe : AuthorityProbeExperiment) →
  probeCost cheapSourceLookup ≤ probeCost probe
rawCheapProbeIsNoMoreExpensiveThanAnyDeclaredProbe cheapSourceLookup = z≤n
rawCheapProbeIsNoMoreExpensiveThanAnyDeclaredProbe provenanceAudit = z≤n
rawCheapProbeIsNoMoreExpensiveThanAnyDeclaredProbe authorityCoreReview = z≤n

------------------------------------------------------------------------
-- Coordinate discrimination capability.
------------------------------------------------------------------------

data SeparatesCoordinate :
    AuthorityProbeExperiment → ResidualCoordinate → Set where
  cheapSeparatesSource :
    SeparatesCoordinate cheapSourceLookup sourceCoordinate

  provenanceAuditSeparatesProvenance :
    SeparatesCoordinate provenanceAudit provenanceCoordinate

  coreReviewSeparatesSource :
    SeparatesCoordinate authorityCoreReview sourceCoordinate
  coreReviewSeparatesScope :
    SeparatesCoordinate authorityCoreReview scopeCoordinate
  coreReviewSeparatesAdmissibility :
    SeparatesCoordinate authorityCoreReview admissibilityCoordinate

record SeparatesLiveCoordinate
    (residual : Residual.AuthorityResidual)
    (probe : AuthorityProbeExperiment) : Set where
  constructor separates-live-coordinate
  field
    coordinate : ResidualCoordinate
    unresolved : UnresolvedAt residual coordinate
    separates : SeparatesCoordinate probe coordinate

open SeparatesLiveCoordinate public

cheapSourceSeparatesInitialLiveResidual :
  SeparatesLiveCoordinate Residual.allAuthorityResidualsUnresolved cheapSourceLookup
cheapSourceSeparatesInitialLiveResidual =
  separates-live-coordinate
    sourceCoordinate
    sourceStillUnresolved
    cheapSeparatesSource

provenanceAuditSeparatesInitialLiveResidual :
  SeparatesLiveCoordinate Residual.allAuthorityResidualsUnresolved provenanceAudit
provenanceAuditSeparatesInitialLiveResidual =
  separates-live-coordinate
    provenanceCoordinate
    provenanceStillUnresolved
    provenanceAuditSeparatesProvenance

coreReviewSeparatesInitialLiveResidual :
  SeparatesLiveCoordinate Residual.allAuthorityResidualsUnresolved authorityCoreReview
coreReviewSeparatesInitialLiveResidual =
  separates-live-coordinate
    sourceCoordinate
    sourceStillUnresolved
    coreReviewSeparatesSource

------------------------------------------------------------------------
-- Measurement provenance and authority are separate proof obligations.
-- Having a cheap syntactic/source query is not authority to treat its result as
-- the governance-relevant measurement used by the downstream consumer.
------------------------------------------------------------------------

data MeasurementProvenance : AuthorityProbeExperiment → Set where
  cheapLookupHasTechnicalProvenance :
    MeasurementProvenance cheapSourceLookup
  provenanceAuditHasAuditProvenance :
    MeasurementProvenance provenanceAudit
  coreReviewHasReviewProvenance :
    MeasurementProvenance authorityCoreReview

data MeasurementAuthority : AuthorityProbeExperiment → Set where
  provenanceAuditMeasurementAuthorised :
    MeasurementAuthority provenanceAudit
  coreReviewMeasurementAuthorised :
    MeasurementAuthority authorityCoreReview

------------------------------------------------------------------------
-- Any supported discrimination is connected to the exact dependency owner.
-- Thus a probe does not merely say "this coordinate is interesting"; it carries
-- the theorem-bearing path from that changed residual to the action-cone
-- certificate that must be reconsidered.
------------------------------------------------------------------------

reopeningFromSeparatedCoordinate :
  ∀ {probe coordinate} →
  SeparatesCoordinate probe coordinate →
  Dependency.ReopeningObligation
    Residual.AuthorityDepends
    (coordinateArtifact coordinate)
    Residual.actionConeCertificateArtifact
reopeningFromSeparatedCoordinate cheapSeparatesSource =
  Residual.sourceReopensActionCone
reopeningFromSeparatedCoordinate provenanceAuditSeparatesProvenance =
  Residual.provenanceReopensActionCone
reopeningFromSeparatedCoordinate coreReviewSeparatesSource =
  Residual.sourceReopensActionCone
reopeningFromSeparatedCoordinate coreReviewSeparatesScope =
  Residual.scopeReopensActionCone
reopeningFromSeparatedCoordinate coreReviewSeparatesAdmissibility =
  Residual.admissibilityReopensActionCone

record ProbeAdmission
    (residual : Residual.AuthorityResidual)
    (probe : AuthorityProbeExperiment) : Set where
  constructor probe-admission
  field
    liveDiscrimination : SeparatesLiveCoordinate residual probe
    measurementProvenance : MeasurementProvenance probe
    measurementAuthority : MeasurementAuthority probe

open ProbeAdmission public

record ProbeConsumerAdequacy
    (probe : AuthorityProbeExperiment) : Set where
  constructor probe-consumer-adequacy
  field
    coordinate : ResidualCoordinate
    separates : SeparatesCoordinate probe coordinate
    downstreamReopening :
      Dependency.ReopeningObligation
        Residual.AuthorityDepends
        (coordinateArtifact coordinate)
        Residual.actionConeCertificateArtifact

open ProbeConsumerAdequacy public

adequacyFromSeparation :
  ∀ {probe coordinate} →
  SeparatesCoordinate probe coordinate →
  ProbeConsumerAdequacy probe
adequacyFromSeparation {coordinate = coordinate} separation =
  probe-consumer-adequacy
    coordinate
    separation
    (reopeningFromSeparatedCoordinate separation)

provenanceAuditAdmission :
  ProbeAdmission Residual.allAuthorityResidualsUnresolved provenanceAudit
provenanceAuditAdmission =
  probe-admission
    provenanceAuditSeparatesInitialLiveResidual
    provenanceAuditHasAuditProvenance
    provenanceAuditMeasurementAuthorised

coreReviewAdmission :
  ProbeAdmission Residual.allAuthorityResidualsUnresolved authorityCoreReview
coreReviewAdmission =
  probe-admission
    coreReviewSeparatesInitialLiveResidual
    coreReviewHasReviewProvenance
    coreReviewMeasurementAuthorised

cheapSourceLookupNotAdmitted :
  ProbeAdmission Residual.allAuthorityResidualsUnresolved cheapSourceLookup → ⊥
cheapSourceLookupNotAdmitted
  (probe-admission live provenance ())

provenanceAuditAdequate : ProbeConsumerAdequacy provenanceAudit
provenanceAuditAdequate =
  adequacyFromSeparation provenanceAuditSeparatesProvenance

coreReviewAdequate : ProbeConsumerAdequacy authorityCoreReview
coreReviewAdequate =
  adequacyFromSeparation coreReviewSeparatesSource

------------------------------------------------------------------------
-- Actionability view: all three moves can produce information about the current
-- residual, but that is weaker than admission.  This explicitly separates
-- "can change evidence" from "may be used as the authorised next experiment".
------------------------------------------------------------------------

data ResolvesInitialResidual :
    Choice.InformationMove → Residual.AuthorityResidual → Set where
  cheapSourceProducesInformation :
    ResolvesInitialResidual
      (probeMove cheapSourceLookup)
      Residual.allAuthorityResidualsUnresolved
  provenanceAuditProducesInformation :
    ResolvesInitialResidual
      (probeMove provenanceAudit)
      Residual.allAuthorityResidualsUnresolved
  coreReviewProducesInformation :
    ResolvesInitialResidual
      (probeMove authorityCoreReview)
      Residual.allAuthorityResidualsUnresolved

initialResidualActionabilityProblem : Choice.ActionabilityProblem
initialResidualActionabilityProblem =
  Choice.actionabilityProblem
    Residual.AuthorityResidual
    Residual.allAuthorityResidualsUnresolved
    ResolvesInitialResidual
    "current structured authority residual"
    "choose information that can change the authority/eligibility/action-cone consumer"
    "measurement authority remains an independent admission receipt"

cheapSourceIsResolvingButNotAdmitted :
  Choice.ResolvingMove initialResidualActionabilityProblem
cheapSourceIsResolvingButNotAdmitted =
  Choice.resolvingMove
    (probeMove cheapSourceLookup)
    cheapSourceProducesInformation

------------------------------------------------------------------------
-- Consumer-relative MDL problem over the current live residual fibre.
------------------------------------------------------------------------

data ProbeRefines : AuthorityProbeExperiment → AuthorityProbeExperiment → Set where

probeProblem : Residual.AuthorityResidual → MDL.ConsumerMDLProblem
probeProblem residual =
  MDL.consumerMDLProblem
    AuthorityProbeExperiment
    (ProbeAdmission residual)
    ProbeConsumerAdequacy
    probeCost
    ProbeRefines
    probeReference
    "description length is declared probe resource cost only"
    "current structured authority residual + downstream action-cone consumer"
  where
    probeReference : AuthorityProbeExperiment → String
    probeReference cheapSourceLookup = "cheap source lookup"
    probeReference provenanceAudit = "provenance audit"
    probeReference authorityCoreReview = "joint authority-core review"

initialProbeProblem : MDL.ConsumerMDLProblem
initialProbeProblem = probeProblem Residual.allAuthorityResidualsUnresolved

provenanceAuditEligible :
  MDL.Eligible initialProbeProblem provenanceAudit
provenanceAuditEligible =
  provenanceAuditAdmission , provenanceAuditAdequate

coreReviewEligible :
  MDL.Eligible initialProbeProblem authorityCoreReview
coreReviewEligible =
  coreReviewAdmission , coreReviewAdequate

cheapSourceLookupNotEligible :
  MDL.Eligible initialProbeProblem cheapSourceLookup → ⊥
cheapSourceLookupNotEligible eligible =
  cheapSourceLookupNotAdmitted (proj₁ eligible)

------------------------------------------------------------------------
-- Cheapest eligible probe.
--
-- `provenanceAudit` is the least-cost eligible probe in this finite portfolio.
-- The raw cheapest source lookup is filtered out before cost comparison because
-- its measurement-authority fibre is empty.
------------------------------------------------------------------------

canonicalCheapestEligibleProbe :
  MDL.MinimalEligibleDescription initialProbeProblem provenanceAudit
canonicalCheapestEligibleProbe =
  MDL.minimalEligibleDescription
    provenanceAuditAdmission
    provenanceAuditAdequate
    minimal
    "filter by live-discrimination + provenance + measurement authority + downstream adequacy, then compare resource cost"
  where
    minimal :
      (candidate : AuthorityProbeExperiment) →
      ProbeAdmission Residual.allAuthorityResidualsUnresolved candidate →
      ProbeConsumerAdequacy candidate →
      probeCost provenanceAudit ≤ probeCost candidate
    minimal cheapSourceLookup admitted adequate =
      ⊥-elim (cheapSourceLookupNotAdmitted admitted)
    minimal provenanceAudit admitted adequate = NatP.≤-refl
    minimal authorityCoreReview admitted adequate = s≤s z≤n

------------------------------------------------------------------------
-- Pareto hyperfabric.
--
-- Resource cost is not the only declared coordinate.  We also expose a finite
-- residual-burden shadow: how many of the four initial residual coordinates are
-- left unresolved if the probe succeeds at exactly its declared capability.
-- This is a fixture-local search coordinate, not probability or truth.
------------------------------------------------------------------------

data ProbeCostAxis : Set where
  resourceCostAxis
  remainingResidualBurdenAxis
  : ProbeCostAxis

remainingResidualBurden : AuthorityProbeExperiment → Nat
remainingResidualBurden cheapSourceLookup = 3
remainingResidualBurden provenanceAudit = 3
remainingResidualBurden authorityCoreReview = 1

probeParetoCosts : MDL.CostHyperfabric initialProbeProblem
probeParetoCosts =
  MDL.costHyperfabric
    ProbeCostAxis
    axisCost
    axisReference
  where
    axisCost : ProbeCostAxis → AuthorityProbeExperiment → Nat
    axisCost resourceCostAxis = probeCost
    axisCost remainingResidualBurdenAxis = remainingResidualBurden

    axisReference : ProbeCostAxis → String
    axisReference resourceCostAxis = "declared resource/search cost"
    axisReference remainingResidualBurdenAxis =
      "fixture-local unresolved authority-residual burden after successful probe"

weaklyDominatesSelf :
  (probe : AuthorityProbeExperiment) →
  MDL.WeaklyDominates probeParetoCosts probe probe
weaklyDominatesSelf probe axis = NatP.≤-refl

twoNotLeOne : 2 ≤ 1 → ⊥
twoNotLeOne ()

threeNotLeOne : 3 ≤ 1 → ⊥
threeNotLeOne ()

provenanceAuditParetoAdmissible :
  MDL.ParetoAdmissible probeParetoCosts provenanceAudit
provenanceAuditParetoAdmissible =
  MDL.paretoAdmissible
    provenanceAuditEligible
    noStrictWinner
    "cheapest eligible probe remains Pareto-admissible, but does not dominate the broader core review"
  where
    noStrictWinner :
      (candidate : AuthorityProbeExperiment) →
      MDL.Eligible initialProbeProblem candidate →
      MDL.WeaklyDominates probeParetoCosts candidate provenanceAudit →
      MDL.WeaklyDominates probeParetoCosts provenanceAudit candidate
    noStrictWinner cheapSourceLookup eligible dominates =
      ⊥-elim (cheapSourceLookupNotEligible eligible)
    noStrictWinner provenanceAudit eligible dominates =
      weaklyDominatesSelf provenanceAudit
    noStrictWinner authorityCoreReview eligible dominates =
      ⊥-elim (twoNotLeOne (dominates resourceCostAxis))

coreReviewParetoAdmissible :
  MDL.ParetoAdmissible probeParetoCosts authorityCoreReview
coreReviewParetoAdmissible =
  MDL.paretoAdmissible
    coreReviewEligible
    noStrictWinner
    "broader authority-core review is Pareto-admissible because its residual-burden advantage trades against higher resource cost"
  where
    noStrictWinner :
      (candidate : AuthorityProbeExperiment) →
      MDL.Eligible initialProbeProblem candidate →
      MDL.WeaklyDominates probeParetoCosts candidate authorityCoreReview →
      MDL.WeaklyDominates probeParetoCosts authorityCoreReview candidate
    noStrictWinner cheapSourceLookup eligible dominates =
      ⊥-elim (cheapSourceLookupNotEligible eligible)
    noStrictWinner provenanceAudit eligible dominates =
      ⊥-elim (threeNotLeOne (dominates remainingResidualBurdenAxis))
    noStrictWinner authorityCoreReview eligible dominates =
      weaklyDominatesSelf authorityCoreReview

cheapestEligibleDoesNotDominateBroaderCoreReview :
  MDL.WeaklyDominates probeParetoCosts provenanceAudit authorityCoreReview → ⊥
cheapestEligibleDoesNotDominateBroaderCoreReview dominates =
  threeNotLeOne (dominates remainingResidualBurdenAxis)

broaderCoreReviewDoesNotDominateCheapestEligible :
  MDL.WeaklyDominates probeParetoCosts authorityCoreReview provenanceAudit → ⊥
broaderCoreReviewDoesNotDominateCheapestEligible dominates =
  twoNotLeOne (dominates resourceCostAxis)

------------------------------------------------------------------------
-- Strong finite conclusion.
--
-- We now have BOTH:
--   * a raw cheapest candidate that is not eligible; and
--   * two eligible/Pareto probes where the cheapest eligible probe and the
--     broader residual-closing probe are incomparable across declared axes.
-- Therefore raw/one-dimensional cheapness cannot be used as a proxy for the
-- best next experiment on the live consumer fibre.
------------------------------------------------------------------------

record CheapestProbeNeedNotBeBestNextExperiment : Set₁ where
  constructor cheapest-probe-need-not-be-best-next-experiment
  field
    rawCheapestIsResolving :
      Choice.ResolvingMove initialResidualActionabilityProblem
    rawCheapestIsNotEligible :
      MDL.Eligible initialProbeProblem cheapSourceLookup → ⊥
    cheapestEligible :
      MDL.MinimalEligibleDescription initialProbeProblem provenanceAudit
    cheapestEligiblePareto :
      MDL.ParetoAdmissible probeParetoCosts provenanceAudit
    broaderProbePareto :
      MDL.ParetoAdmissible probeParetoCosts authorityCoreReview
    cheapestDoesNotDominateBroader :
      MDL.WeaklyDominates probeParetoCosts provenanceAudit authorityCoreReview → ⊥
    broaderDoesNotDominateCheapest :
      MDL.WeaklyDominates probeParetoCosts authorityCoreReview provenanceAudit → ⊥

canonicalCheapestProbeNeedNotBeBestNextExperiment :
  CheapestProbeNeedNotBeBestNextExperiment
canonicalCheapestProbeNeedNotBeBestNextExperiment =
  cheapest-probe-need-not-be-best-next-experiment
    cheapSourceIsResolvingButNotAdmitted
    cheapSourceLookupNotEligible
    canonicalCheapestEligibleProbe
    provenanceAuditParetoAdmissible
    coreReviewParetoAdmissible
    cheapestEligibleDoesNotDominateBroaderCoreReview
    broaderCoreReviewDoesNotDominateCheapestEligible

------------------------------------------------------------------------
-- Boundaries / no promotion.
------------------------------------------------------------------------

data CheapnessCreatesMeasurementAuthority : Set where
data CoordinateSeparationCreatesGovernanceAuthority : Set where
data LargerResidualCoverageMeansMoreTruth : Set where
data ParetoAdmissibilityMeansUniqueBestExperiment : Set where
data ReopeningFootprintEqualsHistoricalCausation : Set where
data ProbeCostIsEvidenceQuality : Set where

cheapnessDoesNotCreateMeasurementAuthority :
  CheapnessCreatesMeasurementAuthority → ⊥
cheapnessDoesNotCreateMeasurementAuthority ()

coordinateSeparationDoesNotCreateGovernanceAuthority :
  CoordinateSeparationCreatesGovernanceAuthority → ⊥
coordinateSeparationDoesNotCreateGovernanceAuthority ()

largerResidualCoverageDoesNotMeanMoreTruth :
  LargerResidualCoverageMeansMoreTruth → ⊥
largerResidualCoverageDoesNotMeanMoreTruth ()

paretoAdmissibilityDoesNotMeanUniqueBestExperiment :
  ParetoAdmissibilityMeansUniqueBestExperiment → ⊥
paretoAdmissibilityDoesNotMeanUniqueBestExperiment ()

reopeningFootprintDoesNotEqualHistoricalCausation :
  ReopeningFootprintEqualsHistoricalCausation → ⊥
reopeningFootprintDoesNotEqualHistoricalCausation ()

probeCostDoesNotMeasureEvidenceQuality : ProbeCostIsEvidenceQuality → ⊥
probeCostDoesNotMeasureEvidenceQuality ()

record IntellectualReceptionProofRelevantResidualProbeParetoChoiceBoundary : Set where
  constructor intellectual-reception-proof-relevant-residual-probe-pareto-choice-boundary
  field
    probeChoiceIsIndexedByCurrentResidual : Bool
    coordinateDiscriminationIsProofRelevant : Bool
    measurementProvenanceAndAuthorityAreSeparateReceipts : Bool
    downstreamReopeningUsesExactDependencyClosure : Bool
    rawCheapestProbeMayBeInadmissible : Bool
    cheapestEligibleProbeMayBeParetoIncomparableWithBroaderProbe : Bool
    cheapnessCreatesMeasurementAuthority : Bool
    largerCoverageRanksTruth : Bool
    paretoAdmissibilityMeansUniqueScientificBest : Bool
    probeCostRanksEvidenceQuality : Bool
    sourceAttributionBoundarySurvives : Bool

canonicalIntellectualReceptionProofRelevantResidualProbeParetoChoiceBoundary :
  IntellectualReceptionProofRelevantResidualProbeParetoChoiceBoundary
canonicalIntellectualReceptionProofRelevantResidualProbeParetoChoiceBoundary =
  intellectual-reception-proof-relevant-residual-probe-pareto-choice-boundary
    true true true true true true false false false false true
