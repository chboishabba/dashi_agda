module DASHI.Reasoning.ClaimAuditManifestExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design
import DASHI.Reasoning.DialecticalOppositionNonExplosionExact as Dialectic

------------------------------------------------------------------------
-- DOMAIN-NEUTRAL CLAIM AUDIT MANIFEST
--
-- Structural lineage: the unmerged Governance Round3 / PR #561
-- `JohnPaperClaimManifestV2Exact` separated construct/mechanism receipts from
-- domain-instantiation, etiology, rights, legal-elements and normative receipts.
-- This owner generalises that idea without importing the closed branch and
-- welds it to the current Predicate Normal Form / evidence-admissibility lane.
------------------------------------------------------------------------

data ClaimReceiptKind : Set where
  predicateContentReceipt
  constructReceipt
  mechanismReceipt
  domainInstantiationReceipt
  associationReceipt
  causalReceipt
  etiologyReceipt
  comparatorReceipt
  outcomeReceipt
  transportReceipt
  practicalSignificanceReceipt
  rightsReceipt
  legalElementsReceipt
  normativeReceipt
  sourceCorrectionReceipt
  reproductionReceipt : ClaimReceiptKind

data ClaimReceiptStatus : Set where
  installed
  partiallyInstalled
  missing
  unresolved
  contradictedAtSameScope
  rejectedUnlessNarrowed
  superseded : ClaimReceiptStatus

record TypedClaimReceipt : Set where
  constructor typedClaimReceipt
  field
    kind : ClaimReceiptKind
    status : ClaimReceiptStatus
    sourceOrReason : String
    scopeReading : String

open TypedClaimReceipt public

------------------------------------------------------------------------
-- Audit maturity is not truth status.  It records how far the evidence chain
-- has actually been traversed.
------------------------------------------------------------------------

data AuditStage : Set where
  registered
  sourceRecovered
  citationCompared
  primaryChainTraced
  designAudited
  independentlyCoded
  dualCoded
  reproductionReady
  independentlyReproduced : AuditStage

data SourceChainLevel : Set where
  publishedSurface
  citedSecondarySource
  citedPrimaryStudy
  underlyingDatasetOrArtifact
  independentReproduction : SourceChainLevel

record SourceChainCoordinate : Set where
  constructor sourceChainCoordinate
  field
    level : SourceChainLevel
    locator : String
    recovered : Bool
    boundedReading : String

open SourceChainCoordinate public

------------------------------------------------------------------------
-- Consequence and logical-shape tags are deliberately plural.  A claim can be
-- both universal and normative, or causal and downstream-policy-relevant.
------------------------------------------------------------------------

data ClaimConsequence : Set where
  ordinaryConsequence
  frameworkCentral
  universalScopeConsequence
  causalConsequence
  comparativeConsequence
  normativeConsequence
  downstreamPolicyRelevant : ClaimConsequence

data ClaimAuditCoding : Set where
  sourceMatches
  sourcePlausible
  sourceDoesNotMatch
  independentFullyAdmissible
  independentPartiallyAdmissible
  independentMismatch
  independentUnresolved
  codingDisagreement : ClaimAuditCoding

record ManifestClaim : Set where
  constructor manifestClaim
  field
    claimKey : String
    parentOrPrior : String
    exactPublishedText : String
    normalizedAssertion : PNF.PredicateNormalAssertion
    consequences : List ClaimConsequence
    sourceChain : List SourceChainCoordinate
    receipts : List TypedClaimReceipt
    obligationAudits : List PNF.ObligationAudit
    sourceCoding : ClaimAuditCoding
    independentCoding : ClaimAuditCoding
    stage : AuditStage
    backwardSafeAssertion : PNF.PredicateNormalAssertion
    boundedReading : String

open ManifestClaim public

------------------------------------------------------------------------
-- Core non-promotion boundaries inherited structurally from the earlier claim
-- manifest work and sharpened through PNF obligations.
------------------------------------------------------------------------

data ConstructPromotesDomainInstantiation : Set where

data MechanismPromotesEtiology : Set where

data CitationMatchPromotesPrimaryEvidence : Set where

data SourceCodingPromotesIndependentCoding : Set where

data OneObligationPromotesWholeClaim : Set where

data ReproductionPromotesNormativeAuthority : Set where

constructDoesNotPromoteDomainInstantiation :
  ConstructPromotesDomainInstantiation → ⊥
constructDoesNotPromoteDomainInstantiation ()

mechanismDoesNotPromoteEtiology : MechanismPromotesEtiology → ⊥
mechanismDoesNotPromoteEtiology ()

citationMatchDoesNotPromotePrimaryEvidence :
  CitationMatchPromotesPrimaryEvidence → ⊥
citationMatchDoesNotPromotePrimaryEvidence ()

sourceCodingDoesNotPromoteIndependentCoding :
  SourceCodingPromotesIndependentCoding → ⊥
sourceCodingDoesNotPromoteIndependentCoding ()

oneObligationDoesNotPromoteWholeClaim :
  OneObligationPromotesWholeClaim → ⊥
oneObligationDoesNotPromoteWholeClaim ()

reproductionDoesNotPromoteNormativeAuthority :
  ReproductionPromotesNormativeAuthority → ⊥
reproductionDoesNotPromoteNormativeAuthority ()

------------------------------------------------------------------------
-- Tiny finite coverage witness: one discharged predicate-content coordinate
-- can coexist with an unresolved transport coordinate.  Hence a positive local
-- receipt is not definitionally a whole-claim closure certificate.
------------------------------------------------------------------------

coverageClaim : PNF.PredicateNormalAssertion
coverageClaim = PNF.explicitInstructionUniversalAssertion

contentObligation : PNF.AssertionObligation
contentObligation =
  PNF.assertionObligation
    "coverage-example"
    PNF.predicateContentObligation
    "does the source support the local intervention/outcome predicate?"

transportObligation : PNF.AssertionObligation
transportObligation =
  PNF.assertionObligation
    "coverage-example"
    PNF.transportObligation
    "does the evidence transport from its study domain to the asserted target?"

partialCoverageAudit : List PNF.ObligationAudit
partialCoverageAudit =
  PNF.obligationAudit contentObligation PNF.discharged
    "bounded local evidence receipt"
    "predicate content discharged at the bounded source scope"
  ∷ PNF.obligationAudit transportObligation PNF.unresolved
    "no transport receipt installed"
    "local support does not discharge target-population transport"
  ∷ []

------------------------------------------------------------------------
-- Reproduction/artifact cross-pollination.  The existing repository study-
-- validation lane makes raw artifacts and independent reproduction separate
-- from reported results.  This generic manifest records that requirement
-- abstractly so domains can name their own artifact set.
------------------------------------------------------------------------

record ReproductionRequirement : Set where
  constructor reproductionRequirement
  field
    claim : String
    requiredArtifacts : List String
    reportedResultIsRawArtifact : Bool
    citationMatchIsIndependentReproduction : Bool
    reproducedBoundedResultIsNormativeAuthority : Bool
    reproductionReading : String

canonicalReproductionRequirement : ReproductionRequirement
canonicalReproductionRequirement =
  reproductionRequirement
    "generic consequential claim"
    ("raw observations/data" ∷ "analysis code/method" ∷ "selection/preprocessing receipt" ∷ "statistical outputs" ∷ "version/environment provenance" ∷ [])
    false
    false
    false
    "A paper can identify what should be reproduced without itself supplying every raw artifact; reproduction of a bounded result still does not supply a stronger semantic, causal, transport or normative receipt."

record ClaimAuditManifestBoundary : Set where
  constructor claimAuditManifestBoundary
  field
    auditStageEqualsTruthStatus : Bool
    constructEqualsApplication : Bool
    mechanismEqualsEtiology : Bool
    citationMatchEqualsPrimaryValidation : Bool
    originalCoderEqualsIndependentCoder : Bool
    partialObligationCoverageEqualsWholeClaimSupport : Bool
    independentReproductionEqualsPolicyAuthority : Bool
    backwardSafeRewriteRetained : Bool

canonicalClaimAuditManifestBoundary : ClaimAuditManifestBoundary
canonicalClaimAuditManifestBoundary =
  claimAuditManifestBoundary false false false false false false false true
