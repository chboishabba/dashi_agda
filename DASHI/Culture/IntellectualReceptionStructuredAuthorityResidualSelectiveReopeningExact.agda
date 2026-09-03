module DASHI.Culture.IntellectualReceptionStructuredAuthorityResidualSelectiveReopeningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.StructuredResidualProductExact as Structured
import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Core.AdaptiveConsumerModelLoopExact as Adaptive
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Culture.IntellectualReceptionContextIndexedAuthorisedStabiliserProofSearchExperimentExact as Context
import DASHI.Culture.IntellectualReceptionOutcomeStratifiedAuthorityFutureConeExact as Outcome
import DASHI.Culture.IntellectualReceptionSemanticStabiliserParetoAuthorityCrossPollinationExact as Stabiliser

------------------------------------------------------------------------
-- STRUCTURED AUTHORITY RESIDUAL
--
-- The previous outcome-stratified owner deliberately left the missing-authority
-- branch open.  Here that residual is no longer one undifferentiated status.
-- It is a typed product of four independent coordinates:
--
--   source receipt / scope / admissibility / provenance.
--
-- The correspondence to StructuredResidual4's generic axis names is local to
-- this owner and does not redefine those generic axes globally.
------------------------------------------------------------------------

data SourceResidualStatus : Set where
  sourceUnresolved sourceRecovered : SourceResidualStatus

data ScopeResidualStatus : Set where
  scopeUnresolved scopeRecovered : ScopeResidualStatus

data AdmissibilityResidualStatus : Set where
  admissibilityUnresolved admissibilityRecovered : AdmissibilityResidualStatus

data ProvenanceResidualStatus : Set where
  provenanceUnresolved provenanceRecovered : ProvenanceResidualStatus

AuthorityResidual : Set
AuthorityResidual =
  Structured.StructuredResidual4
    SourceResidualStatus
    ScopeResidualStatus
    AdmissibilityResidualStatus
    ProvenanceResidualStatus

allAuthorityResidualsUnresolved : AuthorityResidual
allAuthorityResidualsUnresolved =
  Structured.structuredResidual4
    sourceUnresolved
    scopeUnresolved
    admissibilityUnresolved
    provenanceUnresolved

afterSourceRecovered : AuthorityResidual
afterSourceRecovered =
  Structured.structuredResidual4
    sourceRecovered
    scopeUnresolved
    admissibilityUnresolved
    provenanceUnresolved

afterScopeRecovered : AuthorityResidual
afterScopeRecovered =
  Structured.structuredResidual4
    sourceRecovered
    scopeRecovered
    admissibilityUnresolved
    provenanceUnresolved

afterAdmissibilityRecovered : AuthorityResidual
afterAdmissibilityRecovered =
  Structured.structuredResidual4
    sourceRecovered
    scopeRecovered
    admissibilityRecovered
    provenanceUnresolved

allAuthorityResidualsRecovered : AuthorityResidual
allAuthorityResidualsRecovered =
  Structured.structuredResidual4
    sourceRecovered
    scopeRecovered
    admissibilityRecovered
    provenanceRecovered

structuredAuthorityResidualReconstructs :
  (residual : AuthorityResidual) →
  Structured.structuredResidual4
    (Structured.rawEvidence residual)
    (Structured.geometryLineage residual)
    (Structured.modelFidelity residual)
    (Structured.policyAuthority residual)
  ≡ residual
structuredAuthorityResidualReconstructs =
  Structured.rebuildStructuredResidual4

------------------------------------------------------------------------
-- Residual-sensitive probe policy.
--
-- This is a finite least-privilege priority policy for this fixture only:
-- source before scope, scope before admissibility, admissibility before
-- provenance.  It is not claimed to be a universally optimal experiment order.
------------------------------------------------------------------------

data AuthorityProbe : Set where
  recoverAuthoritySource
  recoverAuthorityScope
  checkAuthorityAdmissibility
  recoverAuthorityProvenance
  authorityResidualClosed
  : AuthorityProbe

nextAuthorityProbe : AuthorityResidual → AuthorityProbe
nextAuthorityProbe
  (Structured.structuredResidual4 sourceUnresolved scope admissibility provenance) =
  recoverAuthoritySource
nextAuthorityProbe
  (Structured.structuredResidual4 sourceRecovered scopeUnresolved admissibility provenance) =
  recoverAuthorityScope
nextAuthorityProbe
  (Structured.structuredResidual4 sourceRecovered scopeRecovered admissibilityUnresolved provenance) =
  checkAuthorityAdmissibility
nextAuthorityProbe
  (Structured.structuredResidual4 sourceRecovered scopeRecovered admissibilityRecovered provenanceUnresolved) =
  recoverAuthorityProvenance
nextAuthorityProbe
  (Structured.structuredResidual4 sourceRecovered scopeRecovered admissibilityRecovered provenanceRecovered) =
  authorityResidualClosed

allUnresolvedChoosesSourceProbe :
  nextAuthorityProbe allAuthorityResidualsUnresolved ≡ recoverAuthoritySource
allUnresolvedChoosesSourceProbe = refl

afterSourceChoosesScopeProbe :
  nextAuthorityProbe afterSourceRecovered ≡ recoverAuthorityScope
afterSourceChoosesScopeProbe = refl

afterScopeChoosesAdmissibilityProbe :
  nextAuthorityProbe afterScopeRecovered ≡ checkAuthorityAdmissibility
afterScopeChoosesAdmissibilityProbe = refl

afterAdmissibilityChoosesProvenanceProbe :
  nextAuthorityProbe afterAdmissibilityRecovered ≡ recoverAuthorityProvenance
afterAdmissibilityChoosesProvenanceProbe = refl

allRecoveredClosesResidualSearch :
  nextAuthorityProbe allAuthorityResidualsRecovered ≡ authorityResidualClosed
allRecoveredClosesResidualSearch = refl

------------------------------------------------------------------------
-- Exact dependency graph for selective reopening.
------------------------------------------------------------------------

data AuthorityArtifact : Set where
  sourceResidualArtifact
  scopeResidualArtifact
  admissibilityResidualArtifact
  provenanceResidualArtifact
  authorityCertificateArtifact
  eligibilityCertificateArtifact
  actionConeCertificateArtifact
  semanticLawfulnessCertificateArtifact
  : AuthorityArtifact

data AuthorityDepends : AuthorityArtifact → AuthorityArtifact → Set where
  sourceFeedsAuthority :
    AuthorityDepends sourceResidualArtifact authorityCertificateArtifact
  scopeFeedsAuthority :
    AuthorityDepends scopeResidualArtifact authorityCertificateArtifact
  admissibilityFeedsAuthority :
    AuthorityDepends admissibilityResidualArtifact authorityCertificateArtifact
  provenanceFeedsAuthority :
    AuthorityDepends provenanceResidualArtifact authorityCertificateArtifact
  authorityFeedsEligibility :
    AuthorityDepends authorityCertificateArtifact eligibilityCertificateArtifact
  eligibilityFeedsActionCone :
    AuthorityDepends eligibilityCertificateArtifact actionConeCertificateArtifact

sourceReopensAuthority :
  Dependency.ReopeningObligation
    AuthorityDepends sourceResidualArtifact authorityCertificateArtifact
sourceReopensAuthority =
  Dependency.oneEdgeCreatesReopeningObligation sourceFeedsAuthority

scopeReopensAuthority :
  Dependency.ReopeningObligation
    AuthorityDepends scopeResidualArtifact authorityCertificateArtifact
scopeReopensAuthority =
  Dependency.oneEdgeCreatesReopeningObligation scopeFeedsAuthority

admissibilityReopensAuthority :
  Dependency.ReopeningObligation
    AuthorityDepends admissibilityResidualArtifact authorityCertificateArtifact
admissibilityReopensAuthority =
  Dependency.oneEdgeCreatesReopeningObligation admissibilityFeedsAuthority

provenanceReopensAuthority :
  Dependency.ReopeningObligation
    AuthorityDepends provenanceResidualArtifact authorityCertificateArtifact
provenanceReopensAuthority =
  Dependency.oneEdgeCreatesReopeningObligation provenanceFeedsAuthority

authorityReopensEligibility :
  Dependency.ReopeningObligation
    AuthorityDepends authorityCertificateArtifact eligibilityCertificateArtifact
authorityReopensEligibility =
  Dependency.oneEdgeCreatesReopeningObligation authorityFeedsEligibility

eligibilityReopensActionCone :
  Dependency.ReopeningObligation
    AuthorityDepends eligibilityCertificateArtifact actionConeCertificateArtifact
eligibilityReopensActionCone =
  Dependency.oneEdgeCreatesReopeningObligation eligibilityFeedsActionCone

sourceReopensEligibility :
  Dependency.ReopeningObligation
    AuthorityDepends sourceResidualArtifact eligibilityCertificateArtifact
sourceReopensEligibility =
  Dependency.obligationsCompose sourceReopensAuthority authorityReopensEligibility

sourceReopensActionCone :
  Dependency.ReopeningObligation
    AuthorityDepends sourceResidualArtifact actionConeCertificateArtifact
sourceReopensActionCone =
  Dependency.obligationsCompose sourceReopensEligibility eligibilityReopensActionCone

scopeReopensActionCone :
  Dependency.ReopeningObligation
    AuthorityDepends scopeResidualArtifact actionConeCertificateArtifact
scopeReopensActionCone =
  Dependency.obligationsCompose
    (Dependency.obligationsCompose scopeReopensAuthority authorityReopensEligibility)
    eligibilityReopensActionCone

admissibilityReopensActionCone :
  Dependency.ReopeningObligation
    AuthorityDepends admissibilityResidualArtifact actionConeCertificateArtifact
admissibilityReopensActionCone =
  Dependency.obligationsCompose
    (Dependency.obligationsCompose admissibilityReopensAuthority authorityReopensEligibility)
    eligibilityReopensActionCone

provenanceReopensActionCone :
  Dependency.ReopeningObligation
    AuthorityDepends provenanceResidualArtifact actionConeCertificateArtifact
provenanceReopensActionCone =
  Dependency.obligationsCompose
    (Dependency.obligationsCompose provenanceReopensAuthority authorityReopensEligibility)
    eligibilityReopensActionCone

------------------------------------------------------------------------
-- Adaptive-loop packaging: one changed residual coordinate reopens exactly an
-- affected certificate by a proof-bearing dependency path.  The existence of
-- these witnesses does not assert that unrelated certificates reopen.
------------------------------------------------------------------------

sourceSelectiveActionConeReopening :
  Adaptive.SelectiveCertificateReopening
    AuthorityArtifact AuthorityDepends sourceResidualArtifact
sourceSelectiveActionConeReopening =
  Adaptive.selectiveCertificateReopening
    actionConeCertificateArtifact
    (Dependency.dependencyPath sourceReopensActionCone)
    "source residual changed; reconsider authority -> eligibility -> action cone"

provenanceSelectiveEligibilityReopening :
  Adaptive.SelectiveCertificateReopening
    AuthorityArtifact AuthorityDepends provenanceResidualArtifact
provenanceSelectiveEligibilityReopening =
  Adaptive.selectiveCertificateReopening
    eligibilityCertificateArtifact
    (Dependency.dependencyPath
      (Dependency.obligationsCompose provenanceReopensAuthority authorityReopensEligibility))
    "provenance residual changed; reconsider authority and downstream eligibility"

noResidualDirectlyReopensSemanticLawfulness :
  ∀ {changed} → AuthorityDepends changed semanticLawfulnessCertificateArtifact → ⊥
noResidualDirectlyReopensSemanticLawfulness ()

------------------------------------------------------------------------
-- Closed residual status is not itself an authority receipt.  The capstone
-- therefore stores the closed structured residual and the independently owned
-- reviewed authority/eligibility receipts together.
------------------------------------------------------------------------

record ResolvedAuthorityResidualReceipt : Set₁ where
  constructor resolved-authority-residual-receipt
  field
    residual : AuthorityResidual
    residualClosed : nextAuthorityProbe residual ≡ authorityResidualClosed
    authority :
      Context.ContextAuthorisedGenerator
        Context.reviewedComparisonContext
        Stabiliser.comparisonFlipXGenerator
    eligibility :
      MDL.Eligible
        (Context.contextEligibilityProblem Context.reviewedComparisonContext)
        Stabiliser.comparisonFlipXGenerator

open ResolvedAuthorityResidualReceipt public

canonicalResolvedAuthorityResidualReceipt : ResolvedAuthorityResidualReceipt
canonicalResolvedAuthorityResidualReceipt =
  resolved-authority-residual-receipt
    allAuthorityResidualsRecovered
    refl
    Context.reviewedComparisonReflectionAuthorised
    Context.reviewedComparisonReflectionEligible

------------------------------------------------------------------------
-- Cross-pollination / no-promotion boundaries.
------------------------------------------------------------------------

structuredResidualBoundaryRetained : Structured.StructuredResidualBoundary
structuredResidualBoundaryRetained = Structured.canonicalStructuredResidualBoundary

dependencyClosureBoundaryRetained : Dependency.DependencyClosureBoundary
dependencyClosureBoundaryRetained = Dependency.canonicalDependencyClosureBoundary

adaptiveLoopBoundaryRetained : Adaptive.AdaptiveConsumerLoopBoundary
adaptiveLoopBoundaryRetained = Adaptive.canonicalAdaptiveConsumerLoopBoundary

data ResidualClosedCreatesAuthorityReceipt : Set where
data ProbePriorityIsUniversalOptimum : Set where
data ReopeningMeansRefutation : Set where
data UnresolvedProvenanceRefutesSemanticLawfulness : Set where
data StructuredAuthorityResidualIsScalarScore : Set where

authorityReceiptIsNotManufacturedByResidualClosure :
  ResidualClosedCreatesAuthorityReceipt → ⊥
authorityReceiptIsNotManufacturedByResidualClosure ()

probePriorityIsNotClaimedUniversalOptimum :
  ProbePriorityIsUniversalOptimum → ⊥
probePriorityIsNotClaimedUniversalOptimum ()

reopeningDoesNotMeanRefutation : ReopeningMeansRefutation → ⊥
reopeningDoesNotMeanRefutation ()

unresolvedProvenanceDoesNotRefuteSemanticLawfulness :
  UnresolvedProvenanceRefutesSemanticLawfulness → ⊥
unresolvedProvenanceDoesNotRefuteSemanticLawfulness ()

structuredAuthorityResidualIsNotScalarScore :
  StructuredAuthorityResidualIsScalarScore → ⊥
structuredAuthorityResidualIsNotScalarScore ()

record IntellectualReceptionStructuredAuthorityResidualBoundary : Set where
  constructor intellectual-reception-structured-authority-residual-boundary
  field
    missingAuthorityResidualIsStructured : Bool
    sourceScopeAdmissibilityProvenanceRemainDistinct : Bool
    nextProbeMayDependOnResidualCoordinate : Bool
    reopeningUsesProofBearingDependencyClosure : Bool
    dependencyAffectedCertificatesMayReopenSelectively : Bool
    everyEvidenceUpdateReopensEveryCertificate : Bool
    residualClosureAutomaticallyCreatesAuthority : Bool
    probePriorityIsUniversalOptimum : Bool
    unresolvedProvenanceRefutesSemanticCandidate : Bool
    structuredResidualIsOneScalarQualityScore : Bool
    sourceAttributionBoundarySurvives : Bool

canonicalIntellectualReceptionStructuredAuthorityResidualBoundary :
  IntellectualReceptionStructuredAuthorityResidualBoundary
canonicalIntellectualReceptionStructuredAuthorityResidualBoundary =
  intellectual-reception-structured-authority-residual-boundary
    true true true true true false false false false false true
