module DASHI.Culture.CohnInstitutionalProofSearchResidualPortfolioReuseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.ProofSearchExperimentalParetoCrossPollinationExact as ProofPareto
import DASHI.Core.RecursiveParetoFrontierLiftingExact as Recursive
import DASHI.Culture.IntellectualReceptionProofRelevantResidualProbeParetoChoiceExact as Portfolio
import DASHI.Culture.CohnInstitutionalResidualDiagnosisExact as Diagnosis
import DASHI.Culture.CohnInstitutionalFeministTwoEyedCrossPollinationExact as Cross

------------------------------------------------------------------------
-- PROOF-SEARCH RESIDUAL PORTFOLIO REUSE
--
-- Audit result: the generic machinery needed after the first Cohn residual
-- diagnosis is already repository-owned.  In particular, the Intellectual
-- Reception proof-relevant probe portfolio already carries:
--
--   * a finite residual-coordinate language;
--   * probes that can discriminate one or several live coordinates;
--   * independent provenance/authority admission gates;
--   * exact downstream reopening obligations from separated coordinates;
--   * consumer-relative eligibility;
--   * least eligible description / resource-cost selection;
--   * Pareto comparison including remaining residual burden.
--
-- Therefore this owner does NOT introduce a second set-cover/search calculus.
-- It records the application seam and redirects the duplicate generic route to
-- canonical proof-search reuse.  Cohn/feminist/Two-Eyed/source-derived residual
-- functions remain application-specific and are not identified with the older
-- Intellectual Reception residual coordinates.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Canonical reuse receipts.
------------------------------------------------------------------------

proofSearchBoundary : ProofSearch.ProofSearchLeastPrivilegeBoundary
proofSearchBoundary = ProofSearch.canonicalProofSearchLeastPrivilegeBoundary

proofParetoBoundary : ProofPareto.ProofSearchExperimentalParetoBoundary
proofParetoBoundary = ProofPareto.canonicalProofSearchExperimentalParetoBoundary

recursiveFrontierBoundary : Recursive.RecursiveParetoFrontierBoundary
recursiveFrontierBoundary = Recursive.canonicalRecursiveParetoFrontierBoundary

existingCheapestEligibleProbe :
  MDL.MinimalEligibleDescription Portfolio.initialProbeProblem Portfolio.provenanceAudit
existingCheapestEligibleProbe = Portfolio.canonicalCheapestEligibleProbe

existingMultiCoordinateSourceReceipt :
  Portfolio.SeparatesCoordinate Portfolio.authorityCoreReview Portfolio.sourceCoordinate
existingMultiCoordinateSourceReceipt = Portfolio.coreReviewSeparatesSource

existingMultiCoordinateScopeReceipt :
  Portfolio.SeparatesCoordinate Portfolio.authorityCoreReview Portfolio.scopeCoordinate
existingMultiCoordinateScopeReceipt = Portfolio.coreReviewSeparatesScope

existingMultiCoordinateAdmissibilityReceipt :
  Portfolio.SeparatesCoordinate Portfolio.authorityCoreReview Portfolio.admissibilityCoordinate
existingMultiCoordinateAdmissibilityReceipt = Portfolio.coreReviewSeparatesAdmissibility

existingPortfolioConsumerAdequacy :
  Portfolio.ProbeConsumerAdequacy Portfolio.authorityCoreReview
existingPortfolioConsumerAdequacy = Portfolio.coreReviewAdequate

------------------------------------------------------------------------
-- Duplicate generic route is redirected rather than re-proved.
------------------------------------------------------------------------

genericPortfolioRouteDisposition : ProofSearch.RouteDisposition
genericPortfolioRouteDisposition = ProofSearch.duplicateTheoremRegression

------------------------------------------------------------------------
-- Application seam.
--
-- The current Cohn owner supplies a concrete collision plus source-bounded
-- residual functions.  The older portfolio supplies generic search/admission/
-- Pareto/reopening grammar.  The bridge is structural; no application residual
-- is claimed definitionally equal to an older residual coordinate.
------------------------------------------------------------------------

currentInstitutionalCollision :
  Diagnosis.InstitutionalWorld × Diagnosis.InstitutionalWorld
currentInstitutionalCollision =
  Diagnosis.representedAcceptedWorld , Diagnosis.originatingRefusedWorld

crossPollinationBoundary : Cross.CrossPollinationBoundary
crossPollinationBoundary = Cross.canonicalCrossPollinationBoundary

record InstitutionalProofSearchReuseMap : Set where
  constructor institutional-proof-search-reuse-map
  field
    applicationCollisionReference : String
    applicationCandidateReference : String
    genericPortfolioReference : String
    admissionReference : String
    paretoReference : String
    reopeningReference : String
    identityBoundaryReference : String

open InstitutionalProofSearchReuseMap public

canonicalReuseMap : InstitutionalProofSearchReuseMap
canonicalReuseMap = institutional-proof-search-reuse-map
  "CohnInstitutionalResidualDiagnosisExact.institutionalCollision"
  "subject-position, provenance, permission, ignorance-production, hermeneutical-refusal and critical-uptake residual functions are application candidates"
  "IntellectualReceptionProofRelevantResidualProbeParetoChoiceExact supplies the canonical finite probe-portfolio grammar"
  "live discrimination is insufficient without measurement provenance and authority"
  "rank only eligible probes; include remaining residual burden as an independent fixture-local Pareto coordinate"
  "a supported separated coordinate carries its exact downstream reopening obligation"
  "structural reuse does not identify Cohn/feminist/Two-Eyed/source concepts with Intellectual Reception residual coordinates"

------------------------------------------------------------------------
-- Boundary / roadmap correction.
------------------------------------------------------------------------

record ProofSearchResidualPortfolioReuseBoundary : Set where
  constructor proof-search-residual-portfolio-reuse-boundary
  field
    genericResidualPortfolioAlreadyOwned : Bool
    newGenericSetCoverSubsystemRequired : Bool
    applicationResidualFunctionsRemainApplicationSpecific : Bool
    existingPortfolioSupportsMultiCoordinateProbe : Bool
    existingPortfolioCarriesDependencyReopening : Bool
    existingPortfolioAlreadyRanksEligibleCandidates : Bool
    residualRelevantFrontierMayMaterialiseOnlySelectedAxes : Bool
    duplicateGenericRouteShouldRedirectToReuse : Bool
    genericPortfolioReuseMakesSourceConceptsIdentical : Bool
    globalMinimumCoverAcrossArbitraryCollisionFamiliesPaid : Bool
    currentPairwiseDiagnosisCanReuseExistingPortfolioGrammar : Bool

open ProofSearchResidualPortfolioReuseBoundary public

canonicalReuseBoundary : ProofSearchResidualPortfolioReuseBoundary
canonicalReuseBoundary = proof-search-residual-portfolio-reuse-boundary
  true
  false
  true
  true
  true
  true
  true
  true
  false
  false
  true

------------------------------------------------------------------------
-- The still-unpaid statement is deliberately narrower than the route we almost
-- duplicated.  Existing machinery handles residual-relevant materialisation,
-- multi-coordinate probes and least/Pareto eligible selection.  It does not, by
-- this audit alone, prove a global minimum set-cover theorem for arbitrary
-- collision families.  Such a theorem should be added only if a literal
-- consumer requires it rather than merely because the abstraction is available.
------------------------------------------------------------------------

record ReuseFrontier : Set where
  constructor reuse-frontier
  field
    paidByProofSearch : String
    paidByCurrentApplication : String
    deliberatelyNotReimplemented : String
    genuinelyUnpaidIfDemanded : String
    stopRule : String

open ReuseFrontier public

canonicalReuseFrontier : ReuseFrontier
canonicalReuseFrontier = reuse-frontier
  "least-privilege route admission; duplicate-route redirection; residual-relevant recursive materialisation; finite probe portfolios; multi-coordinate discrimination; measurement provenance/authority gates; least eligible selection; Pareto remaining-residual burden; dependency-derived reopening"
  "source-bounded institutional candidate residual functions plus one concrete collision and pairwise discriminator receipts"
  "generic collision-family set-cover/search machinery"
  "a theorem that a selected subset is globally minimum across an arbitrary family of institutional collisions, if a real downstream consumer later requires exactly that guarantee"
  "prefer redirected reuse while existing proof-search owners satisfy the literal consumer; create a stronger abstraction only against an explicit unpaid obligation"
