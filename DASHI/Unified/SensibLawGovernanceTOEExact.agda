{-# OPTIONS --safe #-}
module DASHI.Unified.SensibLawGovernanceTOEExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Foundations.CanonicalProvenancePromotion as Canonical
import DASHI.Governance.GovernedArtifactCore as Governed
import DASHI.Governance.PromotionSpine as Promotion
import DASHI.Governance.LegalDecisionDoubleProjectionExact as LegalDecision
import DASHI.Governance.LegitimacyEvidenceSeparationExact as Legitimacy
import DASHI.Interop.SensibLawSemanticPromotionPolicy as Semantic
import DASHI.Interop.SensibLawSnowballAttributionLineageAdapterExact as Snowball
import DASHI.Law.SensibLawExpertEvidenceProductionIntegrityExact as Expert
import DASHI.Law.SensibLawRealMatterReviewDecisionExact as Review
import DASHI.Law.SensibLawRealMatterReviewedResumeExact as Resume
import DASHI.Cognition.PNF.SensibLawLegalSemanticAdmissionFrontierExact as Admission
import DASHI.Cognition.PNF.PackedNormativeSparseAdmissionExact as Sparse
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierContractExact as RequirementPareto
import DASHI.Unified.FleetFormalGapTargetTOEExact as Fleet
import DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact as TOEFrame

------------------------------------------------------------------------
-- SENSIBLAW / LEGAL GOVERNANCE TOE CONVERGENCE
--
-- This module owns only the normalization facade.
--
-- Existing SensibLaw, governance, Pareto, snowball, legal-decision and fleet
-- modules remain theorem owners.  The facade does not create legal truth,
-- legal authority, legitimacy, forensic compliance, admission authority, or
-- an Actionstep-specific integration that is not present in the source graph.
--
-- ESD surfaces are not imported as proof authority and are never edited here.
------------------------------------------------------------------------

SemanticPromotionPolicySurface : Set₁
SemanticPromotionPolicySurface = Semantic.SemanticPromotionPolicySurface

ExpertProductionBoundary : Set
ExpertProductionBoundary = Expert.ExpertProductionBoundary

RealMatterReviewBoundary : Set
RealMatterReviewBoundary = Review.RealMatterReviewBoundary

ReviewedResumeBoundary : Set
ReviewedResumeBoundary = Resume.ReviewedResumeBoundary

LegalSemanticAdmissionFrontier : Set
LegalSemanticAdmissionFrontier = Admission.LegalSemanticAdmissionFrontier

FiniteRequirementParetoContract : Set
FiniteRequirementParetoContract = RequirementPareto.FiniteRequirementParetoContract

SensibLawSnowballLineageBoundary : Set
SensibLawSnowballLineageBoundary = Snowball.SensibLawSnowballLineageBoundary

LegitimacyBoundary : Set
LegitimacyBoundary = Legitimacy.LegitimacyBoundary

FleetFormalGapTargetReceipt : Set
FleetFormalGapTargetReceipt = Fleet.FleetFormalGapTargetReceipt

sensibLawSemanticPromotionPolicySurface :
  Semantic.SemanticPromotionPolicySurface
sensibLawSemanticPromotionPolicySurface =
  Semantic.semanticPromotionPolicySurface

sensibLawExpertProductionBoundary :
  Expert.ExpertProductionBoundary
sensibLawExpertProductionBoundary =
  Expert.canonicalExpertProductionBoundary

sensibLawRealMatterReviewBoundary :
  Review.RealMatterReviewBoundary
sensibLawRealMatterReviewBoundary =
  Review.canonicalRealMatterReviewBoundary

sensibLawReviewedResumeBoundary :
  Resume.ReviewedResumeBoundary
sensibLawReviewedResumeBoundary =
  Resume.canonicalReviewedResumeBoundary

sensibLawLegalSemanticAdmissionFrontier :
  Admission.LegalSemanticAdmissionFrontier
sensibLawLegalSemanticAdmissionFrontier =
  Admission.currentLegalSemanticAdmissionFrontier

sensibLawRequirementParetoContract :
  RequirementPareto.FiniteRequirementParetoContract
sensibLawRequirementParetoContract =
  RequirementPareto.canonicalFiniteRequirementParetoContract

sensibLawSnowballLineageBoundary :
  Snowball.SensibLawSnowballLineageBoundary
sensibLawSnowballLineageBoundary =
  Snowball.canonicalSensibLawSnowballLineageBoundary

sensibLawLegitimacyBoundary :
  Legitimacy.LegitimacyBoundary
sensibLawLegitimacyBoundary =
  Legitimacy.canonicalLegitimacyBoundary

sensibLawFleetFormalGapTargetReceipt :
  Fleet.FleetFormalGapTargetReceipt
sensibLawFleetFormalGapTargetReceipt =
  Fleet.canonicalFleetFormalGapTargetReceipt

------------------------------------------------------------------------
-- Canonical semantic non-promotion.
------------------------------------------------------------------------

sensibLawSemanticPromotionLegalAuthorityFlag : Bool
sensibLawSemanticPromotionLegalAuthorityFlag =
  Authority.legalAuthorityFlag Semantic.semanticPromotionAuthorityBoundary

sensibLawSemanticPromotionLegalAuthorityClosed :
  sensibLawSemanticPromotionLegalAuthorityFlag ≡ false
sensibLawSemanticPromotionLegalAuthorityClosed =
  Semantic.semantic-promotion-legal-authority-closed

sensibLawSemanticPromotionTruthAuthorityClosed :
  Authority.truthAuthorityFlag Semantic.semanticPromotionAuthorityBoundary
  ≡ false
sensibLawSemanticPromotionTruthAuthorityClosed =
  Semantic.semantic-promotion-truth-authority-closed

sensibLawSemanticPromotionAllAuthorityClosed :
  Authority.promotesAnyAuthority Semantic.semanticPromotionAuthorityBoundary
  ≡ false
sensibLawSemanticPromotionAllAuthorityClosed =
  Semantic.semantic-promotion-all-authority-closed

------------------------------------------------------------------------
-- Expert-evidence production integrity.
------------------------------------------------------------------------

sensibLawExpertProductionPromotesAnyAuthority : Bool
sensibLawExpertProductionPromotesAnyAuthority =
  Expert.expertProductionPromotesAnyAuthority

sensibLawExpertProductionAuthorityClosed :
  sensibLawExpertProductionPromotesAnyAuthority ≡ false
sensibLawExpertProductionAuthorityClosed =
  Expert.expertProductionPromotesAnyAuthorityIsFalse

QualificationAutomaticallyForensicCompliance : Set
QualificationAutomaticallyForensicCompliance =
  Expert.QualificationAutomaticallyForensicCompliance

sensibLawQualificationDoesNotProveForensicCompliance :
  QualificationAutomaticallyForensicCompliance → ⊥
sensibLawQualificationDoesNotProveForensicCompliance =
  Expert.qualificationDoesNotAutomaticallyProveForensicCompliance

sensibLawReportAdmissionDoesNotRepairMissingInput :
  Expert.ReportAdmissionRepairsMissingInput → ⊥
sensibLawReportAdmissionDoesNotRepairMissingInput =
  Expert.reportAdmissionDoesNotRepairMissingInput

sensibLawMultipleReportsDoNotCreateIndependence :
  Expert.MultipleReportsAutomaticallyIndependent → ⊥
sensibLawMultipleReportsDoNotCreateIndependence =
  Expert.multipleReportsDoNotAutomaticallyCreateIndependence

------------------------------------------------------------------------
-- Real-matter human review remains non-promoting.
------------------------------------------------------------------------

LegalReviewDecisionCreatesApplicability : Set
LegalReviewDecisionCreatesApplicability =
  Review.LegalReviewDecisionCreatesApplicability

LegalReviewDecisionCreatesClaimTruth : Set
LegalReviewDecisionCreatesClaimTruth =
  Review.LegalReviewDecisionCreatesClaimTruth

sensibLawReviewDoesNotCreateApplicability :
  LegalReviewDecisionCreatesApplicability → ⊥
sensibLawReviewDoesNotCreateApplicability =
  Review.legalReviewDecisionDoesNotCreateApplicability

sensibLawReviewDoesNotCreateClaimTruth :
  LegalReviewDecisionCreatesClaimTruth → ⊥
sensibLawReviewDoesNotCreateClaimTruth =
  Review.legalReviewDecisionDoesNotCreateClaimTruth

sensibLawDownstreamCannotRestateEvidenceRole :
  Review.DownstreamMayRestateEvidenceRole → ⊥
sensibLawDownstreamCannotRestateEvidenceRole =
  Review.downstreamCannotRestateEvidenceRole

sensibLawDownstreamCannotRestateNormativeOrder :
  Review.DownstreamMayRestateNormativeOrder → ⊥
sensibLawDownstreamCannotRestateNormativeOrder =
  Review.downstreamCannotRestateNormativeOrder

sensibLawReviewedEvidenceDoesNotCreateRelComparison :
  Resume.ReviewedEvidenceEqualsRelComparison → ⊥
sensibLawReviewedEvidenceDoesNotCreateRelComparison =
  Resume.reviewedEvidenceDoesNotEqualRelComparison

------------------------------------------------------------------------
-- Legal semantic admission remains receipt-gated.
------------------------------------------------------------------------

ParserCandidateAloneAuthorizesAdmission : Set
ParserCandidateAloneAuthorizesAdmission =
  Admission.ParserCandidateAloneAuthorizesAdmission

sensibLawParserCandidateCannotAuthorizeAdmission :
  ParserCandidateAloneAuthorizesAdmission → ⊥
sensibLawParserCandidateCannotAuthorizeAdmission =
  Admission.parserCandidateAloneCannotAuthorizeAdmission

sensibLawSparseAdmissionCannotCreateAuthority :
  Sparse.SparseAdmissionChangesSemanticAuthority → ⊥
sensibLawSparseAdmissionCannotCreateAuthority =
  Admission.sparseAdmissionStillCannotCreateAuthority

sensibLawResidualPriorityIsNotTruthConfidence :
  Admission.ResidualPriorityScoreIsTruthConfidence → ⊥
sensibLawResidualPriorityIsNotTruthConfidence =
  Admission.residualPriorityIsNotTruthConfidence

sensibLawGoldFixtureDoesNotProveUniversalLegalCorrectness :
  Admission.GoldConformanceV01ProvesUniversalLegalCorrectness → ⊥
sensibLawGoldFixtureDoesNotProveUniversalLegalCorrectness =
  Admission.goldV01DoesNotProveUniversalLegalCorrectness

------------------------------------------------------------------------
-- Pareto and snowball remain schedulers/provenance, not discharge.
------------------------------------------------------------------------

sensibLawParetoFrontierMembershipDoesNotSatisfyRequirement :
  RequirementPareto.frontierMembershipDoesNotSatisfyRequirement
    RequirementPareto.canonicalFiniteRequirementParetoContract
  ≡ false
sensibLawParetoFrontierMembershipDoesNotSatisfyRequirement =
  RequirementPareto.frontierMembershipDoesNotSatisfyRequirementIsFalse
    RequirementPareto.canonicalFiniteRequirementParetoContract

sensibLawCitationDoesNotCreateLegalAuthority :
  Snowball.citationCreatesLegalAuthority
    Snowball.canonicalSensibLawSnowballLineageBoundary
  ≡ false
sensibLawCitationDoesNotCreateLegalAuthority = refl

sensibLawRepositoryReconstructionDoesNotBecomeExternalSourceClaim :
  Snowball.repositoryReconstructionBecomesExternalSourceClaim
    Snowball.canonicalSensibLawSnowballLineageBoundary
  ≡ false
sensibLawRepositoryReconstructionDoesNotBecomeExternalSourceClaim = refl

------------------------------------------------------------------------
-- Canonical promotion governance remains fail-closed.
------------------------------------------------------------------------

sensibLawMissingAdmissibilityAbstains :
  Promotion.authorizationFromObligations
    (Canonical.promotionObligations true false true true true)
  ≡ Governed.abstain
sensibLawMissingAdmissibilityAbstains =
  Promotion.missingAdmissibilityAbstains

sensibLawMissingValidationAbstains :
  Promotion.authorizationFromObligations
    (Canonical.promotionObligations true true true true false)
  ≡ Governed.abstain
sensibLawMissingValidationAbstains =
  Promotion.missingValidationAbstains

------------------------------------------------------------------------
-- Official legal surfaces do not reconstruct hidden decision/authority state.
------------------------------------------------------------------------

OfficialLegalSurfaceRecoversFineState : Set
OfficialLegalSurfaceRecoversFineState =
  NF.FactorsThrough LegalDecision.officialSurface LegalDecision.fineLegalStateOf

sensibLawOfficialLegalSurfaceCannotRecoverFineState :
  OfficialLegalSurfaceRecoversFineState → ⊥
sensibLawOfficialLegalSurfaceCannotRecoverFineState =
  LegalDecision.officialSurfaceCannotRecoverFineLegalState

sensibLawOfficialActionCannotRecoverAutonomyAndAuthority :
  NF.FactorsThrough
    LegalDecision.autonomyOfficialSurface
    LegalDecision.fineAutonomyLegalStateOf
  → ⊥
sensibLawOfficialActionCannotRecoverAutonomyAndAuthority =
  LegalDecision.officialActionCannotRecoverAutonomyAndAuthority

------------------------------------------------------------------------
-- Legality is one evidence coordinate.  It is not legitimacy.
------------------------------------------------------------------------

LegalOnlyCreatesLegitimacy : Set₁
LegalOnlyCreatesLegitimacy =
  Legitimacy.AdmittedLegitimacy Legitimacy.demoEvidence Legitimacy.legalOnly

sensibLawLegalOnlyDoesNotCreateLegitimacy :
  LegalOnlyCreatesLegitimacy → ⊥
sensibLawLegalOnlyDoesNotCreateLegitimacy =
  Legitimacy.legalOnlyIsNotAdmittedLegitimacy

sensibLawLegalityAloneImpliesLegitimacyStillFalse :
  Legitimacy.legalityAloneImpliesLegitimacy
    Legitimacy.canonicalLegitimacyBoundary
  ≡ false
sensibLawLegalityAloneImpliesLegitimacyStillFalse =
  Legitimacy.legalityAloneImpliesLegitimacyIsFalse
    Legitimacy.canonicalLegitimacyBoundary

------------------------------------------------------------------------
-- Fleet target discipline.
--
-- The external fleet receipt schedules 58 unformalised gaps.  This bridge does
-- not claim that the legal lane is one numbered gap.  It only preserves the
-- global rule that the 584 discharged fibres remain outside the target.
------------------------------------------------------------------------

legalGovernanceLaneRetargetsDischargedFleetFibres : Bool
legalGovernanceLaneRetargetsDischargedFleetFibres = false

sensibLawLegalLaneDoesNotRetargetDischargedFleetFibres :
  legalGovernanceLaneRetargetsDischargedFleetFibres ≡ false
sensibLawLegalLaneDoesNotRetargetDischargedFleetFibres = refl

sensibLawFleetDischargedFibresRemainDischarged :
  Fleet.dischargedFibresRemainDischarged
    Fleet.canonicalFleetFormalGapTargetReceipt
  ≡ true
sensibLawFleetDischargedFibresRemainDischarged =
  Fleet.fleetDoesNotRetargetDischargedFibres

sensibLawFleetExternalCountDoesNotCreateFormalProof :
  Fleet.externalCountCreatesFormalProof
    Fleet.canonicalFleetFormalGapTargetReceipt
  ≡ false
sensibLawFleetExternalCountDoesNotCreateFormalProof =
  Fleet.fleetExternalCountDoesNotCreateFormalDischarge

------------------------------------------------------------------------
-- Actionstep boundary.
--
-- No Actionstep-specific Agda adapter is imported by this facade.  We therefore
-- do not manufacture Actionstep semantics from generic SensibLaw governance.
-- A future exact adapter may consume this boundary without changing its source
-- owners.
------------------------------------------------------------------------

record ActionstepTOEBoundary : Set where
  constructor actionstep-toe-boundary
  field
    actionstepSpecificAdapterImportedHere : Bool
    actionstepSpecificAdapterImportedHereIsFalse :
      actionstepSpecificAdapterImportedHere ≡ false
    genericSensibLawProofCreatesActionstepAuthority : Bool
    genericSensibLawProofCreatesActionstepAuthorityIsFalse :
      genericSensibLawProofCreatesActionstepAuthority ≡ false
    actionstepReference : String

open ActionstepTOEBoundary public

canonicalActionstepTOEBoundary : ActionstepTOEBoundary
canonicalActionstepTOEBoundary =
  actionstep-toe-boundary
    false refl
    false refl
    "No Actionstep-specific Agda owner is imported by this TOE facade. Exact external-system identity and authority require a separate source-owned adapter."

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F process receipt.
------------------------------------------------------------------------

canonicalSensibLawGovernanceZKPFrame : TOEFrame.TOEZKPFrame
canonicalSensibLawGovernanceZKPFrame =
  TOEFrame.toe-zkp-frame
    "converge existing SensibLaw semantic, review, expert, admission, Pareto, snowball, legal-decision and governance non-promotion proofs into the DASHI TOE"
    "reuse current canonical owners; do not create a second semantic promotion, legal authority, Pareto, snowball, review or governance calculus"
    "add one normalization facade, direct root aliases, validation, and one import-graph attachment"
    "heuristics, parser candidates, review, expert status, report admission, Pareto membership, citations, official action surfaces and legality do not create blocked authority or hidden-state conclusions"
    "one legal-governance normalization lane disjoint from Balaban, Ibrahim, bidi, singular-basin and ESD lanes"
    "PR #1304 owners exist; the fleet 584 discharged fibres remain excluded; the external 58-gap count remains scheduling context; ESD surfaces are read-only"
    "ITIL, ISO 9000/42001/27001/27701/23894/9241, NIST AI RMF, Six Sigma and C4/PlantUML are process lenses only; source authors and meta-introspector repositories retain attribution"
    "EverythingTOESymmetryResolved369, Unifier and Unified.Everything reach the same exact legal-governance owners and non-promotion proofs"
    "code-search reuse audit, source-order regression, root alias validation, trust-escape scan, ESD diff scan, preflight related/discover/lineage, and Agda kernel check when an executor is available"
    false
    false
    false
    false
