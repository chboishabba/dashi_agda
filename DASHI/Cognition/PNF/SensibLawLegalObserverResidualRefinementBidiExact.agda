module DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact where

------------------------------------------------------------------------
-- LEGAL OBSERVER COLLISION -> TYPED LEGAL RESIDUAL -> ACQUISITION ROUTE
--
-- This module is structural glue. It introduces no new external legal or
-- historical proposition. Source-backed propositions remain owned by the
-- imported SensibLaw case/statute/community-source modules, with their author /
-- institution, title and stable identifiers. The generic epistemic-compression
-- theorem is imported from DASHI.Core and specialised here to legal consumers.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.DominantChartEpistemicCompressionExact as Compression
import DASHI.Core.EpistemicCompressionDeliberativeReopeningBidiExact as Reopening
import DASHI.Core.DeliberativeCyberneticLoopBidiExact as Delib
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate

------------------------------------------------------------------------
-- What legal coordinate is absent from the current observer?
------------------------------------------------------------------------

data LegalResidualKind : Set where
  missingFactualFeature : LegalResidualKind
  missingRelationalFeature : LegalResidualKind
  missingDoctrinalPredicate : LegalResidualKind
  missingInstitutionalConstraint : LegalResidualKind
  missingAuthorityRole : LegalResidualKind
  missingPrecedentApplicability : LegalResidualKind
  missingPrecedentDistinction : LegalResidualKind
  missingStatutoryPredicate : LegalResidualKind
  missingJurisdiction : LegalResidualKind
  missingTemporalScope : LegalResidualKind
  missingExceptionOrDefeater : LegalResidualKind
  missingCommunityAuthority : LegalResidualKind
  missingProvenanceOrPermission : LegalResidualKind
  missingRemedyExecution : LegalResidualKind
  missingCommunityOutcome : LegalResidualKind


------------------------------------------------------------------------
-- Acquisition is typed by the kind of information/authority that is missing.
-- Asking or listening can add information; neither operation manufactures legal
-- authority. Primary-source inspection is distinct from situated participation.
------------------------------------------------------------------------

data LegalAcquisitionRoute : Set where
  recoverPrimaryLegalSource : LegalAcquisitionRoute
  inspectJudicialReasons : LegalAcquisitionRoute
  inspectPrecedentTreatment : LegalAcquisitionRoute
  inspectStatutoryText : LegalAcquisitionRoute
  obtainFactualEvidence : LegalAcquisitionRoute
  resolveJurisdictionAndTime : LegalAcquisitionRoute
  inspectExceptionOrDefeater : LegalAcquisitionRoute
  askSituatedHolder : LegalAcquisitionRoute
  listenToAffectedCommunity : LegalAcquisitionRoute
  deliberateWithAuthorityBearer : LegalAcquisitionRoute
  inspectExecutionEvidence : LegalAcquisitionRoute
  inspectCommunityOutcomeEvidence : LegalAcquisitionRoute


preferredRoute : LegalResidualKind → LegalAcquisitionRoute
preferredRoute missingFactualFeature = obtainFactualEvidence
preferredRoute missingRelationalFeature = obtainFactualEvidence
preferredRoute missingDoctrinalPredicate = inspectJudicialReasons
preferredRoute missingInstitutionalConstraint = inspectJudicialReasons
preferredRoute missingAuthorityRole = recoverPrimaryLegalSource
preferredRoute missingPrecedentApplicability = inspectPrecedentTreatment
preferredRoute missingPrecedentDistinction = inspectJudicialReasons
preferredRoute missingStatutoryPredicate = inspectStatutoryText
preferredRoute missingJurisdiction = resolveJurisdictionAndTime
preferredRoute missingTemporalScope = resolveJurisdictionAndTime
preferredRoute missingExceptionOrDefeater = inspectExceptionOrDefeater
preferredRoute missingCommunityAuthority = deliberateWithAuthorityBearer
preferredRoute missingProvenanceOrPermission = askSituatedHolder
preferredRoute missingRemedyExecution = inspectExecutionEvidence
preferredRoute missingCommunityOutcome = inspectCommunityOutcomeEvidence

------------------------------------------------------------------------
-- A generic observer collision is compiled into a legal residual for an issue.
-- The lost distinction from the generic theorem is retained verbatim as a
-- provenance-bearing reference rather than silently rewritten as a legal fact.
------------------------------------------------------------------------

record LegalObserverResidual
    {Situated Surface Outcome : Set}
    {observe : Situated → Surface}
    {consumer : Situated → Outcome}
    (compression : Compression.ProjectionInadequacyReceipt observe consumer)
    (graph : Algebra.LegalGraph)
    (issue : Algebra.LegalIssue)
    : Set where
  constructor legal-observer-residual
  field
    genericRouting : Reopening.CompressionResidualRouting compression
    residualKind : LegalResidualKind
    missingProposition : Algebra.LegalProposition
    missingPropositionTargetsIssue : String
    expectedAuthorityRole : Algebra.AuthorityRole
    acquisitionRoute : LegalAcquisitionRoute
    acquisitionRouteIsPreferred : acquisitionRoute ≡ preferredRoute residualKind
    sourceOrEvidenceStillRequired : Bool
    sourceOrEvidenceStillRequiredIsTrue : sourceOrEvidenceStillRequired ≡ true
    acquisitionCreatesAuthorityByItself : Bool
    acquisitionCreatesAuthorityByItselfIsFalse : acquisitionCreatesAuthorityByItself ≡ false
    relabelOldObserverRepairsResidual : Bool
    relabelOldObserverRepairsResidualIsFalse : relabelOldObserverRepairsResidual ≡ false

open LegalObserverResidual public

------------------------------------------------------------------------
-- The universal law graph therefore consumes the Core correction policy rather
-- than creating a second, legal-only theory of epistemic repair.
------------------------------------------------------------------------

genericLegalCorrectionPolicy : Reopening.CompressionCorrectionPolicy
genericLegalCorrectionPolicy = Reopening.canonicalCompressionCorrectionPolicy

legalCorrectionRequiresNewInformation :
  Reopening.CompressionCorrectionPolicy.collisionRequiresResidual
    genericLegalCorrectionPolicy ≡ true
legalCorrectionRequiresNewInformation = refl

legalCorrectionCannotBeObserverRelabellingOnly :
  Reopening.CompressionCorrectionPolicy.observerRelabellingAloneCountsAsRepair
    genericLegalCorrectionPolicy ≡ false
legalCorrectionCannotBeObserverRelabellingOnly = refl

------------------------------------------------------------------------
-- Duty-of-care coordinates are compiled into the same residual vocabulary.
-- This does not assert that any listed coordinate is decisive in every duty
-- case; it classifies what kind of missing input would have to be recovered.
------------------------------------------------------------------------

dutyResidualKind : Climate.DutyIssue → LegalResidualKind
dutyResidualKind Climate.reasonableForeseeability = missingFactualFeature
dutyResidualKind Climate.knowledge = missingFactualFeature
dutyResidualKind Climate.control = missingFactualFeature
dutyResidualKind Climate.vulnerability = missingRelationalFeature
dutyResidualKind Climate.assumptionOfResponsibility = missingRelationalFeature
dutyResidualKind Climate.plaintiffClassDeterminacy = missingDoctrinalPredicate
dutyResidualKind Climate.harmTypeDeterminacy = missingDoctrinalPredicate
dutyResidualKind Climate.temporalScope = missingTemporalScope
dutyResidualKind Climate.causation = missingFactualFeature
dutyResidualKind Climate.scopeOfDuty = missingDoctrinalPredicate
dutyResidualKind Climate.statutoryCoherence = missingStatutoryPredicate
dutyResidualKind Climate.coreGovernmentPolicy = missingInstitutionalConstraint
dutyResidualKind Climate.institutionalCompetence = missingInstitutionalConstraint
dutyResidualKind Climate.publicAuthorityFunction = missingInstitutionalConstraint
dutyResidualKind Climate.compensability = missingDoctrinalPredicate

dutyResidualProposition : Climate.DutyIssue → Algebra.LegalProposition
dutyResidualProposition = Negligence.compileDutyIssue

statutoryCoherenceRoutesToStatute :
  preferredRoute (dutyResidualKind Climate.statutoryCoherence)
  ≡ inspectStatutoryText
statutoryCoherenceRoutesToStatute = refl

corePolicyRoutesToJudicialReasons :
  preferredRoute (dutyResidualKind Climate.coreGovernmentPolicy)
  ≡ inspectJudicialReasons
corePolicyRoutesToJudicialReasons = refl

foreseeabilityRoutesToEvidence :
  preferredRoute (dutyResidualKind Climate.reasonableForeseeability)
  ≡ obtainFactualEvidence
foreseeabilityRoutesToEvidence = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ListeningCreatesBindingAuthority : Set where
data RelabellingSameLegalObserverRecoversMissingAuthority : Set where
data SameStatementImpliesSameAuthorityRole : Set where
data MissingCommunityOutcomeIsMerelyMissingLegalDoctrine : Set where
data ObserverCollisionProvesOppression : Set where

listeningDoesNotManufactureAuthority : ListeningCreatesBindingAuthority → ⊥
listeningDoesNotManufactureAuthority ()

relabelDoesNotRecoverAuthority :
  RelabellingSameLegalObserverRecoversMissingAuthority → ⊥
relabelDoesNotRecoverAuthority ()

sameStatementDoesNotFixAuthorityRole : SameStatementImpliesSameAuthorityRole → ⊥
sameStatementDoesNotFixAuthorityRole ()

communityOutcomeIsNotCollapsedIntoDoctrine :
  MissingCommunityOutcomeIsMerelyMissingLegalDoctrine → ⊥
communityOutcomeIsNotCollapsedIntoDoctrine ()

projectionFailureDoesNotByItselfProveOppression : ObserverCollisionProvesOppression → ⊥
projectionFailureDoesNotByItselfProveOppression ()

------------------------------------------------------------------------
-- BIDI donor firewalls remain live.
------------------------------------------------------------------------

listeningStillDoesNotAuthoriseAction :
  Reopening.ListeningAutomaticallyAuthorisesAction → ⊥
listeningStillDoesNotAuthoriseAction = Reopening.listeningDoesNotAuthoriseAction

newResidualStillCannotRewriteOldProvenance :
  Reopening.NewResidualMayRewriteOldSourceProvenance → ⊥
newResidualStillCannotRewriteOldProvenance = Reopening.newResidualDoesNotRewriteOldProvenance
