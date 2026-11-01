module DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Core.SnowballPluralLensInvariantExact as Snow
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Reasoning.BlockedImplicationExperimentBackpropExact as Backprop

------------------------------------------------------------------------
-- DISCOVERY / ADMISSION LOOP FOR THE SNOWBALL PLURAL-LENS INVARIANT
--
-- Candidate axes may be proposed by proof search, failed factorisation,
-- experimental design, observed residuals, WrongType/fallacy diagnosis,
-- humour/irony/representation mismatch, affected-subject testimony or other
-- local consumers. Proposal is not admission. Admission is query-indexed and
-- requires an explicit relevance/adequacy reason plus source/authority bounds.
------------------------------------------------------------------------

data DiscoveryRoute : Set where
  proofSearch : DiscoveryRoute
  failedFactorsThrough : DiscoveryRoute
  experimentalDesign : DiscoveryRoute
  residualObservation : DiscoveryRoute
  wrongTypeDiagnosis : DiscoveryRoute
  fallacyDiagnosis : DiscoveryRoute
  humourRepresentationMismatch : DiscoveryRoute
  affectedSubjectVoice : DiscoveryRoute
  sourceProvenanceMismatch : DiscoveryRoute
  externalKnowledgeComparison : DiscoveryRoute

data AdmissionStatus : Set where
  proposed : AdmissionStatus
  admissibleCandidate : AdmissionStatus
  admittedRelevantAxis : AdmissionStatus
  rejectedAxis : AdmissionStatus
  unresolvedAxis : AdmissionStatus

record AxisProposal (Axis : Set) : Set where
  constructor axis-proposal
  field
    axis : Axis
    route : DiscoveryRoute
    consumerReference : String
    queryReference : String
    evidenceOrDefectReference : String
    sourceBoundaryReference : String
    authorityBoundaryReference : String
open AxisProposal public

record AdmissibleAxis {Axis : Set} (proposal : AxisProposal Axis) : Set where
  constructor admissible-axis
  field
    status : AdmissionStatus
    consumerCanDistinguish : Bool
    factorisationOrAdequacyChecked : Bool
    sourceRoleChecked : Bool
    authorityRoleChecked : Bool
    wrongTypeOrFallacyChecked : Bool
    experimentalDesignNeeded : Bool
    promotionStillReauditable : Bool
open AdmissibleAxis public

record DiscoveryAdmissionPolicy : Set where
  constructor discovery-admission-policy
  field
    proofSearchMayProposeAxes : Bool
    proofSearchMaySelfCertifyAxis : Bool
    failedFactorisationMayCreateRepairDemand : Bool
    experimentSelectionEqualsEvidence : Bool
    evidenceEqualsAdmission : Bool
    wrongTypeDiagnosisCanBlockPromotion : Bool
    humourCanExposeRepresentationMismatch : Bool
    admittedAxesSnowballIntoFutureLens : Bool
open DiscoveryAdmissionPolicy public

canonicalDiscoveryAdmissionPolicy : DiscoveryAdmissionPolicy
canonicalDiscoveryAdmissionPolicy = discovery-admission-policy
  true false true false false true true true

------------------------------------------------------------------------
-- Generic relationship to the existing invariant.
------------------------------------------------------------------------

record AdmittedLensExtension
    (Old New Extended : Set)
    (oldLens : Snow.PluralLens Old)
    (extendedLens : Snow.PluralLens Extended) : Set where
  constructor admitted-lens-extension
  field
    extension : Snow.LensExtension Old New Extended oldLens extendedLens
    eachNewAxisHasAdmissionReceipt : New → Bool
    proofSearchOrExperimentIsDiscoveryOnly : Bool
    oldRelevantAxesCannotBeDropped : Bool
open AdmittedLensExtension public

------------------------------------------------------------------------
-- FactorsThrough is used both positively and negatively:
--   success can show a coarse surface suffices for one query;
--   failure gives a typed reason to snowball a missing axis or observer.
------------------------------------------------------------------------

data FactorisationFailureMayBeIgnored : Set where
data ProofSearchResultCreatesTruth : Set where
data ExperimentPlanCreatesEvidence : Set where
data HumourSurfaceCreatesSpeakerIntent : Set where
data WrongTypeAdjacencyCreatesTypeIdentity : Set where

factorisationFailureCannotBeSilentlyIgnored : FactorisationFailureMayBeIgnored → ⊥
factorisationFailureCannotBeSilentlyIgnored ()
proofSearchDoesNotCreateTruth : ProofSearchResultCreatesTruth → ⊥
proofSearchDoesNotCreateTruth ()
experimentPlanDoesNotCreateEvidence : ExperimentPlanCreatesEvidence → ⊥
experimentPlanDoesNotCreateEvidence ()
humourSurfaceDoesNotCreateSpeakerIntent : HumourSurfaceCreatesSpeakerIntent → ⊥
humourSurfaceDoesNotCreateSpeakerIntent ()
wrongTypeAdjacencyDoesNotCreateIdentity : WrongTypeAdjacencyCreatesTypeIdentity → ⊥
wrongTypeAdjacencyDoesNotCreateIdentity ()

record SnowballDiscoveryBoundary : Set where
  constructor snowball-discovery-boundary
  field
    relevanceCanBeDiscoveredDynamically : Bool
    discoveryRoutesAreOpenEnded : Bool
    admissionIsConsumerIndexed : Bool
    nonFactorabilityCanForceAxisRepair : Bool
    experimentalDesignCanTargetMissingAxisEvidence : Bool
    admissibilityCanRejectCandidateAxis : Bool
    wrongTypeFallacyHumourCanActAsDiagnostics : Bool
    currentAxisVocabularyClaimedComplete : Bool
open SnowballDiscoveryBoundary public

canonicalSnowballDiscoveryBoundary : SnowballDiscoveryBoundary
canonicalSnowballDiscoveryBoundary = snowball-discovery-boundary
  true true true true true true true false
