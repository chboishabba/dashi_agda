module DASHI.Interop.SensibLawNatZelphPeerCohortExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Interop.ExternalContextSafetyBoundary as Safety
import DASHI.Interop.GovernedResidualOntologyLearning as Learning
import DASHI.Interop.ZelphBoundedGraphCoverageExact as Zelph
import DASHI.Interop.SensibLawWikidataItemPropertyEvidenceExact as ItemEvidence

------------------------------------------------------------------------
-- Nat P5991 -> P14143 peer-cohort residual.
--
-- Runtime parity:
--   ItemPropertyEvidenceSurface + DomainInvariantSnapshot
--     -> conditioned peer-cohort residual.
--
-- The item surface retains actual property inventory, property-family coverage,
-- statement GUID/rank/visibility, qualifier/scope receipts and asserted/derived
-- relation origin before cohort comparison occurs.
------------------------------------------------------------------------

data PeerResidualState : Set where
  peerExact peerPartial peerContradictory peerUnresolved : PeerResidualState

data PeerComparisonStatus : Set where
  peerAdmissible peerMasked peerUnknown peerInadmissible : PeerComparisonStatus

record NatItemPeerInput : Set where
  constructor nat-item-peer-input
  field
    candidateReference : String
    itemEvidence : ItemEvidence.ItemPropertyEvidenceSurface
    domainInvariantReference : String
    trustedCohortReference : String
    trustedMemberCountReference : String
open NatItemPeerInput public

record NatPeerCohortAssessment : Set where
  constructor nat-peer-cohort-assessment
  field
    candidateReference : String
    sourceRevisionReference : String
    itemEvidenceReference : String
    domainInvariantReference : String
    graphCoverage : Zelph.QueryCoverageReceipt
    trustedCohortReference : String
    trustedMemberCountReference : String
    comparisonStatus : PeerComparisonStatus
    residualState : PeerResidualState
    residualEvidenceReference : String
    authorityIsDiagnosticOnly : Bool
    authorityIsDiagnosticOnlyIsTrue : authorityIsDiagnosticOnly ≡ true
    promotionEvaluated : Bool
    promotionEvaluatedIsFalse : promotionEvaluated ≡ false
    editEffect : Bool
    editEffectIsFalse : editEffect ≡ false
open NatPeerCohortAssessment public

peerStateForCoverage :
  Zelph.QueryCoverageStatus →
  PeerResidualState
peerStateForCoverage Zelph.queryCoverageComplete = peerPartial
peerStateForCoverage Zelph.queryCoverageIncomplete = peerUnresolved
peerStateForCoverage Zelph.queryCoverageInvalid = peerUnresolved

incompleteCoverageKeepsPeerUnresolved :
  peerStateForCoverage Zelph.queryCoverageIncomplete ≡ peerUnresolved
incompleteCoverageKeepsPeerUnresolved = refl

invalidCoverageKeepsPeerUnresolved :
  peerStateForCoverage Zelph.queryCoverageInvalid ≡ peerUnresolved
invalidCoverageKeepsPeerUnresolved = refl

------------------------------------------------------------------------
-- Governed cohort admission is inherited from the generic learning owner.
------------------------------------------------------------------------

heldMemberDoesNotTrainNatInvariant :
  Learning.contributesToEmpiricalInvariant Learning.held ≡ false
heldMemberDoesNotTrainNatInvariant = Learning.heldDoesNotTrainInvariant

unresolvedMemberDoesNotTrainNatInvariant :
  Learning.contributesToEmpiricalInvariant Learning.unresolved ≡ false
unresolvedMemberDoesNotTrainNatInvariant = Learning.unresolvedDoesNotTrainInvariant

coverageIncompleteMemberDoesNotTrainNatInvariant :
  Learning.contributesToEmpiricalInvariant Learning.coverageIncomplete ≡ false
coverageIncompleteMemberDoesNotTrainNatInvariant =
  Learning.coverageIncompleteDoesNotTrainInvariant

------------------------------------------------------------------------
-- Item/property provenance cannot be discarded before peer comparison.
------------------------------------------------------------------------

data FlattenedPeerLabelsReplaceItemEvidence : Set where
data ExactPeerResidualImpliesMigrationSafe : Set where
data ExactPeerResidualImpliesP5991EqualsP14143 : Set where
data CohortMajorityCreatesPolicyAuthority : Set where
data ExternalGraphIdentityCreatesNatRole : Set where

flattenedPeerLabelsDoNotReplaceItemEvidence :
  FlattenedPeerLabelsReplaceItemEvidence → ⊥
flattenedPeerLabelsDoNotReplaceItemEvidence ()

exactPeerResidualDoesNotProveMigrationSafety :
  ExactPeerResidualImpliesMigrationSafe → ⊥
exactPeerResidualDoesNotProveMigrationSafety ()

exactPeerResidualDoesNotEquateProperties :
  ExactPeerResidualImpliesP5991EqualsP14143 → ⊥
exactPeerResidualDoesNotEquateProperties ()

cohortMajorityDoesNotCreatePolicyAuthority :
  CohortMajorityCreatesPolicyAuthority → ⊥
cohortMajorityDoesNotCreatePolicyAuthority ()

externalGraphIdentityDoesNotCreateNatRole :
  ExternalGraphIdentityCreatesNatRole → ⊥
externalGraphIdentityDoesNotCreateNatRole ()

record NatPeerCohortBoundary : Set where
  constructor nat-peer-cohort-boundary
  field
    itemEvidencePrecedesPeerComparison : Bool
    propertyConditionsPreservedIntoPeerFeatures : Bool
    incompleteCoverageKeepsResidualUnresolved : Bool
    trustedMembersRequireGovernedAdmission : Bool
    flattenedLabelsReplaceItemEvidence : Bool
    exactResidualCreatesMigrationSafety : Bool
    exactResidualEquatesSourceAndTargetProperty : Bool
    cohortMajorityCreatesPolicy : Bool
    peerAssessmentCreatesEdit : Bool

canonicalNatPeerCohortBoundary : NatPeerCohortBoundary
canonicalNatPeerCohortBoundary =
  nat-peer-cohort-boundary true true true true false false false false false

natPeerCohortStatement : String
natPeerCohortStatement =
  "Nat peer-cohort comparison consumes revision-bound item/property evidence rather than detached peer labels. Actual property inventory, per-property coverage, statement GUID/rank/visibility, qualifier/scope state and relation origin remain conditioned coordinates. Incomplete coverage remains unresolved; governed reviewed members alone train the empirical invariant. Even exact peer agreement is diagnostic only and does not prove migration safety, equate P5991 with P14143, create policy authority, or edit Wikidata."
