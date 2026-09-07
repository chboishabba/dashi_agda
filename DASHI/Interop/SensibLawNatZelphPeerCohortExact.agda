module DASHI.Interop.SensibLawNatZelphPeerCohortExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Interop.ExternalContextSafetyBoundary as Safety
import DASHI.Interop.GovernedResidualOntologyLearning as Learning
import DASHI.Interop.ZelphBoundedGraphCoverageExact as Zelph

------------------------------------------------------------------------
-- Nat P5991 -> P14143 peer-cohort residual.
--
-- Runtime donor: SensibLaw's DomainPressureAssessment currently carries a
-- peer_cohort residual which remains unresolved until independently reviewed
-- conforming members and coverage-qualified graph evidence exist.
------------------------------------------------------------------------

data PeerResidualState : Set where
  peerExact peerPartial peerContradictory peerUnresolved : PeerResidualState

data PeerComparisonStatus : Set where
  peerAdmissible peerMasked peerUnknown peerInadmissible : PeerComparisonStatus

record NatPeerCohortAssessment : Set where
  constructor nat-peer-cohort-assessment
  field
    candidateReference : String
    sourceRevisionReference : String
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
-- Held/unresolved/incomplete members cannot train the empirical invariant.
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
-- Firewalls.
------------------------------------------------------------------------

data ExactPeerResidualImpliesMigrationSafe : Set where
data ExactPeerResidualImpliesP5991EqualsP14143 : Set where
data CohortMajorityCreatesPolicyAuthority : Set where
data ExternalGraphIdentityCreatesNatRole : Set where

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
    incompleteCoverageKeepsResidualUnresolved : Bool
    trustedMembersRequireGovernedAdmission : Bool
    exactResidualCreatesMigrationSafety : Bool
    exactResidualEquatesSourceAndTargetProperty : Bool
    cohortMajorityCreatesPolicy : Bool
    peerAssessmentCreatesEdit : Bool

canonicalNatPeerCohortBoundary : NatPeerCohortBoundary
canonicalNatPeerCohortBoundary =
  nat-peer-cohort-boundary true true false false false false

natPeerCohortStatement : String
natPeerCohortStatement =
  "Nat peer-cohort evidence may become exact, partial or contradictory only after bounded query coverage and governed reviewed-cohort admission. Incomplete/invalid coverage remains unresolved. Even exact peer agreement is diagnostic only: it does not prove migration safety, equate P5991 with P14143, create policy authority, or edit Wikidata."
