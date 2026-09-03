module DASHI.Core.EvidenceAcquisitionSelectiveReopeningExact where

------------------------------------------------------------------------
-- EVIDENCE ACQUISITION / SELECTIVE REOPENING CORE
--
-- Cross-pollinates EvidenceHyperfabricExact with ActiveObligationEvidenceFibre,
-- AssumptionIndexedReopeningExact, AffectedDependencyClosureExact, and
-- proof-search least-privilege discipline.
--
-- Central law:
--   notLocated  -> open targeted acquisition obligation
--   present     -> acquisition branch satisfied/closed
--   knownAbsent -> acquisition branch closed as absent
--
-- `knownAbsent` closes only the acquisition branch for that exact record.  It
-- is not a refutation of every hypothesis that might have benefited from the
-- record, and it does not fabricate the record itself.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.EvidenceHyperfabricExact as Evidence
import DASHI.Core.AssumptionIndexedReopeningExact as Reopening
import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch

------------------------------------------------------------------------
-- Acquisition targets and branch states.
------------------------------------------------------------------------

data AcquisitionBranchState : Set where
  acquisitionOpen
  acquisitionSatisfied
  acquisitionClosedKnownAbsent
  : AcquisitionBranchState

branchState : Evidence.RecordStatus → AcquisitionBranchState
branchState Evidence.notLocated = acquisitionOpen
branchState Evidence.present = acquisitionSatisfied
branchState Evidence.knownAbsent = acquisitionClosedKnownAbsent

notLocatedOpens :
  branchState Evidence.notLocated ≡ acquisitionOpen
notLocatedOpens = refl

presentSatisfies :
  branchState Evidence.present ≡ acquisitionSatisfied
presentSatisfies = refl

knownAbsentCloses :
  branchState Evidence.knownAbsent ≡ acquisitionClosedKnownAbsent
knownAbsentCloses = refl

------------------------------------------------------------------------
-- A targeted obligation preserves the exact evidence coordinate being sought,
-- the acquisition route, and the authority/admissibility reference needed to
-- obtain it.  Search does not receive permission to invent stronger access.
------------------------------------------------------------------------

record AcquisitionTarget : Set where
  constructor acquisition-target
  field
    targetName : String
    targetDescription : String
    preferredAcquisitionRoute : String
    fallbackAcquisitionRoute : String
    authorityOrAccessReference : String

open AcquisitionTarget public

record AcquisitionObligation (target : AcquisitionTarget) : Set where
  constructor acquisition-obligation
  field
    status : Evidence.RecordStatus
    statusIsNotLocated : status ≡ Evidence.notLocated
    searchReference : String

open AcquisitionObligation public

obligationFromNotLocated :
  (target : AcquisitionTarget) →
  AcquisitionObligation target
obligationFromNotLocated target =
  acquisition-obligation Evidence.notLocated refl
    "targeted acquisition generated from notLocated evidence status"

knownAbsentCannotCarryOpenObligation :
  ∀ {target} →
  (obligation : AcquisitionObligation target) →
  status obligation ≡ Evidence.knownAbsent → ⊥
knownAbsentCannotCarryOpenObligation obligation knownAbsent =
  Evidence.notLocated≠knownAbsent
    (trans (sym (statusIsNotLocated obligation)) knownAbsent)

------------------------------------------------------------------------
-- Acquisition updates are evidence updates, not retroactive truth changes.
------------------------------------------------------------------------

record AcquisitionUpdate (target : AcquisitionTarget) : Set where
  constructor acquisition-update
  field
    beforeStatus : Evidence.RecordStatus
    afterStatus : Evidence.RecordStatus
    updateProvenance : String

open AcquisitionUpdate public

record SatisfiesAcquisition {target : AcquisitionTarget}
    (update : AcquisitionUpdate target) : Set where
  constructor satisfies-acquisition
  field
    beganOpen : beforeStatus update ≡ Evidence.notLocated
    endedPresent : afterStatus update ≡ Evidence.present

open SatisfiesAcquisition public

record ClosesAsKnownAbsent {target : AcquisitionTarget}
    (update : AcquisitionUpdate target) : Set where
  constructor closes-as-known-absent
  field
    beganOpen : beforeStatus update ≡ Evidence.notLocated
    endedKnownAbsent : afterStatus update ≡ Evidence.knownAbsent

open ClosesAsKnownAbsent public

------------------------------------------------------------------------
-- Selective reopening bridge.  A newly acquired record can reopen only those
-- consumers reachable through an explicit dependency path.
------------------------------------------------------------------------

record AcquisitionDependencyGraph (Artifact : Set) : Set₁ where
  constructor acquisition-dependency-graph
  field
    Depends : Artifact → Artifact → Set
    dependencyReference : String

open AcquisitionDependencyGraph public

record SelectiveAcquisitionReopening
    {Artifact : Set}
    (graph : AcquisitionDependencyGraph Artifact)
    (changed target : Artifact) : Set where
  constructor selective-acquisition-reopening
  field
    obligation : Dependency.ReopeningObligation (Depends graph) changed target
    reopeningReference : String

open SelectiveAcquisitionReopening public

oneEdgeAcquisitionReopening :
  ∀ {Artifact}
    {graph : AcquisitionDependencyGraph Artifact}
    {changed target : Artifact} →
  Depends graph changed target →
  SelectiveAcquisitionReopening graph changed target
oneEdgeAcquisitionReopening edge =
  selective-acquisition-reopening
    (Dependency.oneEdgeCreatesReopeningObligation edge)
    "newly acquired evidence reopens exactly dependency-reachable consumer"

------------------------------------------------------------------------
-- Least-privilege proof-search boundary.
------------------------------------------------------------------------

record AcquisitionSearchBoundary : Set where
  constructor acquisition-search-boundary
  field
    notLocatedGeneratesTargetedSearch : Bool
    notLocatedGeneratesTargetedSearchIsTrue :
      notLocatedGeneratesTargetedSearch ≡ true

    knownAbsentKeepsSameAcquisitionBranchOpen : Bool
    knownAbsentKeepsSameAcquisitionBranchOpenIsFalse :
      knownAbsentKeepsSameAcquisitionBranchOpen ≡ false

    knownAbsentRefutesEveryDependentHypothesis : Bool
    knownAbsentRefutesEveryDependentHypothesisIsFalse :
      knownAbsentRefutesEveryDependentHypothesis ≡ false

    acquiredEvidenceReopensUnrelatedConsumers : Bool
    acquiredEvidenceReopensUnrelatedConsumersIsFalse :
      acquiredEvidenceReopensUnrelatedConsumers ≡ false

    acquisitionMayBypassAccessAuthority : Bool
    acquisitionMayBypassAccessAuthorityIsFalse :
      acquisitionMayBypassAccessAuthority ≡ false

    proofSearchMayInventUnavailableRecord : Bool
    proofSearchMayInventUnavailableRecordIsFalse :
      proofSearchMayInventUnavailableRecord ≡ false

canonicalAcquisitionSearchBoundary : AcquisitionSearchBoundary
canonicalAcquisitionSearchBoundary =
  acquisition-search-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
