module DASHI.Physics.Chemistry.AtomicPeriodicTable369ChronologyStatusExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Chronology + mechanical-status ledger for the atomic / periodic-table lane.
--
-- This module deliberately separates:
--   * source-object chronology,
--   * repository implementation chronology,
--   * publication/manuscript chronology,
--   * proof-assistant checking,
--   * executed computational regressions,
--   * mathematically plausible but unpaid physical interpretations.
--
-- Dates are ISO strings so this remains a lightweight provenance owner rather
-- than importing a time library merely to order a small historical ledger.

data ChronologyClass : Set where
  historicalSourceObject : ChronologyClass
  directRepoImplementation : ChronologyClass
  directRepoStrengthening : ChronologyClass
  paperManuscript : ChronologyClass
  crossAssistantMirror : ChronologyClass

record ChronologyReceipt : Set where
  constructor chronologyReceipt
  field
    chronologyClass : ChronologyClass
    date : String
    object : String
    locator : String
    interpretation : String

open ChronologyReceipt public

archiveVisibleDateReceipt : ChronologyReceipt
archiveVisibleDateReceipt =
  chronologyReceipt
    historicalSourceObject
    "2026-01-12?"
    "DASHI Atom conversation object"
    "attached PDF pages visibly render 12/1/26; locale/original-publication identity not independently paid here"
    "earliest attached source-object date cue only; question mark is intentional"

firstDirectRepoAtomicImplementation : ChronologyReceipt
firstDirectRepoAtomicImplementation =
  chronologyReceipt
    directRepoImplementation
    "2026-04-30T21:51:43+10:00"
    "atom/chemistry recovery carrier + closed-shell/shell-filling strengthening tranche"
    "dashi_agda commit 42e1d740141b0e9e1ca717ae5df79d6e31546c07"
    "earliest direct atomic/chemistry implementation commit located in the current archaeology pass"

atomicGenerationPipelineFollowup : ChronologyReceipt
atomicGenerationPipelineFollowup =
  chronologyReceipt
    directRepoStrengthening
    "2026-05-03"
    "explicit atomic generation pipeline"
    "dashi_agda commit history: Add explicit atomic generation pipeline; followed by Thread chemistry into the atomic generation pipeline"
    "direct generative-constructor strengthening after the first recovery carrier"

currentGenerativeConsolidation : ChronologyReceipt
currentGenerativeConsolidation =
  chronologyReceipt
    paperManuscript
    "2026-09-11"
    "369 generative atomic / periodic-table formalism"
    "dashi_agda PR #886"
    "first repo-contained manuscript/formal consolidation located specifically for this reconstructed atomic constructor; not asserted to be the first external publication"

lean369MirrorReceipt : ChronologyReceipt
lean369MirrorReceipt =
  chronologyReceipt
    crossAssistantMirror
    "2026-06-14 or earlier upstream lineage; exact file-introduction commit not paid here"
    "AgdaMirror/Base369.lean"
    "chboishabba/dashi_lean4; fork created 2026-06-14, upstream repository created 2026-03-22"
    "Lean mirror explicitly describes Base369 as genuine and fully proved; this receipt does not imply the atomic constructor itself has been mirrored to Lean"

------------------------------------------------------------------------
-- Mechanical status must not be inferred from suggestive mathematical prose.

data MechanicalStatus : Set where
  sourcePresentNotCheckedThisSession : MechanicalStatus
  historicalRunReportedArtifactMissing : MechanicalStatus
  proofSourceSaysFullyProvedBuildReceiptMissing : MechanicalStatus
  currentPRAuthoredPendingTypecheck : MechanicalStatus
  formalInterfaceOnly : MechanicalStatus
  executedAndReproduced : MechanicalStatus
  typechecked : MechanicalStatus

record MechanicalReceipt : Set where
  constructor mechanicalReceipt
  field
    status : MechanicalStatus
    object : String
    evidence : String
    nonClaim : String

open MechanicalReceipt public

historicalPythonRunStatus : MechanicalReceipt
historicalPythonRunStatus =
  mechanicalReceipt
    historicalRunReportedArtifactMissing
    "historical MDL / exclusion filling regression"
    "attached DASHI Atom archive reports programmatic filling, first 15+ elements, and closure coordinates Z=2,10,18"
    "original script, exact parameter schedule, executable receipt, and artifact hash have not yet been located"

existingAgdaOwnerStatus : MechanicalReceipt
existingAgdaOwnerStatus =
  mechanicalReceipt
    sourcePresentNotCheckedThisSession
    "pre-existing atomic/369 theorem owners on master"
    "repo contains exact Agda definitions/theorem terms and the aggregate policy says green means agda -i . DASHI/Everything.agda passes"
    "this archaeology session has not independently run Agda; the execution environment available here has no Agda binary"

currentPRAgdaStatus : MechanicalReceipt
currentPRAgdaStatus =
  mechanicalReceipt
    currentPRAuthoredPendingTypecheck
    "PR #886 atomic formalism modules"
    "three Agda owners plus focused validation root are present on the PR branch"
    "no PR workflow run was available at the checked head and no local Agda binary was available, so typechecking must not be claimed yet"

leanBase369Status : MechanicalReceipt
leanBase369Status =
  mechanicalReceipt
    proofSourceSaysFullyProvedBuildReceiptMissing
    "chboishabba/dashi_lean4/AgdaMirror/Base369.lean"
    "Lean source contains explicit theorem proofs for ternary/hexadic/nonary spin/XOR laws and describes itself as genuine, fully proved"
    "the repository has a lean-action workflow file, but no workflow runs/status checks were returned for the inspected main head; this session did not independently rebuild Mathlib/Lean"

physicalPeriodicTableStatus : MechanicalReceipt
physicalPeriodicTableStatus =
  mechanicalReceipt
    formalInterfaceOnly
    "full empirical periodic-table recovery"
    "typed recovery boundaries exist for spectra, shell structure, recurrence, nuclear stability, calibration and observables"
    "the interfaces do not constitute empirical spectra, ionisation energies, bonding, nuclear-stability prediction, or a completed physical periodic-table theorem"

------------------------------------------------------------------------
-- Publication identity is fail-closed.  A commit/manuscript date is not an
-- external publication date unless a publication receipt (DOI/arXiv/Zenodo/etc.)
-- is attached for this same atomic manuscript.

record PublicationDiscipline : Set where
  constructor publicationDiscipline
  field
    repoCommitEqualsExternalPublication : Bool
    repoCommitEqualsExternalPublicationIsFalse :
      repoCommitEqualsExternalPublication ≡ false
    manuscriptPresenceEqualsPeerReview : Bool
    manuscriptPresenceEqualsPeerReviewIsFalse :
      manuscriptPresenceEqualsPeerReview ≡ false
    historicalConversationDateEqualsPublicationDate : Bool
    historicalConversationDateEqualsPublicationDateIsFalse :
      historicalConversationDateEqualsPublicationDate ≡ false

canonicalPublicationDiscipline : PublicationDiscipline
canonicalPublicationDiscipline =
  publicationDiscipline false refl false refl false refl
