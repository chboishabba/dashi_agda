module DASHI.Physics.Chemistry.AtomicPeriodicTable369ChronologyVerificationExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as G
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ProvenanceSnowballExact as P

------------------------------------------------------------------------
-- Chronology and execution-status owner for the atom / periodic-table lane.
--
-- Dates here are receipts, not mathematical premises.  We distinguish
-- implementation chronology, publication/manuscript chronology, historical
-- source labels, and present verification state so that priority claims do not
-- silently become theorem claims and source presence does not silently become
-- compiler success.

data DatePrecision : Set where
  exactTimestamp : DatePrecision
  exactDate : DatePrecision
  sourceLabelAmbiguous : DatePrecision
  dateNotLocated : DatePrecision

data EventKind : Set where
  repositoryImplementation : EventKind
  formalTheoremOwner : EventKind
  manuscriptPublication : EventKind
  historicalConversationSource : EventKind
  currentPullRequest : EventKind

record ChronologyReceipt : Set where
  constructor chronologyReceipt
  field
    event : String
    when : String
    precision : DatePrecision
    kind : EventKind
    repositoryOrSource : String
    locator : String
    significance : String

open ChronologyReceipt public

------------------------------------------------------------------------
-- Earliest clean implementation receipts found in the current archaeology.

firstLocatedAtomicCode : ChronologyReceipt
firstLocatedAtomicCode =
  chronologyReceipt
    "spectral-line atomic tooling and smoke tests"
    "2025-11-11T02:31:02Z"
    exactTimestamp
    repositoryImplementation
    "chboishabba/dashifine"
    "commit 4f1441e4989beec157733a960ca7dfc47a2bf3ee; newtest/element_lines.py"
    "earliest clean repo-side atomic implementation located in this audit; atomic/spectral tooling, not yet the 369 periodic-table theorem"

firstBase369AgdaCarrier : ChronologyReceipt
firstBase369AgdaCarrier =
  chronologyReceipt
    "Base369 ternary / hexadic / nonary algebra present at repository inception"
    "2026-02-16T11:20:02Z"
    exactTimestamp
    formalTheoremOwner
    "chboishabba/dashi_agda"
    "init commit 65266f7edc1ec7bb52e59ee020209cc5cb0eecec; Base369.agda blob 8dc130c5af5a28580f729a57ea9e8ba610c0e9ad"
    "earliest exact 369 substrate implementation located in dashi_agda: spin, 3/6/9 cyclic carriers, rotation-order and identity laws, and ternary associativity"

firstLocatedProjectionPhysicsProgramme : ChronologyReceipt
firstLocatedProjectionPhysicsProgramme =
  chronologyReceipt
    "projection / effective-manifold physics targets"
    "2026-03-06T02:37:41Z"
    exactTimestamp
    repositoryImplementation
    "chboishabba/dashiQ"
    "commit 47071bed2cbe853c76fb5bec7d65f3a8b73b14bc; PHYSICS_TARGETS.md"
    "explicit pre-atomic programme placing effective physical structure downstream of projection/geometry"

firstLocatedAtomicClosureOwner : ChronologyReceipt
firstLocatedAtomicClosureOwner =
  chronologyReceipt
    "atom/chemistry recovery carrier with closed-shell and shell-filling strengthening"
    "2026-04-30T11:51:43Z"
    exactTimestamp
    formalTheoremOwner
    "chboishabba/dashi_agda"
    "commit 42e1d740141b0e9e1ca717ae5df79d6e31546c07"
    "earliest located repo-native formal atom/chemistry closure milestone in this audit; explicitly staged rather than a finished physical chemistry theorem"

firstLeanBase369ProofSource : ChronologyReceipt
firstLeanBase369ProofSource =
  chronologyReceipt
    "Lean Base369 mirror introduced as a proof source"
    "2026-07-07T03:47:18Z"
    exactTimestamp
    formalTheoremOwner
    "chboishabba/dashi_lean4"
    "commit 55132524c2e132c0b86c17eeb60d7e39c3af08b6; Base369.lean added in that commit"
    "independent proof-assistant transcription of the 3/6/9 substrate; commit diff adds the file from zero lines and labels it genuine, fully proved"

leanBase369PathReorganization : ChronologyReceipt
leanBase369PathReorganization =
  chronologyReceipt
    "Lean Base369 mirror moved under AgdaMirror"
    "2026-08-12T01:33:28Z"
    exactTimestamp
    repositoryImplementation
    "chboishabba/dashi_lean4"
    "commit 72734285fd83387837e0025eb51a93b63629a0b9; Base369.lean -> AgdaMirror/Base369.lean"
    "path/repository organization receipt only; not the first Lean implementation date"

firstLocatedExplicitPeriodicRecoveryBoundary : ChronologyReceipt
firstLocatedExplicitPeriodicRecoveryBoundary =
  chronologyReceipt
    "explicit atomic periodic-table recovery boundary"
    "2026-07-19T11:39:45Z"
    exactTimestamp
    formalTheoremOwner
    "chboishabba/dashi_agda"
    "commit 554e8f930dfee5293d75d3bb67be8098bde088d3; PR #101"
    "explicit periodic-table recovery owner with shell recurrence and atomic-to-biological recovery tower"

restoredGenerativeShellOwner : ChronologyReceipt
restoredGenerativeShellOwner =
  chronologyReceipt
    "restored exact atomic fermion shell formalism"
    "2026-08-06T03:49:20Z"
    exactTimestamp
    formalTheoremOwner
    "chboishabba/dashi_agda"
    "commit fae9d36f393a173359973ef37c529f332cc644bb"
    "current exact shell/capacity owner restored atop PR 399; restoration date is not asserted to be conception date"

restoredAtomicGenerationPipeline : ChronologyReceipt
restoredAtomicGenerationPipeline =
  chronologyReceipt
    "restored atomic generation pipeline"
    "2026-08-06T03:49:56Z"
    exactTimestamp
    formalTheoremOwner
    "chboishabba/dashi_agda"
    "commit 49000ac7f1ddbf008b27b405cf0768eef32ece2a"
    "current staged nuclear-to-valence generation owner; restoration date is not asserted to be conception date"

historicalAtomExportDateLabel : ChronologyReceipt
historicalAtomExportDateLabel =
  chronologyReceipt
    "DASHI Atom exported conversation source"
    "printed page label 12/1/26; interpretation not normalized here"
    sourceLabelAmbiguous
    historicalConversationSource
    "attached DASHI Atom export"
    "DASHI Atom(20260911-021928).pdf"
    "historical provenance for MDL filling / kernel-exhaustion discussion; the printed date label is retained literally because locale/order is ambiguous"

currentFormalismPR : ChronologyReceipt
currentFormalismPR =
  chronologyReceipt
    "canonical 369 generative atom / periodic-table composition"
    "2026-09-11T02:39:19Z"
    exactTimestamp
    currentPullRequest
    "chboishabba/dashi_agda"
    "draft PR #886"
    "current composition, provenance, verification, attribution, and paper surface"

------------------------------------------------------------------------
-- Verification status is intentionally separate from mathematical status.

data VerificationStatus : Set where
  sourceInspected : VerificationStatus
  historicalRunReported : VerificationStatus
  compilerReceiptFromRepository : VerificationStatus
  proofTermsInspectedBuildNotRerun : VerificationStatus
  renderedThisWorkSession : VerificationStatus
  sourcePresentNotCompilerCheckedThisSession : VerificationStatus
  mathematicalInterfaceOnly : VerificationStatus
  verificationNotLocated : VerificationStatus

record VerificationReceipt : Set where
  constructor verificationReceipt
  field
    subject : String
    status : VerificationStatus
    evidence : String
    boundary : String

open VerificationReceipt public

historicalPythonFillingVerification : VerificationReceipt
historicalPythonFillingVerification =
  verificationReceipt
    "historical MDL filling experiment"
    historicalRunReported
    "DASHI Atom archive reports a programmatic run and closure coordinates Z=2,10,18"
    "original Python artifact/hash has not yet been located or rerun in this PR"

currentAgdaSourceVerification : VerificationReceipt
currentAgdaSourceVerification =
  verificationReceipt
    "PR #886 atomic 369 Agda owners"
    sourcePresentNotCompilerCheckedThisSession
    "source committed on agent/atomic-periodic-table-369-formalism with focused validation root"
    "the current execution environment did not provide an Agda executable and no PR workflow run was returned at the inspected head; source presence is not recorded as a successful typecheck"

existingPeriodicBoundaryVerification : VerificationReceipt
existingPeriodicBoundaryVerification =
  verificationReceipt
    "existing AtomicPeriodicTableRecoveryBoundary owner"
    compilerReceiptFromRepository
    "landed in PR #101 together with a focused biology-recovery Agda workflow definition"
    "workflow definition/source presence is not silently upgraded into a run result; an exact historical successful workflow-run receipt remains separately checkable"

leanBase369Verification : VerificationReceipt
leanBase369Verification =
  verificationReceipt
    "chboishabba/dashi_lean4 Base369 proof source"
    proofTermsInspectedBuildNotRerun
    "commit 55132524c2e132c0b86c17eeb60d7e39c3af08b6 adds Base369.lean from zero lines; the source contains explicit theorem proofs by cases/rfl and the aggregate classifies Base369 as genuine, fully proved"
    "this session inspected proof terms and commit provenance but did not independently execute lake build, so no fresh Lean build receipt is claimed"

latexPaperVerification : VerificationReceipt
latexPaperVerification =
  verificationReceipt
    "AtomicPeriodicTable369Formalism TeX/PDF"
    renderedThisWorkSession
    "LaTeX source compiled to PDF and page renders were inspected before repository insertion"
    "rendering validates the document artifact, not the proof-assistant status or physical truth of the mathematical interpretation"

fullPhysicalRecoveryVerification : VerificationReceipt
fullPhysicalRecoveryVerification =
  verificationReceipt
    "full empirical periodic-table recovery"
    mathematicalInterfaceOnly
    "typed recovery contract exists for spectra, shell structure, valence recurrence, nuclear stability, scale and observables"
    "the contract is not itself evidence that those physical obligations have all been discharged"

------------------------------------------------------------------------
-- Non-collapse rules for external presentation.

record VerificationDiscipline : Set where
  constructor verificationDiscipline
  field
    sourcePresenceImpliesTypecheck : Bool
    sourcePresenceImpliesTypecheckIsFalse : sourcePresenceImpliesTypecheck ≡ false

    historicalReportedRunEqualsRerun : Bool
    historicalReportedRunEqualsRerunIsFalse : historicalReportedRunEqualsRerun ≡ false

    latexRenderEqualsAgdaTypecheck : Bool
    latexRenderEqualsAgdaTypecheckIsFalse : latexRenderEqualsAgdaTypecheck ≡ false

    structuralTheoremEqualsEmpiricalRecovery : Bool
    structuralTheoremEqualsEmpiricalRecoveryIsFalse : structuralTheoremEqualsEmpiricalRecovery ≡ false

canonicalVerificationDiscipline : VerificationDiscipline
canonicalVerificationDiscipline =
  verificationDiscipline false refl false refl false refl false refl

------------------------------------------------------------------------
-- Dashboard consumed by the paper/PR narrative.

record ChronologyVerificationDashboard : Set₁ where
  field
    formalism : Set₁
    formalismIs : formalism ≡ G.CanonicalAtomicPeriodicTableStatement
    provenance : P.ProvenanceDashboard
    firstAtomicImplementation : ChronologyReceipt
    first369Implementation : ChronologyReceipt
    firstFormalAtomicClosure : ChronologyReceipt
    firstLean369ProofSource : ChronologyReceipt
    explicitPeriodicBoundary : ChronologyReceipt
    currentPR : ChronologyReceipt
    currentAgdaVerification : VerificationReceipt
    historicalRunVerification : VerificationReceipt
    lean369Verification : VerificationReceipt
    paperVerification : VerificationReceipt
    discipline : VerificationDiscipline

canonicalChronologyVerificationDashboard : ChronologyVerificationDashboard
canonicalChronologyVerificationDashboard =
  record
    { formalism = G.CanonicalAtomicPeriodicTableStatement
    ; formalismIs = refl
    ; provenance = P.canonicalProvenanceDashboard
    ; firstAtomicImplementation = firstLocatedAtomicCode
    ; first369Implementation = firstBase369AgdaCarrier
    ; firstFormalAtomicClosure = firstLocatedAtomicClosureOwner
    ; firstLean369ProofSource = firstLeanBase369ProofSource
    ; explicitPeriodicBoundary = firstLocatedExplicitPeriodicRecoveryBoundary
    ; currentPR = currentFormalismPR
    ; currentAgdaVerification = currentAgdaSourceVerification
    ; historicalRunVerification = historicalPythonFillingVerification
    ; lean369Verification = leanBase369Verification
    ; paperVerification = latexPaperVerification
    ; discipline = canonicalVerificationDiscipline
    }
