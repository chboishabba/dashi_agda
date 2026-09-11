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
    "current composition, provenance, verification, and paper surface"

------------------------------------------------------------------------
-- Verification status is intentionally separate from mathematical status.

data VerificationStatus : Set where
  sourceInspected : VerificationStatus
  historicalRunReported : VerificationStatus
  compilerReceiptFromRepository : VerificationStatus
  builtByLeanReceipt : VerificationStatus
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
    "the current execution environment did not provide an Agda executable; source presence is not recorded as a successful typecheck"

existingPeriodicBoundaryVerification : VerificationReceipt
existingPeriodicBoundaryVerification =
  verificationReceipt
    "existing AtomicPeriodicTableRecoveryBoundary owner"
    compilerReceiptFromRepository
    "landed in PR #101 together with a focused biology-recovery Agda check"
    "this chronology receipt records repository evidence; it is not a fresh re-typecheck of that historical commit in this session"

leanAristotleVerification : VerificationReceipt
leanAristotleVerification =
  verificationReceipt
    "chboishabba/dashi_lean4 Aristotle closure tranche"
    builtByLeanReceipt
    "ARISTOTLE_SUMMARY.md records lake build success: 8030 jobs, no errors, no sorry/axiom/implemented_by introduced"
    "located Lean content is YM/NS/spectral closure, not a direct atom/periodic-table formalization"

latexPaperVerification : VerificationReceipt
latexPaperVerification =
  verificationReceipt
    "AtomicPeriodicTable369Formalism TeX/PDF"
    renderedThisWorkSession
    "LaTeX source compiled to PDF and page renders were inspected before repository insertion"
    "rendering validates the document artifact, not the physical truth of every mathematical interpretation"

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
    firstFormalAtomicClosure : ChronologyReceipt
    explicitPeriodicBoundary : ChronologyReceipt
    currentPR : ChronologyReceipt
    currentAgdaVerification : VerificationReceipt
    historicalRunVerification : VerificationReceipt
    paperVerification : VerificationReceipt
    discipline : VerificationDiscipline

canonicalChronologyVerificationDashboard : ChronologyVerificationDashboard
canonicalChronologyVerificationDashboard =
  record
    { formalism = G.CanonicalAtomicPeriodicTableStatement
    ; formalismIs = refl
    ; provenance = P.canonicalProvenanceDashboard
    ; firstAtomicImplementation = firstLocatedAtomicCode
    ; firstFormalAtomicClosure = firstLocatedAtomicClosureOwner
    ; explicitPeriodicBoundary = firstLocatedExplicitPeriodicRecoveryBoundary
    ; currentPR = currentFormalismPR
    ; currentAgdaVerification = currentAgdaSourceVerification
    ; historicalRunVerification = historicalPythonFillingVerification
    ; paperVerification = latexPaperVerification
    ; discipline = canonicalVerificationDiscipline
    }
