module DASHI.Wikimedia.IbrahimMonster3BCharacterExecutionCutsetSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimMonsterCharacterDeterminationMathlibProducerSnowballExact as Mathlib
import DASHI.Wikimedia.IbrahimMonster3BReplayStatusMultiplicitySplitSnowballExact as Replay
import DASHI.Moonshine.Monster3BActualKernelCharacterPromotionExact as Kernel
import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannMultiplicityExact as Multiplicity
import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannUniquenessBidiExact as Uniqueness
import DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact as Action

------------------------------------------------------------------------
-- MONSTER 3B CHARACTER / EXECUTION CUTSET
--
-- The current proof search has two independent producer gates before actual
-- W_zeta recognition can be promoted:
--
--   A. actual MN3B / kernel-character certificate replay;
--   B. generic equal-character -> equivariant-isomorphism theorem KERNEL
--      execution and explicit cross-prover transport.
--
-- The Lean source for gate B is now merged to dashi_lean4 main.  That removes
-- source authoring from the cutset but does not pay a kernel receipt: GitHub
-- reports no workflow run for the exact reconciliation merge SHA.
------------------------------------------------------------------------

record LeanCharacterExecutionReceipt : Set where
  constructor lean-character-execution-receipt
  field
    repository : String
    projectName : String
    branch : String
    pullRequest : String
    branchHeadCommit : String
    mergeCommit : String
    mathlibRevision : String
    sourceFile : String
    regressionFile : String
    theoremName : String
    sourceWritten : Bool
    sourceImportedByDefaultTarget : Bool
    pullRequestOpen : Bool
    sourceMergedToMain : Bool
    workflowAdvertisedForPullRequests : Bool
    workflowRunObservedForHead : Bool
    kernelSuccessObserved : Bool
open LeanCharacterExecutionReceipt public

currentLeanCharacterExecutionReceipt : LeanCharacterExecutionReceipt
currentLeanCharacterExecutionReceipt = lean-character-execution-receipt
  "chboishabba/dashi_lean4"
  "RequestProject"
  "agent/monster-character-determination-mathlib"
  "https://github.com/chboishabba/dashi_lean4/pull/1"
  "751d58de09bcb37d1b1f3dbac2511f6cb362da5e"
  "ff0b3a02fb4e3581b3518fb2abfe381a5b36e1cd"
  "v4.28.0"
  "Synthesis/MonsterCharacterDetermination.lean"
  "Synthesis/MonsterCharacterMultiplicityRegression.lean"
  "Synthesis.nonempty_iso_of_character_eq"
  true true false true true false false

------------------------------------------------------------------------
-- The pinned execution environment is stronger evidence than a floating
-- current-master lookup.  Current mathlib master remains a compatibility
-- observation only; RequestProject is pinned to v4.28.0.
------------------------------------------------------------------------

record MathlibExecutionPinCorrection : Set where
  constructor mathlib-execution-pin-correction
  field
    externalProducerLocatedOnCurrentMathlib : Bool
    requestProjectPinsMathlibVersion : String
    pinnedVersionContainsCharOrthonormal : Bool
    floatingMasterCommitIsExecutionRevision : Bool
    theoremSourceAuthor : String
    literatureDOI : String
    codeArtifactDOI : String
    codeArtifactDOIResolved : Bool
open MathlibExecutionPinCorrection public

canonicalMathlibExecutionPinCorrection : MathlibExecutionPinCorrection
canonicalMathlibExecutionPinCorrection = mathlib-execution-pin-correction
  true
  "v4.28.0"
  true
  false
  "Antoine Labelle"
  "10.1007/978-1-4684-9458-7"
  "unresolved / not asserted"
  false

------------------------------------------------------------------------
-- Actual-kernel gate.  The source owners and producer exist, but the current
-- repo status explicitly says the actual character certificate is not yet
-- observed.  Do not substitute source-backed character identities or a
-- generated-certificate recipe for this execution receipt.
------------------------------------------------------------------------

kernelPromotionStatus : Kernel.ActualKernelPromotionStatus
kernelPromotionStatus = Kernel.canonicalActualKernelPromotionStatus

replayStatus : Replay.ReplayMultiplicityFrontier
replayStatus = Replay.currentReplayMultiplicityFrontier

------------------------------------------------------------------------
-- Constituent recognition gate.  The existing multiplicity theorem only
-- counts a literal finite list AFTER each constituent has already been given
-- selected central character, irreducibility, and Stone-von Neumann degree.
------------------------------------------------------------------------

record ConstituentRecognitionBoundary : Set where
  constructor constituent-recognition-boundary
  field
    wholeActualCharacterCanBeComparedToNinetyModelCopies : Bool
    literalConstituentListInterfaceExists : Bool
    constituentListInterfaceConstructsDecomposition : Bool
    eachConstituentClassificationRequiredUpstream : Bool
    genericIrreducibleCharacterIsoConsumerExists : Bool
    leanWrapperSourceExists : Bool
    leanWrapperSourceMerged : Bool
    leanWrapperKernelPaid : Bool
    agdaCrossProverTransportPaid : Bool
open ConstituentRecognitionBoundary public

canonicalConstituentRecognitionBoundary : ConstituentRecognitionBoundary
canonicalConstituentRecognitionBoundary = constituent-recognition-boundary
  true true false true true true true false false

------------------------------------------------------------------------
-- Ordered proof cutset.
------------------------------------------------------------------------

data CharacterRecognitionLeaf : Set where
  actualKernelReplay : CharacterRecognitionLeaf
  leanEqualCharacterKernelExecution : CharacterRecognitionLeaf
  agdaCharacterTheoremTransport : CharacterRecognitionLeaf
  actualIrreducibleConstituentAttachment : CharacterRecognitionLeaf
  actualZetaSectorRecognition : CharacterRecognitionLeaf
  actualMultiplicityInertiaAction : CharacterRecognitionLeaf
  actualTwelveSeventyEightSplit : CharacterRecognitionLeaf


data LeafState : Set where
  closed sourceMerged waiting blocked : LeafState

leafState : CharacterRecognitionLeaf → LeafState
leafState actualKernelReplay = waiting
leafState leanEqualCharacterKernelExecution = sourceMerged
leafState agdaCharacterTheoremTransport = blocked
leafState actualIrreducibleConstituentAttachment = blocked
leafState actualZetaSectorRecognition = blocked
leafState actualMultiplicityInertiaAction = blocked
leafState actualTwelveSeventyEightSplit = blocked

highestAlphaExecutableLeaf : CharacterRecognitionLeaf
highestAlphaExecutableLeaf = actualKernelReplay

parallelExecutableLeaf : CharacterRecognitionLeaf
parallelExecutableLeaf = leanEqualCharacterKernelExecution

------------------------------------------------------------------------
-- Attribution coordinates. OEIS is a numerical-family/discovery coordinate,
-- not a character-determination theorem or actual-action witness.
------------------------------------------------------------------------

record CutsetAttributionCoordinates : Set where
  constructor cutset-attribution-coordinates
  field
    serreDOI : String
    barracloughWilsonDOI : String
    wilsonConstructionDOI : String
    groupRepresentationQid : String
    representationCharacterQid : String
    maschkeQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    multiplicityNinetyOEIS : String
    oeisPaysCharacterIso : Bool
    oeisPaysActualAction : Bool
open CutsetAttributionCoordinates public

canonicalCutsetAttributionCoordinates : CutsetAttributionCoordinates
canonicalCutsetAttributionCoordinates = cutset-attribution-coordinates
  "10.1007/978-1-4684-9458-7"
  "10.1112/S1461157000001352"
  "10.1515/jgth.1998.023"
  "Q1055807"
  "Q600043"
  "Q656198"
  "512.22"
  "512.23"
  "A005052"
  false false

------------------------------------------------------------------------
-- WrongType boundaries.
------------------------------------------------------------------------

data MergedLeanSourceCreatesKernelReceipt : Set where
data KernelCharacterEqualityCreatesConstituentList : Set where
data NinetyOEISEqualityCreatesMultiplicityAction : Set where
data AgdaConsumerRecordCreatesExternalTheorem : Set where

mergedLeanSourceDoesNotCreateReceipt : MergedLeanSourceCreatesKernelReceipt → ⊥
mergedLeanSourceDoesNotCreateReceipt ()

characterEqualityDoesNotCreateConstituentList :
  KernelCharacterEqualityCreatesConstituentList → ⊥
characterEqualityDoesNotCreateConstituentList ()

oeisDoesNotCreateMultiplicityAction :
  NinetyOEISEqualityCreatesMultiplicityAction → ⊥
oeisDoesNotCreateMultiplicityAction ()

agdaConsumerDoesNotCreateExternalTheorem :
  AgdaConsumerRecordCreatesExternalTheorem → ⊥
agdaConsumerDoesNotCreateExternalTheorem ()

------------------------------------------------------------------------
-- Canonical frontier.
------------------------------------------------------------------------

record Monster3BCharacterExecutionFrontier : Set where
  constructor monster3b-character-execution-frontier
  field
    mathlibPinnedProducerFound : Bool
    leanWrapperSourceWritten : Bool
    leanWrapperInDefaultBuildTarget : Bool
    leanWrapperMergedToMain : Bool
    leanWrapperKernelReceiptPaid : Bool
    actualKernelReplayRecipeExists : Bool
    actualKernelReplayReceiptPaid : Bool
    wholeCharacterNinetyFoldIdentityCompilerExists : Bool
    constituentRecognitionAutomaticallyFollows : Bool
    agdaCharacterTransportPaid : Bool
    actualZetaRecognitionPaid : Bool
    actualMultiplicityActionPaid : Bool
    actualTwelveSeventyEightSplitPaid : Bool
    nextResidual : String
open Monster3BCharacterExecutionFrontier public

currentMonster3BCharacterExecutionFrontier : Monster3BCharacterExecutionFrontier
currentMonster3BCharacterExecutionFrontier = monster3b-character-execution-frontier
  true true true true false
  true false true false
  false false false false
  "observe the two remaining execution receipts without changing theorem architecture: (1) the current MN3B AtlasRep/CTblLib/generated-certificate replay, and (2) a Lean kernel execution of the exact merged dashi_lean4 theorem source at ff0b3a02fb4e3581b3518fb2abfe381a5b36e1cd under RequestProject/mathlib v4.28.0. Then transport only that theorem into Agda and attach the SAME actual irreducible E-constituents. Do not infer a constituent list from 65610 = 90*729, and do not let A005052(2)=90 manufacture the multiplicity action."
