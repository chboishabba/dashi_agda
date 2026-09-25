module DASHI.Interop.Round11MachinCrossProverRecognitionExact where

------------------------------------------------------------------------
-- ROUND11 / MACHIN CROSS-PROVER RECOGNITION FIREWALL
--
-- Cross-pollinated from the repository's source-attribution and recognition
-- discipline:
--
--   source fact
--     ≠ repository formal reconstruction
--     ≠ cross-module inference
--     ≠ cross-prover replay observation.
--
-- The route-B mathematics is already closed independently on the Lean side.
-- What remains is recognition of an ACTUAL imported/elaborated Agda binding.
-- Name/hash/table agreement is deliberately not promoted to that claim.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

data ClaimOrigin : Set where
  vendoredExternalDependency : ClaimOrigin
  agdaFormalReconstruction : ClaimOrigin
  leanFormalReconstruction : ClaimOrigin
  repositoryCrossModuleInference : ClaimOrigin
  crossProverReplayObservation : ClaimOrigin
  repositoryNewExtension : ClaimOrigin

bishopRepresentationOrigin : ClaimOrigin
bishopRepresentationOrigin = vendoredExternalDependency

round11MachinSourceReceiptOrigin : ClaimOrigin
round11MachinSourceReceiptOrigin = agdaFormalReconstruction

canonicalLeanBindingOrigin : ClaimOrigin
canonicalLeanBindingOrigin = leanFormalReconstruction

sourceToTargetBindingTableOrigin : ClaimOrigin
sourceToTargetBindingTableOrigin = repositoryCrossModuleInference

genuineReplayObservationOrigin : ClaimOrigin
genuineReplayObservationOrigin = crossProverReplayObservation

record ManifestRecognition : Set where
  constructor manifest-recognition
  field
    exactAgdaCommitPinned : Bool
    exactBishopSubmodulePinned : Bool
    loadBearingBlobsMatched : Bool
    sourceDeclarationsObserved : Bool
    theoremBindingTableKernelMatchedOnLeanSide : Bool
    canonicalLeanBindingInhabitedIndependently : Bool
    everyAdmissibleLeanBindingSetoidEquivalent : Bool

    agdaElaborationObserved : Bool
    sourceProofObjectsImportedIntoLean : Bool
    importedBindingInhabitedFromSourceTerms : Bool

open ManifestRecognition public

currentManifestRecognition : ManifestRecognition
currentManifestRecognition =
  manifest-recognition
    true true true true true true true
    false false false

record RecognitionCompilerContract : Set where
  constructor recognition-compiler-contract
  field
    importedBindingNeedsActualSourceTerms : Bool
    manifestAgreementAloneSuffices : Bool
    importedConvergenceStructureMustBePreserved : Bool
    canonicalSetoidAgreementThenFollows : Bool
    primitiveExtractionThenFollows : Bool
    qE4E6DeltaTransportThenFollows : Bool

open RecognitionCompilerContract public

canonicalRecognitionCompilerContract : RecognitionCompilerContract
canonicalRecognitionCompilerContract =
  recognition-compiler-contract
    true false true true true true

record RecognitionBoundary : Set where
  constructor recognition-boundary
  field
    typedClaimOriginsOwned : Bool
    manifestRecognitionSeparatedFromReplay : Bool
    convergenceStructurePreservationRequired : Bool
    downstreamCanonicalizationCompilerOwnedInLean : Bool
    actualCrossProverReplayObserved : Bool

canonicalRecognitionBoundary : RecognitionBoundary
canonicalRecognitionBoundary =
  recognition-boundary
    true true true true false

nextResidual : String
nextResidual =
  "observe a pinned Agda elaboration or genuine proof-term importer that supplies the five Round11/Machin convergence fields to Lean; hashes, declaration names, and theorem-binding-table equality are necessary provenance but are not that proof object"
