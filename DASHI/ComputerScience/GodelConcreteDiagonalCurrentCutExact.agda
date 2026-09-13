module DASHI.ComputerScience.GodelConcreteDiagonalCurrentCutExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- CURRENT CANONICAL DIAGONAL CUT AFTER 2026 SOTA + IMPORT AUDIT
--
-- The mathematics is no longer the first mandatory blocker.  A finished
-- external Agda development already owns the relevant diagonal/Lob/Godel-II
-- machinery.  The present critical path is exact dependency intake followed by
-- same-carrier payment construction and local kernel replay.
------------------------------------------------------------------------

data LiveDiagonalResidual : Set where
  coquandT4DependencyIntake
  coquandT4ArithmeticSourcePayment
  coquandT4FinishedDiagonalPayment
  localKernelReplayReceipt : LiveDiagonalResidual

data OptionalDiagonalProducerResidual : Set where
  sourceNativeSubstitutionAndRepresentationAlignment
  representedFunctionPrecompositionClosure
  base12SelfSubstitutionPrimitiveRecursive
  base12ToSourceNativeSameCodeWeld
  fromScratchPrimitiveRecursiveLibrary : OptionalDiagonalProducerResidual

record CurrentDiagonalCut : Set where
  constructor currentDiagonalCut
  field
    rawArithmeticSyntaxSourceWritten : Bool
    captureAvoidingInstantiationSourceWritten : Bool
    prefixStreamRoundtripSourceWritten : Bool
    base12NatRetractionSourceWritten : Bool
    genericArithmetisedSubstitutionCompilerOwned : Bool
    genericDiagonalCompilerOwned : Bool
    primitiveRecursiveRepresentabilityCompilerOwned : Bool
    theoremVRelationGraphAdapterOwned : Bool
    recentExternalMachineCheckedProducersLocated : Bool
    formulaSentenceShapeAuthorityOwned : Bool
    externalArithmeticABICompilerOwned : Bool
    externalFinishedDiagonalCompilerOwned : Bool
    coquandT4PaymentTargetOwned : Bool
    exactT4RevisionPinned : Bool
    upstreamLicenseResolved : Bool
    localT4DependencyPresent : Bool
    canonicalLiveResiduals : List LiveDiagonalResidual
    optionalProducerResiduals : List OptionalDiagonalProducerResidual
    representabilityRouteMandatoryForFinishedExternalProof : Bool
    base12PRIsMandatoryForDiagonal : Bool
    fromScratchPRLibraryIsMandatory : Bool
    concreteDiagonalLemmaKernelCertified : Bool

canonicalCurrentDiagonalCut : CurrentDiagonalCut
canonicalCurrentDiagonalCut =
  currentDiagonalCut
    true true true true true true true true
    true true true true true
    true false false
    (coquandT4DependencyIntake ∷
     coquandT4ArithmeticSourcePayment ∷
     coquandT4FinishedDiagonalPayment ∷
     localKernelReplayReceipt ∷ [])
    (sourceNativeSubstitutionAndRepresentationAlignment ∷
     representedFunctionPrecompositionClosure ∷
     base12SelfSubstitutionPrimitiveRecursive ∷
     base12ToSourceNativeSameCodeWeld ∷
     fromScratchPrimitiveRecursiveLibrary ∷ [])
    false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SourceWrittenCodecMeansKernelCertified : Set where
data ClosedSerializationMeansClosedDiagonalLemma : Set where
data SourceRepresentabilityMeansCustomBase12PR : Set where
data OptionalBase12ProducerIsMandatoryTheoremDebt : Set where
data ExternalFormalisationAutomaticallyPaysLocalABI : Set where
data ExistingMachineProofMeansReproveLocally : Set where
data FinishedExternalProofRequiresLocalRepresentabilityReplay : Set where
data PublicUpstreamMeansDependencyMayBeVendored : Set where

sourceWrittenDoesNotMeanCertified :
  SourceWrittenCodecMeansKernelCertified → ⊥
sourceWrittenDoesNotMeanCertified ()

serializationDoesNotCloseDiagonal :
  ClosedSerializationMeansClosedDiagonalLemma → ⊥
serializationDoesNotCloseDiagonal ()

historicalRepresentabilityDoesNotPayCustomCode :
  SourceRepresentabilityMeansCustomBase12PR → ⊥
historicalRepresentabilityDoesNotPayCustomCode ()

base12ProducerDoesNotBecomeMandatory :
  OptionalBase12ProducerIsMandatoryTheoremDebt → ⊥
base12ProducerDoesNotBecomeMandatory ()

externalFormalisationNeedsAdapter :
  ExternalFormalisationAutomaticallyPaysLocalABI → ⊥
externalFormalisationNeedsAdapter ()

machineCheckedPriorArtDoesNotForceReproof :
  ExistingMachineProofMeansReproveLocally → ⊥
machineCheckedPriorArtDoesNotForceReproof ()

finishedExternalProofDoesNotForceRepresentabilityReplay :
  FinishedExternalProofRequiresLocalRepresentabilityReplay → ⊥
finishedExternalProofDoesNotForceRepresentabilityReplay ()

publicUpstreamDoesNotSupplyVendoringAuthority :
  PublicUpstreamMeansDependencyMayBeVendored → ⊥
publicUpstreamDoesNotSupplyVendoringAuthority ()
