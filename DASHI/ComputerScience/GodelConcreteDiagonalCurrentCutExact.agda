module DASHI.ComputerScience.GodelConcreteDiagonalCurrentCutExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- CURRENT CANONICAL DIAGONAL CUT AFTER 2026 SOTA AUDIT
--
-- The executable base-12 code remains an implementation lane.  Recent
-- machine-checked external arithmetic developments mean that re-proving
-- representability/diagonalisation from scratch is no longer the preferred
-- theorem route.  The canonical residual is same-object transport into the
-- local ABI, with syntactic-shape preservation made explicit.
------------------------------------------------------------------------

data LiveDiagonalResidual : Set where
  externalArithmeticSameObjectAdapter
  sourceNativeSubstitutionAndRepresentationAlignment
  representedFunctionPrecompositionClosure : LiveDiagonalResidual

data OptionalDiagonalProducerResidual : Set where
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
    coquandT4AdapterFrontierOwned : Bool
    canonicalLiveResiduals : List LiveDiagonalResidual
    optionalProducerResiduals : List OptionalDiagonalProducerResidual
    base12PRIsMandatoryForDiagonal : Bool
    fromScratchPRLibraryIsMandatory : Bool
    concreteDiagonalLemmaKernelCertified : Bool

canonicalCurrentDiagonalCut : CurrentDiagonalCut
canonicalCurrentDiagonalCut =
  currentDiagonalCut
    true true true true true true true true
    true true true
    (externalArithmeticSameObjectAdapter ∷
     sourceNativeSubstitutionAndRepresentationAlignment ∷
     representedFunctionPrecompositionClosure ∷ [])
    (base12SelfSubstitutionPrimitiveRecursive ∷
     base12ToSourceNativeSameCodeWeld ∷
     fromScratchPrimitiveRecursiveLibrary ∷ [])
    false
    false
    false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SourceWrittenCodecMeansKernelCertified : Set where
data ClosedSerializationMeansClosedDiagonalLemma : Set where
data SourceRepresentabilityMeansCustomBase12PR : Set where
data OptionalBase12ProducerIsMandatoryTheoremDebt : Set where
data ExternalFormalisationAutomaticallyPaysLocalABI : Set where
data ExistingMachineProofMeansReproveLocally : Set where

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
