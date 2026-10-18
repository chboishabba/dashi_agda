module DASHI.Core.SemanticPatchBackendExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- SEMANTIC PATCH BACKEND BOUNDARY
--
-- Tree-sitter/source observations are upstream evidence. A patch backend may
-- accelerate deterministic graph reconstruction, but it may not acquire new
-- semantic authority or change the graph contract.
------------------------------------------------------------------------

data SemanticBackendKind : Set where
  pythonReferenceBackend : SemanticBackendKind
  rustCandidateBackend : SemanticBackendKind

record SemanticPatchBackendContract : Set where
  constructor semanticPatchBackendContract
  field
    backendKind : SemanticBackendKind
    sourceObservationsRemainAuthority : Bool
    sourceObservationsRemainAuthorityIsTrue :
      sourceObservationsRemainAuthority ≡ true

    backendMayInventDependency : Bool
    backendMayInventDependencyIsFalse :
      backendMayInventDependency ≡ false

    backendMayInventSymbolIdentity : Bool
    backendMayInventSymbolIdentityIsFalse :
      backendMayInventSymbolIdentity ≡ false

open SemanticPatchBackendContract public

pythonReferenceContract : SemanticPatchBackendContract
pythonReferenceContract =
  semanticPatchBackendContract
    pythonReferenceBackend
    true refl
    false refl
    false refl

rustCandidateContract : SemanticPatchBackendContract
rustCandidateContract =
  semanticPatchBackendContract
    rustCandidateBackend
    true refl
    false refl
    false refl

record BackendParityBoundary : Set where
  constructor backendParityBoundary
  field
    implementationLanguageMayChangeGraphMeaning : Bool
    implementationLanguageMayChangeGraphMeaningIsFalse :
      implementationLanguageMayChangeGraphMeaning ≡ false

    rustBackendRequiresReferenceParity : Bool
    rustBackendRequiresReferenceParityIsTrue :
      rustBackendRequiresReferenceParity ≡ true

canonicalBackendParityBoundary : BackendParityBoundary
canonicalBackendParityBoundary =
  backendParityBoundary
    false refl
    true refl
