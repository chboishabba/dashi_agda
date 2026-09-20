module DASHI.Core.LocalDeclarationScopeExact where

open import DASHI.Core.Prelude
open import DASHI.Core.TemporalSemanticGraphExact

------------------------------------------------------------------------
-- LOCAL DECLARATION OWNERSHIP
--
-- A declaration introduced in a local where-scope remains a semantic symbol,
-- but its identity is scoped and it carries explicit ownership evidence back
-- to the declaration whose local scope introduced it.
------------------------------------------------------------------------

data DeclarationVisibility : Set where
  moduleVisible : DeclarationVisibility
  localVisible : DeclarationVisibility

record DeclarationScopeEvidence : Set where
  constructor declarationScopeEvidence
  field
    declarationId : String
    declarationScopeId : String
    declarationVisibility : DeclarationVisibility

open DeclarationScopeEvidence public

data LocalOwnershipDisposition : Set where
  moduleContainmentOnly : LocalOwnershipDisposition
  localOwnershipRequired : LocalOwnershipDisposition

ownershipDisposition :
  DeclarationVisibility →
  LocalOwnershipDisposition
ownershipDisposition moduleVisible = moduleContainmentOnly
ownershipDisposition localVisible = localOwnershipRequired

localDeclarationRequiresOwnership :
  ownershipDisposition localVisible
    ≡ localOwnershipRequired
localDeclarationRequiresOwnership = refl

moduleDeclarationDoesNotRequireLocalOwner :
  ownershipDisposition moduleVisible
    ≡ moduleContainmentOnly
moduleDeclarationDoesNotRequireLocalOwner = refl

record LocalDeclarationScopeBoundary : Set where
  constructor localDeclarationScopeBoundary
  field
    equalNamesInDifferentLocalScopesDefineSameIdentity : Bool
    equalNamesInDifferentLocalScopesDefineSameIdentityIsFalse :
      equalNamesInDifferentLocalScopesDefineSameIdentity ≡ false

    localDeclarationMayBecomeModuleGlobalByRendering : Bool
    localDeclarationMayBecomeModuleGlobalByRenderingIsFalse :
      localDeclarationMayBecomeModuleGlobalByRendering ≡ false

    localOwnershipMayBeOmittedFromAuthorityGraph : Bool
    localOwnershipMayBeOmittedFromAuthorityGraphIsFalse :
      localOwnershipMayBeOmittedFromAuthorityGraph ≡ false

canonicalLocalDeclarationScopeBoundary :
  LocalDeclarationScopeBoundary
canonicalLocalDeclarationScopeBoundary =
  localDeclarationScopeBoundary
    false refl
    false refl
    false refl
