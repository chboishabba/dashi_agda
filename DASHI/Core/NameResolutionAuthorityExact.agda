module DASHI.Core.NameResolutionAuthorityExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- NAME-RESOLUTION AUTHORITY BOUNDARY
--
-- Syntax extraction may observe names, but dependency admission requires scope
-- evidence.  Repo-wide uniqueness alone never licenses an unqualified edge.
------------------------------------------------------------------------

data ResolutionEvidenceKind : Set where
  sameModuleEvidence : ResolutionEvidenceKind
  qualifiedNameEvidence : ResolutionEvidenceKind
  admittedOpenScopeEvidence : ResolutionEvidenceKind
  globalUniquenessOnly : ResolutionEvidenceKind
  unresolvedEvidence : ResolutionEvidenceKind

data ResolutionDisposition : Set where
  admitDependency : ResolutionDisposition
  rejectDependency : ResolutionDisposition

resolutionDisposition :
  ResolutionEvidenceKind →
  ResolutionDisposition
resolutionDisposition sameModuleEvidence = admitDependency
resolutionDisposition qualifiedNameEvidence = admitDependency
resolutionDisposition admittedOpenScopeEvidence = admitDependency
resolutionDisposition globalUniquenessOnly = rejectDependency
resolutionDisposition unresolvedEvidence = rejectDependency

globalUniquenessDoesNotAdmit :
  resolutionDisposition globalUniquenessOnly
    ≡ rejectDependency
globalUniquenessDoesNotAdmit = refl

sameModuleAdmits :
  resolutionDisposition sameModuleEvidence
    ≡ admitDependency
sameModuleAdmits = refl

qualifiedNameAdmits :
  resolutionDisposition qualifiedNameEvidence
    ≡ admitDependency
qualifiedNameAdmits = refl

openScopeAdmits :
  resolutionDisposition admittedOpenScopeEvidence
    ≡ admitDependency
openScopeAdmits = refl

record OpenScopeBoundary : Set where
  constructor openScopeBoundary
  field
    usingRestrictionMayBeIgnored : Bool
    usingRestrictionMayBeIgnoredIsFalse :
      usingRestrictionMayBeIgnored ≡ false

    hidingRestrictionMayBeIgnored : Bool
    hidingRestrictionMayBeIgnoredIsFalse :
      hidingRestrictionMayBeIgnored ≡ false

    renamingMayInventOldAndNewAliases : Bool
    renamingMayInventOldAndNewAliasesIsFalse :
      renamingMayInventOldAndNewAliases ≡ false

canonicalOpenScopeBoundary : OpenScopeBoundary
canonicalOpenScopeBoundary =
  openScopeBoundary
    false refl
    false refl
    false refl
