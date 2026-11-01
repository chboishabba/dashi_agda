module DASHI.Foundations.UBP.ExternalRepositoryProvenance where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- External repository provenance.
--
-- The mathematical and computational material studied by the UBP tranche is
-- attributed to its external author and repository at the type level.  DASHI
-- contributes a critical formalisation and cross-pollination layer; it does
-- not claim authorship of the Universal Binary Principle repository, TGIC,
-- TAX, NRCI, OffBit, GLR, or the source implementation studied here.
------------------------------------------------------------------------

record ExternalRepositorySource : Set where
  constructor externalRepositorySource
  field
    projectName : String
    authorName : String
    repositoryOwner : String
    repositoryName : String
    repositoryURL : String
    defaultBranch : String
    sourcePath : String
    sourceRelationship : String
    sourceDOI : String

open ExternalRepositorySource public

ubpProjectName : String
ubpProjectName = "Universal Binary Principle — Research Repository"

ubpAuthorName : String
ubpAuthorName = "Euan R. A. Craig (DigitalEuan)"

ubpRepositoryOwner : String
ubpRepositoryOwner = "DigitalEuan"

ubpRepositoryName : String
ubpRepositoryName = "UBP_Repo"

ubpRepositoryURL : String
ubpRepositoryURL = "https://github.com/DigitalEuan/UBP_Repo"

ubpDefaultBranch : String
ubpDefaultBranch = "main"

ubpRepositorySource : ExternalRepositorySource
ubpRepositorySource =
  externalRepositorySource
    ubpProjectName
    ubpAuthorName
    ubpRepositoryOwner
    ubpRepositoryName
    ubpRepositoryURL
    ubpDefaultBranch
    "README.md"
    "external project identity and author statement; DASHI does not claim authorship"
    "no DOI assigned to the GitHub repository"

ubpCheckpointSource : ExternalRepositorySource
ubpCheckpointSource =
  externalRepositorySource
    ubpProjectName
    ubpAuthorName
    ubpRepositoryOwner
    ubpRepositoryName
    ubpRepositoryURL
    ubpDefaultBranch
    "core_studio_v4.0/ubp_checkpoint_v5.4.1.md"
    "source checkpoint whose claims and implementation boundaries are formalised critically"
    "no DOI assigned to this repository file"

ubpUnifiedCoreSource : ExternalRepositorySource
ubpUnifiedCoreSource =
  externalRepositorySource
    ubpProjectName
    ubpAuthorName
    ubpRepositoryOwner
    ubpRepositoryName
    ubpRepositoryURL
    ubpDefaultBranch
    "core_studio_v4.0/core/ubp_unified_v5.py"
    "source implementation for the declared Golay, Leech, TAX, NRCI, and observer-constant operations"
    "no DOI assigned to this repository file"

ubpTGICSource : ExternalRepositorySource
ubpTGICSource =
  externalRepositorySource
    ubpProjectName
    ubpAuthorName
    ubpRepositoryOwner
    ubpRepositoryName
    ubpRepositoryURL
    ubpDefaultBranch
    "core_studio_v4.0/core/tgic_v3.py"
    "source implementation for the three-axis, six-directed-face, nine-local-term simulator studied by the DASHI bridge"
    "no DOI assigned to this repository file"

sourceCount : ∀ {A : Set} → List A → Nat
sourceCount [] = zero
sourceCount (_ ∷ xs) = suc (sourceCount xs)

canonicalUBPExternalSources : List ExternalRepositorySource
canonicalUBPExternalSources =
  ubpRepositorySource
  ∷ ubpCheckpointSource
  ∷ ubpUnifiedCoreSource
  ∷ ubpTGICSource
  ∷ []

canonicalUBPExternalSourceCount : Nat
canonicalUBPExternalSourceCount = sourceCount canonicalUBPExternalSources

canonicalUBPExternalSourceCountIsFour :
  canonicalUBPExternalSourceCount ≡ 4
canonicalUBPExternalSourceCountIsFour = refl

record ExternalProvenanceReceipt : Set where
  constructor externalProvenanceReceipt
  field
    repositoryIdentityAttached : Bool
    repositoryIdentityAttachedIsTrue : repositoryIdentityAttached ≡ true
    authorIdentityAttached : Bool
    authorIdentityAttachedIsTrue : authorIdentityAttached ≡ true
    sourcePathsAttached : Bool
    sourcePathsAttachedIsTrue : sourcePathsAttached ≡ true
    dashiClaimsOriginalUBPAuthorship : Bool
    dashiClaimsOriginalUBPAuthorshipIsFalse :
      dashiClaimsOriginalUBPAuthorship ≡ false
    formalisationIsDerivativeCriticalWork : Bool
    formalisationIsDerivativeCriticalWorkIsTrue :
      formalisationIsDerivativeCriticalWork ≡ true

open ExternalProvenanceReceipt public

canonicalExternalProvenanceReceipt : ExternalProvenanceReceipt
canonicalExternalProvenanceReceipt =
  externalProvenanceReceipt
    true refl
    true refl
    true refl
    false refl
    true refl

externalRepositoryProvenanceGenericReceipt : GenericReceipt.GenericReceipt
externalRepositoryProvenanceGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "UBP external repository provenance"
    "DASHI.Foundations.UBP.ExternalRepositoryProvenance"
    "canonicalUBPExternalSources"
    "project name, author name, GitHub owner, repository URL, branch, and source paths are attached explicitly"
    "citation and attribution do not import theorem proofs or promote UBP physical and semantic claims"
    "agda -i . DASHI/Foundations/UBP/ExternalRepositoryProvenance.agda"

externalRepositoryProvenanceNonPromoting :
  GenericReceipt.promotesClaim externalRepositoryProvenanceGenericReceipt ≡ false
externalRepositoryProvenanceNonPromoting =
  GenericReceipt.promotesClaimIsFalse externalRepositoryProvenanceGenericReceipt
