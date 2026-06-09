module DASHI.Core.AuthorityBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Citation authority and artifact authority are distinct authority kinds.
--
-- A citation can close a source-identification slot without authorizing a
-- machine-readable artifact.  Artifact authority is a separate kind and must
-- be carried by its own boundary receipt.

data AuthorityKind : Set where
  CitationAuthority :
    AuthorityKind

  ArtifactAuthority :
    AuthorityKind

record AuthorityBoundary (kind : AuthorityKind) : Set where
  constructor mkAuthorityBoundary
  field
    authorityKind :
      AuthorityKind

    authorityKindMatches :
      authorityKind ≡ kind

    recordIdentifier :
      String

    citation :
      String

    authorityAccepted :
      Bool

    artifactAuthority :
      Bool

    machineReadableArtifactPresent :
      Bool

    notes :
      List String

open AuthorityBoundary public

CitationAuthorityBoundary :
  Set
CitationAuthorityBoundary =
  AuthorityBoundary CitationAuthority

ArtifactAuthorityBoundary :
  Set
ArtifactAuthorityBoundary =
  AuthorityBoundary ArtifactAuthority

record CitationAuthorityNoArtifact : Set where
  constructor mkCitationAuthorityNoArtifact
  field
    citationBoundary :
      CitationAuthorityBoundary

    citationAuthorityAccepted :
      authorityAccepted citationBoundary ≡ true

    artifactAuthorityIsFalse :
      artifactAuthority citationBoundary ≡ false

    machineReadableArtifactPresentIsFalse :
      machineReadableArtifactPresent citationBoundary ≡ false

open CitationAuthorityNoArtifact public
