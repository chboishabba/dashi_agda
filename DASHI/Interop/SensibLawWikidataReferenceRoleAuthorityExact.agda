module DASHI.Interop.SensibLawWikidataReferenceRoleAuthorityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- WIKIDATA REFERENCE ROLE != SOURCE SUPPORT != AUTHORITY
--
-- Cross-pollination from the attached Aristotle and Senate-law archives:
-- * Aristotle distinguishes reference URL / stated in from imported-from
--   provenance, with imported-from not counted as a reliable source;
-- * the Senate model separately types procedural source and floor enforceability,
--   showing that source identity is still weaker than consumer-specific authority.
------------------------------------------------------------------------

data WikidataReferenceProperty : Set where
  p854ReferenceURL : WikidataReferenceProperty
  p248StatedIn : WikidataReferenceProperty
  p143ImportedFrom : WikidataReferenceProperty
  otherReferenceProperty : WikidataReferenceProperty

data ReferenceRole : Set where
  sourceCandidate : ReferenceRole
  provenanceOnly : ReferenceRole
  unclassifiedReference : ReferenceRole

roleForReferenceProperty : WikidataReferenceProperty → ReferenceRole
roleForReferenceProperty p854ReferenceURL = sourceCandidate
roleForReferenceProperty p248StatedIn = sourceCandidate
roleForReferenceProperty p143ImportedFrom = provenanceOnly
roleForReferenceProperty otherReferenceProperty = unclassifiedReference

p854IsSourceCandidate : roleForReferenceProperty p854ReferenceURL ≡ sourceCandidate
p854IsSourceCandidate = refl

p248IsSourceCandidate : roleForReferenceProperty p248StatedIn ≡ sourceCandidate
p248IsSourceCandidate = refl

p143IsProvenanceOnly : roleForReferenceProperty p143ImportedFrom ≡ provenanceOnly
p143IsProvenanceOnly = refl

data ReferencePresencePaysSourceSupport : Set where
data ProvenanceOnlyPaysSourceSupport : Set where
data SourceCandidateAutomaticallyAuthoritative : Set where
data SourceCandidateSkipsContentVerification : Set where

referencePresenceDoesNotPaySourceSupport : ReferencePresencePaysSourceSupport → ⊥
referencePresenceDoesNotPaySourceSupport ()

provenanceOnlyDoesNotPaySourceSupport : ProvenanceOnlyPaysSourceSupport → ⊥
provenanceOnlyDoesNotPaySourceSupport ()

sourceCandidateDoesNotCreateAuthority : SourceCandidateAutomaticallyAuthoritative → ⊥
sourceCandidateDoesNotCreateAuthority ()

sourceCandidateStillNeedsContentVerification : SourceCandidateSkipsContentVerification → ⊥
sourceCandidateStillNeedsContentVerification ()

record WikidataReferenceRoleAuthorityBoundary : Set where
  constructor wikidata-reference-role-authority-boundary
  field
    p854SourceCandidate : Bool
    p248SourceCandidate : Bool
    p143ProvenanceOnly : Bool
    referencePresencePaysSupport : Bool
    provenanceOnlyPaysSupport : Bool
    sourceCandidateCreatesAuthority : Bool
    sourceCandidateNeedsContentVerification : Bool
    sourceCandidateNeedsConsumerAuthorityEvaluation : Bool
    primarySourcePreferredWhenAvailable : Bool

canonicalWikidataReferenceRoleAuthorityBoundary : WikidataReferenceRoleAuthorityBoundary
canonicalWikidataReferenceRoleAuthorityBoundary =
  wikidata-reference-role-authority-boundary
    true true true false false false true true true
