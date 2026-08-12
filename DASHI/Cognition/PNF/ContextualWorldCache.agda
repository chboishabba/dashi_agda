module DASHI.Cognition.PNF.ContextualWorldCache where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (_∈_)

open import DASHI.Cognition.PNF.NumericAuthority

------------------------------------------------------------------------
-- Cached external/world candidates are label-local proposal fibres.
--
-- A local lexical symbol such as "Springfield" may have many world candidates.
-- Reusing the label fibre is cheap; selecting one external entity for a mention
-- still requires mention-local contextual evidence.  Caching one previous
-- Springfield does not globally rewrite the label into that entity.
------------------------------------------------------------------------

record WorldEntityId : Set where
  constructor worldEntityId
  field worldEntityValue : Nat

open WorldEntityId public

record CachedWorldCandidate : Set where
  constructor cachedWorldCandidate
  field
    localLabel : SymbolId
    candidateOrdinal : Nat
    worldEntity : WorldEntityId

open CachedWorldCandidate public

record CachedLabelFibre : Set where
  constructor cachedLabelFibre
  field
    label : SymbolId
    candidates : List CachedWorldCandidate
    cacheRevision : Nat

open CachedLabelFibre public

------------------------------------------------------------------------
-- Candidate requirements and mention observations are deliberately different
-- objects.  The database may cache stable requirements for a world candidate,
-- while every mention contributes its own local observed context.
------------------------------------------------------------------------

record CandidateContextRequirement : Set where
  constructor candidateContextRequirement
  field
    requirementCandidate : CachedWorldCandidate
    requiredContextSymbols : List SymbolId
    requirementRevision : Nat

open CandidateContextRequirement public

record MentionContextEvidence : Set where
  constructor mentionContextEvidence
  field
    mentionToken : TokenId
    mentionRegion : RegionId
    observedContextSymbols : List SymbolId
    evidenceId : Nat

open MentionContextEvidence public

-- Every required context symbol must be witnessed in the mention-local observed
-- context before this particular requirement certificate counts as satisfied.
-- This is intentionally a positive witness.  Failure to construct it is not a
-- negative/refutation witness.
ContextRequirementsSatisfied :
  CandidateContextRequirement → MentionContextEvidence → Set
ContextRequirementsSatisfied requirement evidence =
  ∀ {symbol} →
    symbol ∈ requiredContextSymbols requirement →
    symbol ∈ observedContextSymbols evidence

record ContextQualifiedWorldAttachment : Set where
  constructor contextQualifiedWorldAttachment
  field
    labelSymbol : SymbolId
    mention : TokenId
    selectedCandidate : CachedWorldCandidate
    requirement : CandidateContextRequirement
    contextEvidence : MentionContextEvidence
    selectedLabelMatchesMentionLabel :
      localLabel selectedCandidate ≡ labelSymbol
    requirementTargetsSelectedCandidate :
      requirementCandidate requirement ≡ selectedCandidate
    evidenceMentionsSameToken :
      mentionToken contextEvidence ≡ mention
    contextRequirementsSatisfied :
      ContextRequirementsSatisfied requirement contextEvidence

open ContextQualifiedWorldAttachment public

------------------------------------------------------------------------
-- Signed/ternary contextual evidence is evidence about preference, not world
-- identity authority.  A consumer may accumulate positive, neutral and negative
-- axes without converting a strict contextual winner into a canonical identity
-- proof.  In particular, no/unknown context is not negative evidence.
------------------------------------------------------------------------

data ContextAxisDirection : Set where
  contradictsContext neutralContext supportsContext : ContextAxisDirection

record ContextAxisEvidence : Set where
  constructor contextAxisEvidence
  field
    axisSymbol : SymbolId
    candidate : CachedWorldCandidate
    direction : ContextAxisDirection
    axisEvidenceId : Nat

open ContextAxisEvidence public

record ContextualWorldPreference : Set where
  constructor contextualWorldPreference
  field
    mention : TokenId
    preferredCandidate : CachedWorldCandidate
    evidence : List ContextAxisEvidence
    preferenceRevision : Nat

open ContextualWorldPreference public

------------------------------------------------------------------------
-- Boundary laws.
------------------------------------------------------------------------

data CachedLabelIdentityPromotionPermission : Set where

cachedLabelCannotPromoteOneWorldEntity :
  CachedLabelIdentityPromotionPermission → ⊥
cachedLabelCannotPromoteOneWorldEntity ()

data ContextPreferenceIdentityPromotionPermission : Set where

contextPreferenceCannotPromoteWorldIdentity :
  ContextPreferenceIdentityPromotionPermission → ⊥
contextPreferenceCannotPromoteWorldIdentity ()

data MissingContextRefutationPermission : Set where

missingContextDoesNotRefuteCandidate :
  MissingContextRefutationPermission → ⊥
missingContextDoesNotRefuteCandidate ()

record ContextualWorldCacheBoundary : Set where
  constructor contextualWorldCacheBoundary
  field
    labelMayCacheMultipleWorldCandidates : Bool
    labelMayCacheMultipleWorldCandidatesIsTrue :
      labelMayCacheMultipleWorldCandidates ≡ true
    previousAttachmentGloballyFixesLabelMeaning : Bool
    previousAttachmentGloballyFixesLabelMeaningIsFalse :
      previousAttachmentGloballyFixesLabelMeaning ≡ false
    mentionAttachmentRequiresContextEvidence : Bool
    mentionAttachmentRequiresContextEvidenceIsTrue :
      mentionAttachmentRequiresContextEvidence ≡ true
    candidateRequirementsSeparatedFromMentionObservations : Bool
    candidateRequirementsSeparatedFromMentionObservationsIsTrue :
      candidateRequirementsSeparatedFromMentionObservations ≡ true
    missingContextCountsAsNegativeEvidence : Bool
    missingContextCountsAsNegativeEvidenceIsFalse :
      missingContextCountsAsNegativeEvidence ≡ false
    contextualPreferenceIsWorldIdentityProof : Bool
    contextualPreferenceIsWorldIdentityProofIsFalse :
      contextualPreferenceIsWorldIdentityProof ≡ false

open ContextualWorldCacheBoundary public

canonicalContextualWorldCacheBoundary : ContextualWorldCacheBoundary
canonicalContextualWorldCacheBoundary =
  contextualWorldCacheBoundary
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
