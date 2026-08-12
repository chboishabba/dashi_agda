module DASHI.Cognition.PNF.ContextualWorldCache where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

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

record MentionContextEvidence : Set where
  constructor mentionContextEvidence
  field
    mentionToken : TokenId
    mentionRegion : RegionId
    requiredContextSymbols : List SymbolId
    observedContextSymbols : List SymbolId
    evidenceId : Nat

open MentionContextEvidence public

record ContextQualifiedWorldAttachment : Set where
  constructor contextQualifiedWorldAttachment
  field
    labelSymbol : SymbolId
    mention : TokenId
    selectedCandidate : CachedWorldCandidate
    contextEvidence : MentionContextEvidence
    selectedLabelMatchesMentionLabel :
      localLabel selectedCandidate ≡ labelSymbol
    evidenceMentionsSameToken :
      mentionToken contextEvidence ≡ mention

open ContextQualifiedWorldAttachment public

------------------------------------------------------------------------
-- Boundary laws.
------------------------------------------------------------------------

data CachedLabelIdentityPromotionPermission : Set where

cachedLabelCannotPromoteOneWorldEntity :
  CachedLabelIdentityPromotionPermission → ⊥
cachedLabelCannotPromoteOneWorldEntity ()

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

open ContextualWorldCacheBoundary public

canonicalContextualWorldCacheBoundary : ContextualWorldCacheBoundary
canonicalContextualWorldCacheBoundary =
  contextualWorldCacheBoundary true refl false refl true refl
