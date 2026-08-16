module DASHI.Governance.AsymmetricLegibilityContestabilityExact where

------------------------------------------------------------------------
-- SOURCE / CROSS-POLLINATION CALIBRATION
--
-- Author: David Blackwell.
-- Title: "Equivalent Comparisons of Experiments".
-- Venue: The Annals of Mathematical Statistics 24(2), 265--272 (1953).
-- DOI: 10.1214/aoms/1177729032.
--
-- Author: Helen Nissenbaum.
-- Title: "Privacy as Contextual Integrity".
-- Venue: Washington Law Review 79(1), 119--158 (2004).
-- DOI: no DOI assigned/recorded for the journal article.
--
-- Blackwell motivates comparison of information structures.  Nissenbaum
-- motivates context-relative information-flow vocabulary.  Neither source
-- proves the governance conclusions below; the exact factorisation and
-- no-decoder theorem are DASHI constructions.
--
-- Internal producer pollen:
--   * PR #549: raw/internal representation can be strictly finer than the
--     admitted/coarsened observation channel;
--   * PR #556: DomainPermeabilityAuthorityTransport keeps technical reuse
--     separate from legitimate authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Governance.DomainPermeabilityAuthorityTransport as Domain

------------------------------------------------------------------------
-- An institution may hold a finer representation than the view disclosed to
-- the affected subject.  subjectView is definitionally a coarsening of the
-- institutional view through disclose.
------------------------------------------------------------------------

record LegibilityChannel : Set₁ where
  constructor legibilityChannel
  field
    Subject : Set
    InstitutionalView : Set
    SubjectView : Set
    inspect : Subject → InstitutionalView
    disclose : InstitutionalView → SubjectView

open LegibilityChannel public

subjectView :
  (L : LegibilityChannel) →
  Subject L → SubjectView L
subjectView L subject = disclose L (inspect L subject)

record AsymmetricLegibilityWitness
  (L : LegibilityChannel) : Set₁ where
  constructor asymmetricLegibilityWitness
  field
    left right : Subject L
    institutionSeparates :
      inspect L left ≡ inspect L right → ⊥
    subjectCannotSeparate :
      subjectView L left ≡ subjectView L right

open AsymmetricLegibilityWitness public

------------------------------------------------------------------------
-- Exact decoder obstruction.
--
-- If the disclosed subject-side view collapses two institutionally distinct
-- cases, there cannot be a decoder from the disclosed view that recovers the
-- exact institutional representation for every subject.
------------------------------------------------------------------------

record ExactInstitutionalViewDecoder
  (L : LegibilityChannel) : Set₁ where
  constructor exactInstitutionalViewDecoder
  field
    decode : SubjectView L → InstitutionalView L
    decodeExact :
      (subject : Subject L) →
      decode (subjectView L subject) ≡ inspect L subject

open ExactInstitutionalViewDecoder public

asymmetricGapBlocksExactSubjectRecovery :
  ∀ {L : LegibilityChannel} →
  AsymmetricLegibilityWitness L →
  ExactInstitutionalViewDecoder L →
  ⊥
asymmetricGapBlocksExactSubjectRecovery gap decoder =
  institutionSeparates gap institutionViewsEqual
  where
    institutionViewsEqual :
      inspect _ (left gap) ≡ inspect _ (right gap)
    institutionViewsEqual =
      trans
        (sym (decodeExact decoder (left gap)))
        (trans
          (cong (decode decoder) (subjectCannotSeparate gap))
          (decodeExact decoder (right gap)))

------------------------------------------------------------------------
-- Contestability is represented separately from legibility.  A system may be
-- informationally asymmetric yet expose explanation, appeal and correction;
-- or it may expose none.  The carrier itself does not classify either case as
-- lawful/unlawful, fair/unfair, or abusive/non-abusive.
------------------------------------------------------------------------

record ContestabilityInterface
  (L : LegibilityChannel) : Set₁ where
  constructor contestabilityInterface
  field
    Explanation : Subject L → Set
    Appeal : Subject L → Set
    Correction : Subject L → Set

open ContestabilityInterface public

record ContestabilityReceipt
  {L : LegibilityChannel}
  (C : ContestabilityInterface L)
  (subject : Subject L) : Set₁ where
  constructor contestabilityReceipt
  field
    explanationAvailable : Explanation C subject
    appealAvailable : Appeal C subject
    correctionAvailable : Correction C subject

------------------------------------------------------------------------
-- Authority and contestability do not arrive merely from reuse of the same
-- machinery.  Reuse across a target domain still needs its own authority
-- witness in the existing domain-permeability theorem.
------------------------------------------------------------------------

domainReuseStillNeedsOwnAuthority :
  Domain.DomainTransportReceipt.targetDomainNeedsOwnAuthorityWitness
    Domain.canonicalDomainTransportReceipt
  ≡ true
domainReuseStillNeedsOwnAuthority = refl

sameRepresentationStillDoesNotCreateAuthority :
  Domain.DomainTransportReceipt.representationEqualityCreatesLegalAuthority
    Domain.canonicalDomainTransportReceipt
  ≡ false
sameRepresentationStillDoesNotCreateAuthority = refl

------------------------------------------------------------------------
-- Finite regression: two cases are separated internally and collapsed in the
-- disclosed bit.  Therefore exact institutional reconstruction is impossible.
------------------------------------------------------------------------

data Case2 : Set where case0 case1 : Case2

data Internal2 : Set where internal0 internal1 : Internal2

data PublicOne : Set where public : PublicOne

inspect2 : Case2 → Internal2
inspect2 case0 = internal0
inspect2 case1 = internal1

disclose2 : Internal2 → PublicOne
disclose2 internal0 = public
disclose2 internal1 = public

finiteLegibilityChannel : LegibilityChannel
finiteLegibilityChannel =
  legibilityChannel Case2 Internal2 PublicOne inspect2 disclose2

finiteAsymmetricGap :
  AsymmetricLegibilityWitness finiteLegibilityChannel
finiteAsymmetricGap =
  asymmetricLegibilityWitness case0 case1 (λ ()) refl

finiteExactDecoderImpossible :
  ExactInstitutionalViewDecoder finiteLegibilityChannel → ⊥
finiteExactDecoderImpossible =
  asymmetricGapBlocksExactSubjectRecovery finiteAsymmetricGap

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record AsymmetricLegibilityBoundary : Set where
  constructor asymmetricLegibilityBoundary
  field
    institutionCanDistinguishImpliesSubjectCanReconstruct : Bool
    asymmetryAloneProvesAbuse : Bool
    asymmetryAloneProvesIllegality : Bool
    explanationAppealCorrectionAreSeparateWitnesses : Bool
    targetDomainAuthorityNeedsSeparateWitness : Bool
    exactRecoveryBlockedByConcreteCollapseWitness : Bool

canonicalAsymmetricLegibilityBoundary : AsymmetricLegibilityBoundary
canonicalAsymmetricLegibilityBoundary =
  asymmetricLegibilityBoundary
    false
    false
    false
    true
    true
    true
