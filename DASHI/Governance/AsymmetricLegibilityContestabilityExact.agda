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
-- DOI: no DOI listed in the cited journal record.
--
-- Blackwell motivates comparison of information structures.  Nissenbaum
-- motivates context-relative information-flow vocabulary.  Neither source
-- proves the governance conclusions below; the exact factorisation and
-- no-decoder theorem are DASHI constructions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Governance.DomainPermeabilityAuthorityTransport as Domain
import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources

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
    institutionSeparates : inspect L left ≡ inspect L right → ⊥
    subjectCannotSeparate : subjectView L left ≡ subjectView L right

open AsymmetricLegibilityWitness public

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
asymmetricGapBlocksExactSubjectRecovery {L = L} gap decoder =
  institutionSeparates gap institutionViewsEqual
  where
    institutionViewsEqual :
      inspect L (left gap) ≡ inspect L (right gap)
    institutionViewsEqual =
      trans
        (sym (decodeExact decoder (left gap)))
        (trans
          (cong (decode decoder) (subjectCannotSeparate gap))
          (decodeExact decoder (right gap)))

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

finiteAsymmetricGap : AsymmetricLegibilityWitness finiteLegibilityChannel
finiteAsymmetricGap =
  asymmetricLegibilityWitness case0 case1 (λ ()) refl

finiteExactDecoderImpossible :
  ExactInstitutionalViewDecoder finiteLegibilityChannel → ⊥
finiteExactDecoderImpossible =
  asymmetricGapBlocksExactSubjectRecovery finiteAsymmetricGap

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
  asymmetricLegibilityBoundary false false false true true true

record AsymmetricLegibilitySourceReceipt : Set where
  constructor asymmetricLegibilitySourceReceipt
  field
    sources : List Sources.ScholarlySource
    boundary : AsymmetricLegibilityBoundary

canonicalAsymmetricLegibilitySourceReceipt : AsymmetricLegibilitySourceReceipt
canonicalAsymmetricLegibilitySourceReceipt =
  asymmetricLegibilitySourceReceipt
    (Sources.blackwellExperimentComparison
      ∷ Sources.nissenbaumContextualIntegrity
      ∷ [])
    canonicalAsymmetricLegibilityBoundary
