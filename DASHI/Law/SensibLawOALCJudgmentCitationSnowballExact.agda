module DASHI.Law.SensibLawOALCJudgmentCitationSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawOALCLegalFollowAttributionSnowballExact as OALC
import DASHI.Law.SensibLawCitationAuthorityFollowExact as Follow
import DASHI.Law.SensibLawCitationUsePropositionExact as Use
import DASHI.Law.SensibLawCitationReviewUnitDecisionGateExact as Review
import DASHI.Law.SensibLawCullenResidualCitationReviewShortlistExact as Shortlist
import DASHI.Law.WaltonsEstoppelMaterialisationExact as Waltons
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Attribution

------------------------------------------------------------------------
-- OALC JUDGMENT -> PARAGRAPH/CITATION SNOWBALL
--
-- A pinned OALC decision may be observed at paragraph/span resolution.  Text
-- matching can schedule research/review work and citation occurrences can
-- schedule exact authority follow.  Neither observation is a legal proposition,
-- estoppel-element payment, treatment classification, current-authority
-- determination, or consumer closure.
------------------------------------------------------------------------

record OalcParagraphCandidate : Set where
  constructor oalcParagraphCandidate
  field
    documentReference : String
    sourceRevisionReference : String
    canonicalTextDigestReference : String
    paragraphOrdinal : Nat
    paragraphLocatorReference : String
    reportedParagraphLabelReference : String
    paragraphTextReference : String
    matchedResearchRequirementReferences : List String

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false

    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open OalcParagraphCandidate public

record OalcJudgmentMaterialisation : Set₁ where
  constructor oalcJudgmentMaterialisation
  field
    sourceReceipt : OALC.PinnedOalcSourceReceipt
    paragraphCandidates : List OalcParagraphCandidate
    citationCandidates : List Follow.CitationCandidate
    digestCorrespondenceReceipt : Set

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    materialisationCreatesLegalAuthority : Bool
    materialisationCreatesLegalAuthorityIsFalse :
      materialisationCreatesLegalAuthority ≡ false

    materialisationCreatesClaimTruth : Bool
    materialisationCreatesClaimTruthIsFalse :
      materialisationCreatesClaimTruth ≡ false

open OalcJudgmentMaterialisation public

------------------------------------------------------------------------
-- Research matching remains scheduling metadata.
------------------------------------------------------------------------

data EstoppelResearchMatch : Set where
  assumptionMatch : EstoppelResearchMatch
  relianceMatch : EstoppelResearchMatch
  detrimentMatch : EstoppelResearchMatch
  unconscionabilityMatch : EstoppelResearchMatch

record ParagraphResearchMatchReceipt : Set where
  constructor paragraphResearchMatchReceipt
  field
    paragraphReference : String
    match : EstoppelResearchMatch
    lexicalMatchReference : String
    researchRequirementReference : String

    reviewStillRequired : Bool
    reviewStillRequiredIsTrue : reviewStillRequired ≡ true

    paysEstoppelRequirement : Bool
    paysEstoppelRequirementIsFalse :
      paysEstoppelRequirement ≡ false

open ParagraphResearchMatchReceipt public

------------------------------------------------------------------------
-- Citation snowball: occurrence -> identity -> acquisition -> PNF re-entry ->
-- reviewed proposition use.  The existing generic parents own every promotion.
------------------------------------------------------------------------

CitationFollowBoundary : Set
CitationFollowBoundary = Follow.CitationFollowBoundary

citationFollowBoundaryPaid : CitationFollowBoundary
citationFollowBoundaryPaid =
  Follow.canonicalCitationFollowBoundary

CitationUseBoundary : Set
CitationUseBoundary = Use.CitationUseBoundary

citationUseBoundaryPaid : CitationUseBoundary
citationUseBoundaryPaid =
  Use.canonicalCitationUseBoundary

ResidualShortlistBoundary : Set
ResidualShortlistBoundary = Shortlist.CullenResidualCitationReviewShortlistBoundary

residualShortlistBoundaryPaid : ResidualShortlistBoundary
residualShortlistBoundaryPaid =
  Shortlist.canonicalCullenResidualCitationReviewShortlistBoundary

CitationReviewBoundary : Set
CitationReviewBoundary = Review.CitationReviewUnitDecisionBoundary

citationReviewBoundaryPaid : CitationReviewBoundary
citationReviewBoundaryPaid =
  Review.canonicalCitationReviewUnitDecisionBoundary

AttributionBoundary : Set
AttributionBoundary = Attribution.AttributionSnowballBoundary

attributionBoundaryPaid : AttributionBoundary
attributionBoundaryPaid =
  Attribution.canonicalAttributionSnowballBoundary

WaltonsBoundary : Set
WaltonsBoundary = Waltons.WaltonsEstoppelBoundary

waltonsBoundaryPaid : WaltonsBoundary
waltonsBoundaryPaid =
  Waltons.canonicalWaltonsEstoppelBoundary

------------------------------------------------------------------------
-- A source-located citation occurrence can schedule exact follow while its use
-- remains unresolved.  Scheduling preserves provenance but creates no treatment.
------------------------------------------------------------------------

record CitationSnowballDirective : Set where
  constructor citationSnowballDirective
  field
    citationCandidate : Follow.CitationCandidate
    jurisdictionReference : String
    exactAuthorityProducerReference : String
    sourceRevisionReference : String
    paragraphLocatorReference : String

    treatmentResolved : Bool
    treatmentResolvedIsFalse : treatmentResolved ≡ false

    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse :
      createsLegalAuthority ≡ false

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

open CitationSnowballDirective public

------------------------------------------------------------------------
-- Formal no-collapse laws.
------------------------------------------------------------------------

data ParagraphObservationAutomaticallyLegalProposition : Set where
data LexicalMatchAutomaticallyPaysEstoppelRequirement : Set where
data CitationOccurrenceAutomaticallyTreatment : Set where
data ExactCitationFollowAutomaticallyCurrentAuthority : Set where
data AcquiredCitedCaseAutomaticallyAdopted : Set where
data ReviewedCitationUseAutomaticallyClosesEstoppelResidual : Set where
data MoreCitationCandidatesAutomaticallyIncreaseAuthorityWeight : Set where
data SnowballMultiplicityAutomaticallyIndependentCorroboration : Set where
data QidOrExternalIdentityAutomaticallyChangesCitationUse : Set where

paragraphDoesNotBecomeLegalProposition :
  ParagraphObservationAutomaticallyLegalProposition → ⊥
paragraphDoesNotBecomeLegalProposition ()

lexicalMatchDoesNotPayEstoppel :
  LexicalMatchAutomaticallyPaysEstoppelRequirement → ⊥
lexicalMatchDoesNotPayEstoppel ()

citationOccurrenceDoesNotBecomeTreatment :
  CitationOccurrenceAutomaticallyTreatment → ⊥
citationOccurrenceDoesNotBecomeTreatment ()

exactFollowDoesNotCreateCurrentAuthority :
  ExactCitationFollowAutomaticallyCurrentAuthority → ⊥
exactFollowDoesNotCreateCurrentAuthority ()

acquiredCaseDoesNotBecomeAdopted :
  AcquiredCitedCaseAutomaticallyAdopted → ⊥
acquiredCaseDoesNotBecomeAdopted ()

reviewedUseDoesNotAutomaticallyCloseEstoppel :
  ReviewedCitationUseAutomaticallyClosesEstoppelResidual → ⊥
reviewedUseDoesNotAutomaticallyCloseEstoppel ()

moreCitationsDoNotCreateAuthorityWeight :
  MoreCitationCandidatesAutomaticallyIncreaseAuthorityWeight → ⊥
moreCitationsDoNotCreateAuthorityWeight ()

snowballMultiplicityDoesNotCreateIndependence :
  SnowballMultiplicityAutomaticallyIndependentCorroboration → ⊥
snowballMultiplicityDoesNotCreateIndependence ()

externalIdentityDoesNotChangeCitationUse :
  QidOrExternalIdentityAutomaticallyChangesCitationUse → ⊥
externalIdentityDoesNotChangeCitationUse ()

record OalcJudgmentCitationSnowballBoundary : Set where
  constructor oalcJudgmentCitationSnowballBoundary
  field
    pinnedOalcDecisionMayRefineToParagraphObserver : Bool
    pinnedOalcDecisionMayRefineToParagraphObserverIsTrue :
      pinnedOalcDecisionMayRefineToParagraphObserver ≡ true

    paragraphObserverRetainsSourceRevision : Bool
    paragraphObserverRetainsSourceRevisionIsTrue :
      paragraphObserverRetainsSourceRevision ≡ true

    lexicalResearchMatchMayScheduleReview : Bool
    lexicalResearchMatchMayScheduleReviewIsTrue :
      lexicalResearchMatchMayScheduleReview ≡ true

    lexicalResearchMatchPaysLegalElement : Bool
    lexicalResearchMatchPaysLegalElementIsFalse :
      lexicalResearchMatchPaysLegalElement ≡ false

    residualIndexedShortlistReused : Bool
    residualIndexedShortlistReusedIsTrue :
      residualIndexedShortlistReused ≡ true

    citationOccurrenceMayScheduleExactFollow : Bool
    citationOccurrenceMayScheduleExactFollowIsTrue :
      citationOccurrenceMayScheduleExactFollow ≡ true

    citationFollowClassifiesTreatment : Bool
    citationFollowClassifiesTreatmentIsFalse :
      citationFollowClassifiesTreatment ≡ false

    reviewedCitationUseRemainsCandidateOnly : Bool
    reviewedCitationUseRemainsCandidateOnlyIsTrue :
      reviewedCitationUseRemainsCandidateOnly ≡ true

    externalIdentityAltersLegalUse : Bool
    externalIdentityAltersLegalUseIsFalse :
      externalIdentityAltersLegalUse ≡ false

canonicalOalcJudgmentCitationSnowballBoundary :
  OalcJudgmentCitationSnowballBoundary
canonicalOalcJudgmentCitationSnowballBoundary =
  oalcJudgmentCitationSnowballBoundary
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl
