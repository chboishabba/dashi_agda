module DASHI.Law.SensibLawJudgmentFootnoteAnchorObserverRefinementExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Second introspective refinement of the retained Cullen judgment observer.
--
-- v0.2 has now been observed to recover 190 citation candidates from body plus
-- 163 material footnotes. That observer still leaves a consumer-relevant
-- collision: a citation in footnote N does not itself say which body proposition
-- invoked footnote N. The exact missing coordinate is the WordprocessingML
-- body paragraph -> w:footnoteReference/@w:id relation.
--
-- Rust v0.3 preserves that relation and propagates it to each footnote citation
-- candidate as anchor paragraph locator(s) and anchor text(s). This is source
-- provenance only. It cannot itself establish residual relevance, treatment,
-- proposition correspondence, authority or payment.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

lastObservedV02Head : String
lastObservedV02Head = "00bb9957ace2d3c2ea7d6104ad5cab100dd29369"

v03SourceHeadBeforeLocalValidation : String
v03SourceHeadBeforeLocalValidation = "fc5aeec3607fb908259d2d890f48435987c87320"

v02Schema : String
v02Schema = "sl.judgment_citation_review_queue.v0_2"

v03Schema : String
v03Schema = "sl.judgment_citation_review_queue.v0_3"

liveResidualRef : String
liveResidualRef = "residual:cullen-positive-operational-act"

livePropositionRef : String
livePropositionRef = "prop:cullen-positive-operational-duty"

missingCoordinate : String
missingCoordinate = "body paragraph <-> w:footnoteReference/@w:id"

record FootnoteAnchorObserverRefinementBoundary : Set where
  constructor footnoteAnchorObserverRefinementBoundary
  field
    v02BodyAndFootnoteObserverObserved : Bool
    v02BodyAndFootnoteObserverObservedIsTrue :
      v02BodyAndFootnoteObserverObserved ≡ true

    v03BodyParagraphCarrierImplemented : Bool
    v03BodyParagraphCarrierImplementedIsTrue :
      v03BodyParagraphCarrierImplemented ≡ true

    v03FootnoteReferenceIdPreserved : Bool
    v03FootnoteReferenceIdPreservedIsTrue :
      v03FootnoteReferenceIdPreserved ≡ true

    v03CitationCandidateAnchorLocatorsImplemented : Bool
    v03CitationCandidateAnchorLocatorsImplementedIsTrue :
      v03CitationCandidateAnchorLocatorsImplemented ≡ true

    v03CitationCandidateAnchorTextsImplemented : Bool
    v03CitationCandidateAnchorTextsImplementedIsTrue :
      v03CitationCandidateAnchorTextsImplemented ≡ true

    oldBodyOnlyDigestPathRetained : Bool
    oldBodyOnlyDigestPathRetainedIsTrue : oldBodyOnlyDigestPathRetained ≡ true

    v03ExtractionNetworkFreeByConstruction : Bool
    v03ExtractionNetworkFreeByConstructionIsTrue :
      v03ExtractionNetworkFreeByConstruction ≡ true

    v03RuntimeObserved : Bool
    v03RuntimeObservedIsFalse : v03RuntimeObserved ≡ false

    anchorObservationAutomaticallyResidualPayment : Bool
    anchorObservationAutomaticallyResidualPaymentIsFalse :
      anchorObservationAutomaticallyResidualPayment ≡ false

    anchorObservationAutomaticallyCitationTreatment : Bool
    anchorObservationAutomaticallyCitationTreatmentIsFalse :
      anchorObservationAutomaticallyCitationTreatment ≡ false

    anchorObservationAutomaticallyCurrentAuthority : Bool
    anchorObservationAutomaticallyCurrentAuthorityIsFalse :
      anchorObservationAutomaticallyCurrentAuthority ≡ false

canonicalFootnoteAnchorObserverRefinementBoundary :
  FootnoteAnchorObserverRefinementBoundary
canonicalFootnoteAnchorObserverRefinementBoundary =
  footnoteAnchorObserverRefinementBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data AnchorAutomaticallyPaysResidual : Set where
data AnchorAutomaticallyTreatment : Set where
data AnchorAutomaticallyAuthority : Set where
data MoreContextAutomaticallyConsumerClosure : Set where

anchorDoesNotPayResidual : AnchorAutomaticallyPaysResidual → ⊥
anchorDoesNotPayResidual ()

anchorDoesNotBecomeTreatment : AnchorAutomaticallyTreatment → ⊥
anchorDoesNotBecomeTreatment ()

anchorDoesNotBecomeAuthority : AnchorAutomaticallyAuthority → ⊥
anchorDoesNotBecomeAuthority ()

moreContextDoesNotCloseConsumer : MoreContextAutomaticallyConsumerClosure → ⊥
moreContextDoesNotCloseConsumer ()
