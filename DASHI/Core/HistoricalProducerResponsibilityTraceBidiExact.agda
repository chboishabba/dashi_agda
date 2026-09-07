module DASHI.Core.HistoricalProducerResponsibilityTraceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.HistoricalFirstFailureTraceBidiExact as History
import DASHI.Core.QueryPromotionResidualBidiExact as QueryPromotion
import DASHI.Core.TemporalStrandProvenanceBidiExact as Strand
import DASHI.Core.BraidedEvidenceTraceBidiCrossPollination2026Exact as Braid

------------------------------------------------------------------------
-- HISTORICAL FIRST FAILURE -> PRODUCER RESPONSIBILITY TRACE
--
-- A historical residual identifies which promotion obligation was first open.
-- This owner adds the typed provenance strand and producer kind responsible for
-- paying that obligation at that historical snapshot.  Responsibility here is
-- proof/work responsibility only; it is not blame, legal liability, or action
-- authority.
------------------------------------------------------------------------

data ResponsibilityTarget : Set where
  responsible : Strand.StrandObligation → ResponsibilityTarget
  noResponsibility : ResponsibilityTarget

responsibilityForResidual : QueryPromotion.PromotionResidual → ResponsibilityTarget
responsibilityForResidual QueryPromotion.missingArtifact =
  responsible Strand.artifactObligation
responsibilityForResidual QueryPromotion.missingCorrespondence =
  responsible Strand.correspondenceObligation
responsibilityForResidual QueryPromotion.missingTransport =
  responsible Strand.transportObligation
responsibilityForResidual QueryPromotion.missingTargetInhabitance =
  responsible Strand.inhabitanceObligation
responsibilityForResidual QueryPromotion.promotionClosed = noResponsibility

record HistoricalProducerResponsibility
    (snapshot : History.HistoricalPromotionSnapshot) : Set₁ where
  constructor historical-producer-responsibility
  field
    target : ResponsibilityTarget
    targetMatchesResidual :
      target ≡ responsibilityForResidual (History.firstResidual snapshot)
    producerKind : QueryPromotion.ProducerKind
    producerMatchesResidual :
      producerKind ≡ QueryPromotion.producerFor (History.firstResidual snapshot)
    responsibleStrand : Braid.EvidenceStrand
    producerReceiptReference : String
    responsibilityReading : String

open HistoricalProducerResponsibility public

------------------------------------------------------------------------
-- Exact earlier calibration: the historical first failure is transport, so the
-- work target is the transport obligation and the required producer kind is
-- `proveTransport`.
------------------------------------------------------------------------

earlierTransportResponsibility :
  HistoricalProducerResponsibility History.earlierMissingTransport
earlierTransportResponsibility =
  historical-producer-responsibility
    (responsible Strand.transportObligation)
    refl
    QueryPromotion.proveTransport
    refl
    Strand.transportStrand
    "historical transport-stage producer receipt"
    "at the earlier snapshot the first unpaid promotion obligation is transport"

earlierResponsibilityTargetsTransport :
  target earlierTransportResponsibility ≡ responsible Strand.transportObligation
earlierResponsibilityTargetsTransport = refl

earlierResponsibilitySelectsTransportProducer :
  producerKind earlierTransportResponsibility ≡ QueryPromotion.proveTransport
earlierResponsibilitySelectsTransportProducer = refl

------------------------------------------------------------------------
-- A later closed state has no current producer responsibility.  This does not
-- rewrite the typed earlier responsibility trace.
------------------------------------------------------------------------

closedStateHasNoResponsibilityTarget :
  responsibilityForResidual (History.firstResidual History.laterPromotionClosed)
  ≡ noResponsibility
closedStateHasNoResponsibilityTarget = refl

data LaterClosureErasesHistoricalProducerResponsibility : Set where
data ProducerResponsibilityMeansBlameOrLiability : Set where
data ProducerKindCreatesProducerReceipt : Set where

laterClosureDoesNotEraseHistoricalResponsibility :
  LaterClosureErasesHistoricalProducerResponsibility → ⊥
laterClosureDoesNotEraseHistoricalResponsibility ()

producerResponsibilityDoesNotMeanBlameOrLiability :
  ProducerResponsibilityMeansBlameOrLiability → ⊥
producerResponsibilityDoesNotMeanBlameOrLiability ()

producerKindDoesNotCreateProducerReceipt : ProducerKindCreatesProducerReceipt → ⊥
producerKindDoesNotCreateProducerReceipt ()

record HistoricalProducerResponsibilityBoundary : Set where
  constructor historical-producer-responsibility-boundary
  field
    firstFailureDeterminesObligationClass : Bool
    firstFailureDeterminesProducerKind : Bool
    responsibilityIsTimeIndexed : Bool
    laterClosureRewritesEarlierResponsibility : Bool
    responsibilityImpliesBlameOrLiability : Bool

canonicalHistoricalProducerResponsibilityBoundary :
  HistoricalProducerResponsibilityBoundary
canonicalHistoricalProducerResponsibilityBoundary =
  historical-producer-responsibility-boundary true true true false false
