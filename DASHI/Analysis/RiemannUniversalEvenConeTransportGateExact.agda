module DASHI.Analysis.RiemannUniversalEvenConeTransportGateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannG2PhaseWeldCellwiseUpperBridgeExact as Upper
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as FinalCore

------------------------------------------------------------------------
-- UNIVERSAL EVEN-CONE SAME-OBJECT TRANSPORT GATE
------------------------------------------------------------------------

universalReturn : Universal.UniversalEvenConeReturn
universalReturn = Universal.canonicalUniversalEvenConeReturn

upperBoundary : Upper.PhaseWeldCellwiseUpperBridgeBoundary
upperBoundary = Upper.canonicalPhaseWeldCellwiseUpperBridgeBoundary

record UniversalEvenConeTransportCandidate : Set₁ where
  constructor universal-even-cone-transport-candidate
  field
    SourceTaper : Set
    FinalPoleQuotientTaper : Set
    sourceTaper : SourceTaper
    finalTaper : FinalPoleQuotientTaper

    sameObjectTransport : Set
    sameObjectTransportReceipt : sameObjectTransport
    transportedTaperIsSourceTaper : Set
    transportedTaperIsSourceTaperReceipt : transportedTaperIsSourceTaper

    sourceTaperNonnegative : Set
    sourceTaperNonnegativeReceipt : sourceTaperNonnegative
    sourcePoleClassKilledExactly : Set
    sourcePoleClassKilledExactlyReceipt : sourcePoleClassKilledExactly
    sourceSameOrdinateClusterPositive : Set
    sourceSameOrdinateClusterPositiveReceipt : sourceSameOrdinateClusterPositive

    finalTaperNonnegative : Set
    finalTaperNonnegativeReceipt : finalTaperNonnegative
    finalPoleClassKilledExactly : Set
    finalPoleClassKilledExactlyReceipt : finalPoleClassKilledExactly
    finalSameOrdinateClusterPositive : Set
    finalSameOrdinateClusterPositiveReceipt : finalSameOrdinateClusterPositive

    positivePartPhaseMajorantAvailable : Set
    positivePartPhaseMajorantAvailableReceipt : positivePartPhaseMajorantAvailable
open UniversalEvenConeTransportCandidate public

------------------------------------------------------------------------
-- Exact attachment compilers.
--
-- Taper identity is already one of the representation attachments consumed by
-- the final analytic-core API.  The transport candidate therefore discharges
-- that coordinate directly.  The off-ordinate attachment has an additional,
-- independent crossing-cutoff identity, so that receipt stays explicit.
------------------------------------------------------------------------

transportToGammaRepresentationAttachment :
  (candidate : UniversalEvenConeTransportCandidate) ->
  (core : FinalCore.GammaAnalyticCore) ->
  FinalCore.GammaRepresentationAttachment core
transportToGammaRepresentationAttachment candidate core = record
  { FinalCore.sameLiteralPoleQuotientTaperAsFinalConsumer =
      sameObjectTransport candidate
  ; FinalCore.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt =
      sameObjectTransportReceipt candidate
  ; FinalCore.attachmentReference =
      "universal-even-cone same-object transport -> final Gamma taper attachment"
  }

record OffCutoffAttachmentInput
    (candidate : UniversalEvenConeTransportCandidate)
    (core : FinalCore.OffAnalyticCore) : Set₁ where
  constructor off-cutoff-attachment-input
  field
    crossingCutoffFeedsThisExactOffProducer : Set
    crossingCutoffFeedsThisExactOffProducerReceipt :
      crossingCutoffFeedsThisExactOffProducer
    attachmentReference : String
open OffCutoffAttachmentInput public

transportToOffRepresentationAttachment :
  (candidate : UniversalEvenConeTransportCandidate) ->
  (core : FinalCore.OffAnalyticCore) ->
  OffCutoffAttachmentInput candidate core ->
  FinalCore.OffRepresentationAttachment core
transportToOffRepresentationAttachment candidate core cutoff = record
  { FinalCore.crossingCutoffFeedsThisExactOffProducer =
      crossingCutoffFeedsThisExactOffProducer cutoff
  ; FinalCore.crossingCutoffFeedsThisExactOffProducerReceipt =
      crossingCutoffFeedsThisExactOffProducerReceipt cutoff
  ; FinalCore.sameLiteralPoleQuotientTaperAsFinalConsumer =
      sameObjectTransport candidate
  ; FinalCore.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt =
      sameObjectTransportReceipt candidate
  ; FinalCore.attachmentReference = attachmentReference cutoff
  }

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data SourceExistenceCreatesAgdaTransport : Set where
data OEISNumericalPatternCreatesTaperTransport : Set where
data PositivePartMajorantClosesGamma : Set where
data PositivePartMajorantClosesSignedOffOrdinateTail : Set where

sourceExistenceDoesNotCreateTransport : SourceExistenceCreatesAgdaTransport -> ⊥
sourceExistenceDoesNotCreateTransport ()

oeisDoesNotCreateTaperTransport : OEISNumericalPatternCreatesTaperTransport -> ⊥
oeisDoesNotCreateTaperTransport ()

positivePartMajorantDoesNotCloseGamma : PositivePartMajorantClosesGamma -> ⊥
positivePartMajorantDoesNotCloseGamma ()

positivePartMajorantDoesNotCloseSignedTail :
  PositivePartMajorantClosesSignedOffOrdinateTail -> ⊥
positivePartMajorantDoesNotCloseSignedTail ()

record UniversalEvenConeTransportBoundary : Set where
  constructor universal-even-cone-transport-boundary
  field
    sourceUniversalTaperOwned : Bool
    sameObjectTransportInterfaceSpecified : Bool
    transportCandidateCarriesProofWitnesses : Bool
    nonnegativeTaperFeedsPositivePartMajorant : Bool
    existingOneSidedCellUpperRouteReusable : Bool
    gammaRepresentationAttachmentCompilerAvailable : Bool
    offRepresentationAttachmentUsesTransportedTaper : Bool
    offRepresentationAttachmentStillNeedsCutoffReceipt : Bool

    sameObjectTransportPaid : Bool
    positivePartMajorantAuthorityPaid : Bool
    signedOffOrdinateTailPaid : Bool
    gammaPaid : Bool

    sourceExistenceCreatesAgdaTransport : Bool
    oeisNumericalPatternCreatesTaperTransport : Bool
    positivePartMajorantClosesGamma : Bool
open UniversalEvenConeTransportBoundary public

canonicalUniversalEvenConeTransportBoundary : UniversalEvenConeTransportBoundary
canonicalUniversalEvenConeTransportBoundary =
  universal-even-cone-transport-boundary
    true true true true true
    true true true
    false false false false
    false false false
