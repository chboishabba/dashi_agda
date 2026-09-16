module DASHI.Cognition.PNF.SensibLawTranscriptBoundaryFibreBroadcastValidationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawTranscriptBoundaryFibreClassifierExact as Fibre
import DASHI.Cognition.PNF.SensibLawTranscriptBoundaryFibreBroadcastGraphExact as Broadcast
import DASHI.Cognition.PNF.SensibLawTranscriptSpeakerResolutionExact as Speaker
import DASHI.Cognition.PNF.SensibLawAttributionPropositionOccurrenceBidiExact as Attribution
import DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact as Consumer

------------------------------------------------------------------------
-- Narrow validation root for transcript-wide fibre broadcasting.
------------------------------------------------------------------------

speakerRouteExact :
  Broadcast.routeFor Fibre.speakerCut ≡ Broadcast.speakerResolutionRoute
speakerRouteExact = refl

quoteRouteExact :
  Broadcast.routeFor Fibre.reporterQuoteHandoff ≡ Broadcast.reporterQuoteFrameRoute
quoteRouteExact = refl

nestingRouteExact :
  Broadcast.routeFor Fibre.attributionNesting ≡ Broadcast.attributionModalWrapperRoute
nestingRouteExact = refl

asrRouteExact :
  Broadcast.routeFor Fibre.asrDamage ≡ Broadcast.transcriptRepairRoute
asrRouteExact = refl

rhetoricalRouteExact :
  Broadcast.routeFor Fibre.rhetoricalPivot ≡ Broadcast.contrastConcessionRoute
rhetoricalRouteExact = refl

speakerCarrierOwner : Set
speakerCarrierOwner = Speaker.SpeakerResolutionPacket

consumerCandidateOwner : Set
consumerCandidateOwner = Consumer.DiscourseActCandidate

classifierBoundaryRetained : Fibre.FibreClassifierBoundary
classifierBoundaryRetained = Fibre.canonicalFibreClassifierBoundary

broadcastBoundaryRetained : Broadcast.FibreBroadcastBoundary
broadcastBoundaryRetained = Broadcast.canonicalFibreBroadcastBoundary

attributionTruthFirewall : Attribution.ClaimAssertionIsTruthProof → ⊥
attributionTruthFirewall = Attribution.claimAssertionDoesNotProveTruth
