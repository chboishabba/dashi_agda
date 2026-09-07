module DASHI.Cognition.PNF.SensibLawHerzogUniversalLegalCrossPollinationEverything where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.HerzogUniversalLegalAlgebraEverything as Herzog
import DASHI.Law.HerzogUniversalLegalEvidenceBridgeExact as Bridge
import DASHI.Law.SecurityClassificationInputLineageDagExact as Lineage
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as Residual

------------------------------------------------------------------------
-- Legal algebra consumes Herzog evidence as typed facts/residuals without
-- promoting police/security classification into legal authority.
------------------------------------------------------------------------

postHocNarrativeDoesNotReachPreActionClassification :
  Search.reachable 1 Bridge.currentHerzogGraph Bridge.currentHerzogFacts
    Bridge.preActionClassificationContentEstablished ≡ false
postHocNarrativeDoesNotReachPreActionClassification =
  Herzog.currentHerzogClassificationContentRemainsOpen

postHocNarrativeDoesNotReachLegalQualification :
  Search.reachable 1 Bridge.currentHerzogGraph Bridge.currentHerzogFacts
    Bridge.legalQualificationOfClassification ≡ false
postHocNarrativeDoesNotReachLegalQualification =
  Herzog.currentHerzogLegalQualificationRemainsOpen

classificationLineageResidualReopensEvidence :
  Residual.preferredRoute
    (Bridge.lineageResidualKind Lineage.classificationContentResidual)
  ≡ Residual.obtainFactualEvidence
classificationLineageResidualReopensEvidence = refl

producerCarrierResidualReopensProvenance :
  Residual.preferredRoute
    (Bridge.lineageResidualKind Lineage.carrierContentResidual)
  ≡ Residual.askSituatedHolder
producerCarrierResidualReopensProvenance = refl

incidentIdentityStillNotCausalAttribution :
  Bridge.SameIncidentCreatesCausalContribution → ⊥
incidentIdentityStillNotCausalAttribution = Bridge.sameIncidentDoesNotCreateCausation

causalContributionStillNotLegalAttribution :
  Bridge.CausalContributionCreatesLegalAttribution → ⊥
causalContributionStillNotLegalAttribution = Bridge.causationDoesNotCreateLegalAttribution

legalAttributionStillNotLiability :
  Bridge.LegalAttributionAutomaticallyCreatesLiability → ⊥
legalAttributionStillNotLiability = Bridge.attributionDoesNotAutomaticallyCreateLiability

securityClassificationStillNotCourtHolding :
  Bridge.SecurityClassificationIsCourtHolding → ⊥
securityClassificationStillNotCourtHolding = Bridge.classificationDoesNotBecomeCourtHolding

------------------------------------------------------------------------
-- This adapter is intended to be extended by the full #756 multi-source join:
-- document multiplicity, ultimate-producer independence, classification use,
-- incident same-object use, Country/self-determination content and legal
-- qualification are independent coordinates. None is reconstructed here from
-- the others.
------------------------------------------------------------------------

data HerzogCrossPollinationAggregateMeansCorpusComplete : Set where
aggregateDoesNotClaimCorpusCompleteness :
  HerzogCrossPollinationAggregateMeansCorpusComplete → ⊥
aggregateDoesNotClaimCorpusCompleteness ()
