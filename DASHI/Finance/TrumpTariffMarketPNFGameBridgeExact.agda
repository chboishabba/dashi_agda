module DASHI.Finance.TrumpTariffMarketPNFGameBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Finance.TrumpTariffMarketSignalSourceExact as SourceAtlas
import DASHI.GameTheory.StrategicInteractionCoreExact as Game
import DASHI.GameTheory.FiniteIncompleteInformationBayesianExact as Bayesian
import DASHI.GameTheory.SourceConditionedMarketInformationExact as Information

record TariffClaimPNFBinding (claim : SourceAtlas.TariffMarketClaim) : Set₁ where
  constructor tariff-claim-pnf-binding
  field
    event : PNF.EventPNF
    SameObject : Set
    sameObjectReceipt : SameObject
    eventTimeBindingReference publicationTimeBindingReference propositionScopeReference : String
open TariffClaimPNFBinding public

record TariffSequencePNF : Set₁ where
  constructor tariff-sequence-pnf
  field
    signalBinding : TariffClaimPNFBinding SourceAtlas.buyPost
    policyBinding : TariffClaimPNFBinding SourceAtlas.tariffPauseAnnouncement
    marketBinding : TariffClaimPNFBinding SourceAtlas.marketRally
    sequenceReference : String
open TariffSequencePNF public

record TariffBayesianInformationBridge
    {G : Game.StrategicGame}
    (B : Bayesian.FiniteBayesianGame G)
    (I : Information.SourceConditionedInformation B) : Set₁ where
  constructor tariff-bayesian-information-bridge
  field
    sourceSequence : SourceAtlas.PublicSequence
    pnfSequence : TariffSequencePNF
    publicSignalModelReference sourceEvidenceStateReference : String
    sequenceDeterminesPrior : Bool
    sequenceDeterminesPriorIsFalse : sequenceDeterminesPrior ≡ false
    sequenceRevealsHiddenType : Bool
    sequenceRevealsHiddenTypeIsFalse : sequenceRevealsHiddenType ≡ false
    sequenceRevealsMotive : Bool
    sequenceRevealsMotiveIsFalse : sequenceRevealsMotive ≡ false
open TariffBayesianInformationBridge public

data InformationCut : Set where
  beforeBuyPost : InformationCut
  afterBuyBeforePause : InformationCut
  afterPauseBeforeClose : InformationCut
  afterMarketClose : InformationCut
  laterDocumentaryReview : InformationCut

record PublicClaimAvailability : Set where
  constructor public-claim-availability
  field
    claim : SourceAtlas.TariffMarketClaim
    firstAvailableCut : InformationCut
    availabilityReference : String
open PublicClaimAvailability public

buyPostAvailability : PublicClaimAvailability
buyPostAvailability = public-claim-availability SourceAtlas.buyPost afterBuyBeforePause "09:37 ET public post may enter public evidence only from the post onward"
tariffPauseAvailability : PublicClaimAvailability
tariffPauseAvailability = public-claim-availability SourceAtlas.tariffPauseAnnouncement afterPauseBeforeClose "13:18 ET public policy announcement may enter public evidence only from the announcement onward"
marketOutcomeAvailability : PublicClaimAvailability
marketOutcomeAvailability = public-claim-availability SourceAtlas.marketRally afterMarketClose "closing-session outcome is not available as a completed observation before the close"

data LaterEvidenceMayPopulateEarlierInformationSet : Set where
data MarketResponseAutomaticallyRevealsPrivateSignal : Set where
data BayesianCompatibilityAutomaticallyRevealsMotive : Set where
laterEvidenceCannotBeBackdated : LaterEvidenceMayPopulateEarlierInformationSet → ⊥
laterEvidenceCannotBeBackdated ()
marketResponseDoesNotRevealPrivateSignal : MarketResponseAutomaticallyRevealsPrivateSignal → ⊥
marketResponseDoesNotRevealPrivateSignal ()
bayesianCompatibilityDoesNotRevealMotive : BayesianCompatibilityAutomaticallyRevealsMotive → ⊥
bayesianCompatibilityDoesNotRevealMotive ()

record TariffPNFGameBoundary : Set where
  constructor tariff-pnf-game-boundary
  field
    PNFRequiresSameObjectBinding : Bool
    eventPublicationAndObservationTimeRemainSeparate : Bool
    publicSignalAndSourceEvidenceRemainSeparate : Bool
    laterEvidenceCannotBeBackdated : Bool
    marketResponseDoesNotRevealHiddenType : Bool
    equilibriumCompatibilityDoesNotRevealMotive : Bool

canonicalTariffPNFGameBoundary : TariffPNFGameBoundary
canonicalTariffPNFGameBoundary = tariff-pnf-game-boundary true true true true true true
