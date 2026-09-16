module DASHI.Finance.TrumpFamilyTradeStrategicIdentificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.GameTheory.StrategicExperimentalIdentificationFibreExact as Identify
import DASHI.Finance.TrumpFamilyTradeSourceAtlas2026SupplementExact as SourceAtlas

------------------------------------------------------------------------
-- EXACT IDENTIFICATION COLLISION
--
-- A perfectly observed, source-paid transaction does not identify the latent
-- information state that generated it.  This is an abstract finite collision,
-- not a claim that either latent model describes any named person.
------------------------------------------------------------------------

data LatentInformationModel : Set where
  publicInformationOnly : LatentInformationModel
  additionalInformationAvailable : LatentInformationModel

data TransactionObservation : Set where
  observedOGENvidiaSale : TransactionObservation

data TradeIdentificationQuery : Set where
  informationStateQuery : TradeIdentificationQuery

data InformationStateAnswer : Set where
  publicOnlyAnswer : InformationStateAnswer
  additionalInformationAnswer : InformationStateAnswer

observeTransaction : LatentInformationModel → TransactionObservation
observeTransaction publicInformationOnly = observedOGENvidiaSale
observeTransaction additionalInformationAvailable = observedOGENvidiaSale

answerInformationState :
  TradeIdentificationQuery → LatentInformationModel → InformationStateAnswer
answerInformationState informationStateQuery publicInformationOnly = publicOnlyAnswer
answerInformationState informationStateQuery additionalInformationAvailable =
  additionalInformationAnswer

transactionIdentificationSurface : Identify.StrategicIdentificationSurface
transactionIdentificationSurface =
  Identify.strategic-identification-surface
    LatentInformationModel
    TransactionObservation
    TradeIdentificationQuery
    InformationStateAnswer
    observeTransaction
    answerInformationState
    "abstract latent-information alternatives compatible with one observed transaction"
    "source-paid OGE transaction surface; canonical documentary anchor: Trump-2026-OGE-278T-NVDA-sale-2026-03-06"
    "consumer asks which latent information model generated the observation"

informationAnswersDiffer :
  publicOnlyAnswer ≡ additionalInformationAnswer → ⊥
informationAnswersDiffer ()

sameObservedTransactionDifferentInformationState :
  Identify.SameObservedPlayDifferentStrategicAnswer
    transactionIdentificationSurface
    informationStateQuery
sameObservedTransactionDifferentInformationState =
  Identify.same-observed-play-different-strategic-answer
    publicInformationOnly
    additionalInformationAvailable
    refl
    informationAnswersDiffer

transactionObservationHasInformationIdentificationDefect :
  Identify.StrategicIdentificationDefect
    transactionIdentificationSurface
    informationStateQuery
transactionObservationHasInformationIdentificationDefect =
  Identify.observationCollisionCreatesIdentificationDefect
    sameObservedTransactionDifferentInformationState

transactionObservationCannotIdentifyInformationState :
  Identify.IdentifiedForQuery
      transactionIdentificationSurface
      informationStateQuery
  → ⊥
transactionObservationCannotIdentifyInformationState =
  Identify.identificationDefectBlocksIdentification
    transactionObservationHasInformationIdentificationDefect

------------------------------------------------------------------------
-- Keep the empirical anchor and the abstract collision in separate authority
-- layers.  The exact source record establishes a transaction; the collision
-- establishes a non-identifiability theorem about what that observation alone
-- can recover.
------------------------------------------------------------------------

sourceAnchor : SourceAtlas.Atlas.TradeEvidenceClaim
sourceAnchor = SourceAtlas.trumpOGE278TNvidiaSale

record TrumpFamilyTradeStrategicIdentificationBoundary : Set where
  constructor trump-family-trade-strategic-identification-boundary
  field
    transactionObservationCanBeExact : Bool
    exactTransactionDoesNotIdentifyInformationState : Bool
    informationCollisionIsAbstractNotBiographical : Bool
    modelCompatibilityDoesNotProveHistoricalIntent : Bool
    additionalEvidenceMayRefineSelectedQuery : Bool

canonicalTrumpFamilyTradeStrategicIdentificationBoundary :
  TrumpFamilyTradeStrategicIdentificationBoundary
canonicalTrumpFamilyTradeStrategicIdentificationBoundary =
  trump-family-trade-strategic-identification-boundary true true true true true
