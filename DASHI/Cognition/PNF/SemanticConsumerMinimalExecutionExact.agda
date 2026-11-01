module DASHI.Cognition.PNF.SemanticConsumerMinimalExecutionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Cognition.PNF.BracketedTSFVFractranWorldFibreExact as World
import DASHI.Foundations.SSPTritCarrier as Trit

------------------------------------------------------------------------
-- SSSP cross-pollination: do not choose a complete semantic world merely
-- because the fine carrier contains one.  Execute only the quotient demanded
-- by the current consumer, retaining the hidden world fibre losslessly.
------------------------------------------------------------------------

record ConsumerRequest : Set where
  constructor consumerRequest
  field
    query : Context.QueryFrame
    requestedObservation : Context.RequestedPrimeObservation

open ConsumerRequest public

record ConsumerMinimalTokenState : Set where
  constructor consumerMinimalTokenState
  field
    request : ConsumerRequest
    visible : Trit.SSPTrit
    residualWorlds : List World.WorldHistory
    residualOptions : List World.StratifiedOption
    stratum : World.Stratum
    bracket : World.Bracket

open ConsumerMinimalTokenState public

record FineWorldProjection : Set₁ where
  constructor fineWorldProjection
  field
    FineWorld : Set
    observe : FineWorld → Trit.SSPTrit
    retainWorld : FineWorld → World.WorldHistory

open FineWorldProjection public

record SameConsumerObservation
    (projection : FineWorldProjection)
    (left right : FineWorld projection)
    : Set where
  constructor sameConsumerObservation
  field
    observationAgrees : observe projection left ≡ observe projection right

open SameConsumerObservation public

record RetainedResidualPair
    (projection : FineWorldProjection)
    (left right : FineWorld projection)
    : Set where
  constructor retainedResidualPair
  field
    sameObservation : SameConsumerObservation projection left right
    leftHistory : World.WorldHistory
    rightHistory : World.WorldHistory
    leftRetained : leftHistory ≡ retainWorld projection left
    rightRetained : rightHistory ≡ retainWorld projection right

open RetainedResidualPair public

-- Refinement never requires reconstruction of the source document.  A new
-- discriminator consumes the retained fibre and may expose a stricter coarse
-- observation while carrying the old residual forward.
record ResidualRefinement : Set₁ where
  constructor residualRefinement
  field
    before : ConsumerMinimalTokenState
    after : ConsumerMinimalTokenState
    discriminatorAvailable : Bool
    oldWorldsRetainedForAudit : List World.WorldHistory
    oldOptionsRetainedForAudit : List World.StratifiedOption

open ResidualRefinement public

record ConsumerMinimalBoundary : Set where
  constructor consumerMinimalBoundary
  field
    completeWorldRequiredBeforeExecution : Bool
    equalObservationErasesResidual : Bool
    laterPredicateMaySplitExistingFibre : Bool
    residualRefinementRequiresDocumentRebuild : Bool
    consumerQuotientIsExecutionState : Bool

canonicalConsumerMinimalBoundary : ConsumerMinimalBoundary
canonicalConsumerMinimalBoundary =
  consumerMinimalBoundary false false true false true
