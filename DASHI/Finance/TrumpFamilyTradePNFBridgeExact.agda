module DASHI.Finance.TrumpFamilyTradePNFBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- SOURCE -> PNF BRIDGE
--
-- PNF retains event/publication/observation time, semantic roles and revision
-- history.  This bridge requires an application-supplied exact binding between
-- a source-bounded trade claim and an EventPNF; it does not manufacture a PNF
-- parse from a filing and does not promote a candidate event into trade or legal
-- authority.
------------------------------------------------------------------------

record TradeClaimPNFBinding (claim : Atlas.TradeEvidenceClaim) : Set₁ where
  constructor trade-claim-pnf-binding
  field
    event : PNF.EventPNF
    claimEventSameObject : Set
    claimEventSameObjectReceipt : claimEventSameObject
    eventTimeBindingReference : String
    publicationTimeBindingReference : String
    entityResolutionReference : String
    propositionScopeReference : String

open TradeClaimPNFBinding public

record PointInTimeTradePNF (claim : Atlas.TradeEvidenceClaim) : Set₁ where
  constructor point-in-time-trade-pnf
  field
    binding : TradeClaimPNFBinding claim
    informationAvailableAt : String
    informationCutReference : String
    laterSourceMayRevise : Bool
    laterSourceMayReviseIsTrue : laterSourceMayRevise ≡ true

open PointInTimeTradePNF public

------------------------------------------------------------------------
-- A time-labelled PNF supports point-in-time reasoning, not hindsight import.
------------------------------------------------------------------------

record PNFInformationCut : Set₁ where
  constructor pnf-information-cut
  field
    Claim : Set
    Event : Claim → PNF.EventPNF
    admissibleAt : Claim → String → Set
    cutReference : String

open PNFInformationCut public

record SamePublicSurfaceDifferentPNFProvenance
    (left right : PNF.EventPNF) : Set₁ where
  constructor same-public-surface-different-pnf-provenance
  field
    SamePublicSurface : Set
    samePublicSurface : SamePublicSurface
    provenanceDiffers : Set
    provenanceDifference : provenanceDiffers
    differenceReference : String

open SamePublicSurfaceDifferentPNFProvenance public

------------------------------------------------------------------------
-- Firewalls.  These are particularly important for political/market material:
-- event parsing, temporal adjacency and source presence do not create hidden
-- knowledge, motive, legal findings, causal market effects, or trade authority.
------------------------------------------------------------------------

data PNFBindingAutomaticallyAdmissible : Set where
data PNFEventAutomaticallyProvesHiddenKnowledge : Set where
data PNFTemporalAdjacencyAutomaticallyProvesTradeCausation : Set where
data PNFClaimAutomaticallyCreatesTradeSignal : Set where
data PNFClaimAutomaticallyCreatesLegalFinding : Set where

pnfBindingDoesNotAutoAdmit : PNFBindingAutomaticallyAdmissible → ⊥
pnfBindingDoesNotAutoAdmit ()

pnfEventDoesNotProveHiddenKnowledge : PNFEventAutomaticallyProvesHiddenKnowledge → ⊥
pnfEventDoesNotProveHiddenKnowledge ()

temporalAdjacencyDoesNotProveTradeCausation :
  PNFTemporalAdjacencyAutomaticallyProvesTradeCausation → ⊥
temporalAdjacencyDoesNotProveTradeCausation ()

pnfClaimDoesNotCreateTradeSignal : PNFClaimAutomaticallyCreatesTradeSignal → ⊥
pnfClaimDoesNotCreateTradeSignal ()

pnfClaimDoesNotCreateLegalFinding : PNFClaimAutomaticallyCreatesLegalFinding → ⊥
pnfClaimDoesNotCreateLegalFinding ()

record TrumpFamilyTradePNFBoundary : Set where
  constructor trump-family-trade-pnf-boundary
  field
    sourceToPNFRequiresSameObjectBinding : Bool
    eventAndPublicationTimeRemainSeparate : Bool
    pointInTimeCutBlocksHindsightImport : Bool
    pnfDoesNotCreateHiddenKnowledge : Bool
    pnfDoesNotCreateTradeSignal : Bool
    pnfDoesNotCreateLegalFinding : Bool

canonicalTrumpFamilyTradePNFBoundary : TrumpFamilyTradePNFBoundary
canonicalTrumpFamilyTradePNFBoundary =
  trump-family-trade-pnf-boundary true true true true true true
