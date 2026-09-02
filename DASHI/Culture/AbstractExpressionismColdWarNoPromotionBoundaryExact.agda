module DASHI.Culture.AbstractExpressionismColdWarNoPromotionBoundaryExact where

open import DASHI.Core.Prelude

import DASHI.Culture.CulturalInstitutionalAmplificationCoreExact as Core
import DASHI.Culture.CulturalColdWarFundingProvenanceSameObjectBidiExact as Provenance

------------------------------------------------------------------------
-- ABSTRACT EXPRESSIONISM / COLD WAR CLAIM STRATA
--
-- This owner types historiographical claim strength.  It deliberately does not
-- instantiate named historical actors or exhibitions; those require separately
-- sourced receipts.
------------------------------------------------------------------------

record AbstractExpressionistWork (work : Core.Work) : Set where
  constructor abstract-expressionist-work

record FreedomContrastReception
    (work : Core.Work)
    (audience : Core.Audience) : Set where
  constructor freedom-contrast-reception

record PoliticallyUsefulReception (work : Core.Work) : Set₁ where
  constructor politically-useful-reception
  field
    audience : Core.Audience
    reception : Core.ReceptionReceipt work audience
    freedomContrast : FreedomContrastReception work audience

open PoliticallyUsefulReception public

record CovertlyFundedAmplification (work : Core.Work) : Set₁ where
  constructor covertly-funded-amplification
  field
    amplification : Core.AmplificationEvent work
    sourceActor targetActor : Provenance.HistoricalActor
    covertPath : Provenance.ProvenancePath sourceActor targetActor

open CovertlyFundedAmplification public

record ColdWarCulturalUse (work : Core.Work) : Set₁ where
  constructor cold-war-cultural-use
  field
    abstractExpressionist : AbstractExpressionistWork work
    amplified : CovertlyFundedAmplification work
    politicallyUseful : PoliticallyUsefulReception work

open ColdWarCulturalUse public

------------------------------------------------------------------------
-- Stronger claims require independent evidence and do not follow from cultural
-- use, covert amplification, or ideological usefulness.
------------------------------------------------------------------------

data StateSelectedExactWork (work : Core.Work) : Set where

data StateDirectedProduction (work : Core.Work) : Set where

data ArtistKnewCovertSponsor (work : Core.Work) : Set where

data StateCreatedArtMovement : Set where

data IdeologicalUseCreatesOriginalMeaning (work : Core.Work) : Set where

coldWarUseDoesNotCreateStateSelection :
  ∀ {work} → ColdWarCulturalUse work → StateSelectedExactWork work → ⊥
coldWarUseDoesNotCreateStateSelection use ()

covertAmplificationDoesNotCreateDirectedProduction :
  ∀ {work} → CovertlyFundedAmplification work → StateDirectedProduction work → ⊥
covertAmplificationDoesNotCreateDirectedProduction amplified ()

covertAmplificationDoesNotCreateArtistKnowledge :
  ∀ {work} → CovertlyFundedAmplification work → ArtistKnewCovertSponsor work → ⊥
covertAmplificationDoesNotCreateArtistKnowledge amplified ()

coldWarUseDoesNotCreateArtMovement :
  ∀ {work} → ColdWarCulturalUse work → StateCreatedArtMovement → ⊥
coldWarUseDoesNotCreateArtMovement use ()

politicalUseDoesNotCreateOriginalMeaning :
  ∀ {work} → PoliticallyUsefulReception work →
  IdeologicalUseCreatesOriginalMeaning work → ⊥
politicalUseDoesNotCreateOriginalMeaning useful ()

------------------------------------------------------------------------
-- The positive theorem: independent production and covert amplification are
-- jointly coherent because they inhabit distinct coordinates.
------------------------------------------------------------------------

record IndependentProductionWithColdWarUse (work : Core.Work) : Set₁ where
  constructor independent-production-with-cold-war-use
  field
    production : Core.ProductionReceipt work
    use : ColdWarCulturalUse work

open IndependentProductionWithColdWarUse public

record AbstractExpressionismColdWarNoPromotionBoundary : Set where
  constructor abstract-expressionism-cold-war-no-promotion-boundary
  field
    productionAndAmplificationCanCoexist : Bool
    ideologicalUseIsReceptionIndexed : Bool
    covertAmplificationAutomaticallyMeansStateSelection : Bool
    covertAmplificationAutomaticallyMeansDirectedProduction : Bool
    covertAmplificationAutomaticallyMeansArtistKnowledge : Bool
    coldWarUseAutomaticallyMeansStateCreatedMovement : Bool
    politicalUseAutomaticallyCreatesOriginalMeaning : Bool
    namedHistoricalInstantiationRequiresSeparateReceipts : Bool

canonicalAbstractExpressionismColdWarNoPromotionBoundary :
  AbstractExpressionismColdWarNoPromotionBoundary
canonicalAbstractExpressionismColdWarNoPromotionBoundary =
  abstract-expressionism-cold-war-no-promotion-boundary
    true true false false false false false true
