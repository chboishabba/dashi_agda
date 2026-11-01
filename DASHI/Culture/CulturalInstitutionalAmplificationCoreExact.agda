module DASHI.Culture.CulturalInstitutionalAmplificationCoreExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- CULTURAL INSTITUTIONAL AMPLIFICATION CORE
--
-- Production, institutional selection, funding, circulation and reception are
-- separate typed strata.  The core deliberately contains no historical CIA,
-- MoMA, CCF, artist or exhibition facts.
------------------------------------------------------------------------

postulate
  Work Institution Funder Venue Audience HistoricalTime : Set

record ProductionReceipt (work : Work) : Set where
  constructor production-receipt

record InstitutionalSelection (institution : Institution) (work : Work) : Set where
  constructor institutional-selection

record FundingReceipt (funder : Funder) (institution : Institution) : Set where
  constructor funding-receipt

record CirculationReceipt
    (institution : Institution)
    (work : Work)
    (venue : Venue)
    (time : HistoricalTime) : Set where
  constructor circulation-receipt

record ReceptionReceipt
    (work : Work)
    (audience : Audience) : Set where
  constructor reception-receipt

record AmplificationEvent (work : Work) : Set₁ where
  constructor amplification-event
  field
    institution : Institution
    funder : Funder
    venue : Venue
    audience : Audience
    time : HistoricalTime
    selected : InstitutionalSelection institution work
    funded : FundingReceipt funder institution
    circulated : CirculationReceipt institution work venue time
    received : ReceptionReceipt work audience

open AmplificationEvent public

------------------------------------------------------------------------
-- No-promotion boundaries.
------------------------------------------------------------------------

data FundingCreatesProduction (funder : Funder) (work : Work) : Set where

data SelectionCreatesProduction (institution : Institution) (work : Work) : Set where

data ReceptionCreatesProduction (audience : Audience) (work : Work) : Set where

data AmplificationCreatesProduction (work : Work) : Set where

fundingDoesNotCreateProduction :
  ∀ {funder work} → FundingCreatesProduction funder work → ⊥
fundingDoesNotCreateProduction ()

selectionDoesNotCreateProduction :
  ∀ {institution work} → SelectionCreatesProduction institution work → ⊥
selectionDoesNotCreateProduction ()

receptionDoesNotCreateProduction :
  ∀ {audience work} → ReceptionCreatesProduction audience work → ⊥
receptionDoesNotCreateProduction ()

amplificationDoesNotCreateProduction :
  ∀ {work} → AmplificationCreatesProduction work → ⊥
amplificationDoesNotCreateProduction ()

------------------------------------------------------------------------
-- A selected work can be institutionally amplified without claiming that the
-- institution or funder produced it.
------------------------------------------------------------------------

record IndependentlyProducedAndAmplified (work : Work) : Set₁ where
  constructor independently-produced-and-amplified
  field
    production : ProductionReceipt work
    amplification : AmplificationEvent work

open IndependentlyProducedAndAmplified public

record CulturalInstitutionalAmplificationBoundary : Set where
  constructor cultural-institutional-amplification-boundary
  field
    productionSelectionFundingCirculationReceptionAreTyped : Bool
    amplificationCanCoexistWithIndependentProduction : Bool
    fundingAutomaticallyCreatesProduction : Bool
    selectionAutomaticallyCreatesProduction : Bool
    receptionAutomaticallyCreatesProduction : Bool

canonicalCulturalInstitutionalAmplificationBoundary :
  CulturalInstitutionalAmplificationBoundary
canonicalCulturalInstitutionalAmplificationBoundary =
  cultural-institutional-amplification-boundary
    true true false false false
