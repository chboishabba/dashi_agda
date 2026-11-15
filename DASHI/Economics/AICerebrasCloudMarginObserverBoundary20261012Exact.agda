module DASHI.Economics.AICerebrasCloudMarginObserverBoundary20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- CEREBRAS CLOUD MARGIN OBSERVER BOUNDARY
--
-- The Q2-2026 filing pays a genuine provider accounting-margin surface for
-- "cloud and other services".  It does NOT reveal marginal inference-serving
-- cost.  Moreover the same underlying period has opposite year-over-year
-- directions under GAAP and the company's separately defined core/non-GAAP
-- observer.  Margin claims must therefore retain their accounting basis.
------------------------------------------------------------------------

secFilingKind : Source.SourceKind
secFilingKind = Source.namedSourceKind "primary SEC filing"

cerebrasQ22026Source : Source.AttributedSource
cerebrasQ22026Source = Source.mkNoDOISource
  "Cerebras Systems Inc."
  "Quarterly report for period ended June 30 2026"
  "SEC Form 10-Q"
  "2026-08-12"
  "https://www.sec.gov/Archives/edgar/data/2021728/000162828026056357/cbrs-20260630.htm"
  secFilingKind
  "primary carrier for Q2/H1 2026 cloud-and-other-services revenue, cost of revenue and GAAP gross margins, plus reconciliation to company-defined core gross margin"
  Source.publicAttribution

data MarginDirection : Set where
  up down flat unknown : MarginDirection

record MarginObserver : Set where
  constructor margin-observer
  field
    company : String
    segment : String
    accountingBasis : String
    earlierMarginBp : Nat
    laterMarginBp : Nat
    direction : MarginDirection
    accountingGrossMarginPaid : Bool
    pureInferenceSegment : Bool
    providerMarginalServingCostPaid : Bool
    marginalInferenceServingMarginPaid : Bool
    source : Source.AttributedSource

open MarginObserver public

cerebrasGaapCloudMargin : MarginObserver
cerebrasGaapCloudMargin = margin-observer
  "Cerebras"
  "cloud and other services"
  "GAAP"
  2560
  1950
  down
  true
  false
  false
  false
  cerebrasQ22026Source

cerebrasCoreCloudMargin : MarginObserver
cerebrasCoreCloudMargin = margin-observer
  "Cerebras"
  "cloud and other services"
  "company-defined core / non-GAAP"
  2600
  4180
  up
  true
  false
  false
  false
  cerebrasQ22026Source

q22026GaapCloudMarginIs1950bp :
  laterMarginBp cerebrasGaapCloudMargin ≡ 1950
q22026GaapCloudMarginIs1950bp = refl

q22026CoreCloudMarginIs4180bp :
  laterMarginBp cerebrasCoreCloudMargin ≡ 4180
q22026CoreCloudMarginIs4180bp = refl

gaapDirectionIsDown : direction cerebrasGaapCloudMargin ≡ down
gaapDirectionIsDown = refl

coreDirectionIsUp : direction cerebrasCoreCloudMargin ≡ up
coreDirectionIsUp = refl

accountingGrossMarginPaid : accountingGrossMarginPaid cerebrasGaapCloudMargin ≡ true
accountingGrossMarginPaid = refl

marginalInferenceServingMarginStillOpen :
  marginalInferenceServingMarginPaid cerebrasGaapCloudMargin ≡ false
marginalInferenceServingMarginStillOpen = refl

data AccountingGrossMarginImpliesMarginalServingMarginPermission : Set where
data CoreMarginImpliesGAAPMarginPermission : Set where
data OppositeObserverDirectionImpliesAccountingErrorPermission : Set where

accountingGrossMarginDoesNotCreateMarginalServingMargin :
  AccountingGrossMarginImpliesMarginalServingMarginPermission → ⊥
accountingGrossMarginDoesNotCreateMarginalServingMargin ()

coreMarginDoesNotReplaceGAAPMargin : CoreMarginImpliesGAAPMarginPermission → ⊥
coreMarginDoesNotReplaceGAAPMargin ()

oppositeObserverDirectionDoesNotProveAccountingError :
  OppositeObserverDirectionImpliesAccountingErrorPermission → ⊥
oppositeObserverDirectionDoesNotProveAccountingError ()

boundary : String
boundary =
  "Cerebras Q2-2026 pays a provider accounting gross-margin surface for cloud and other services: GAAP margin is 19.5 percent versus 25.6 percent in Q2-2025, while the company's core/non-GAAP margin is 41.8 percent versus 26.0 percent. The opposite year-over-year directions demonstrate accounting-observer dependence. Neither basis isolates pure inference nor reveals provider marginal serving cost, so quality-adjusted marginal inference margin remains open."
