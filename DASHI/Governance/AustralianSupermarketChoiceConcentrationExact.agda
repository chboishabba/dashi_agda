module DASHI.Governance.AustralianSupermarketChoiceConcentrationExact where

------------------------------------------------------------------------
-- AUSTRALIAN SUPERMARKET CONCENTRATION ADAPTER
--
-- Primary public source:
-- Australian Competition and Consumer Commission (ACCC),
-- Supermarkets Inquiry / competition-priorities material, 2024-2025.
-- Title used for the bounded receipt here:
-- "ACCC's compliance and enforcement priorities update 2025-26 address".
-- Institution/author: Australian Competition and Consumer Commission.
-- No DOI asserted.
--
-- The ACCC states that the retail level of Australia's supermarket industry is
-- highly concentrated and estimates Coles + Woolworths at approximately 67%
-- of national supermarket retail sales (FY2023 basis), while ALDI, Coles,
-- Woolworths and Metcash together account for approximately 83%.
--
-- Source role: concentration / market-structure evidence only.  These figures
-- do not by themselves establish coercion, collusion, unlawful conduct,
-- consumer entrapment, or identical substitution conditions for every buyer,
-- supplier, worker, town or product category.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.EffectiveChoiceConcentrationExact as Concentration

record PublicMarketReceipt : Set where
  constructor publicMarketReceipt
  field
    institution : String
    title : String
    year : Nat
    doi : String
    boundedRole : String

open PublicMarketReceipt public

acccSupermarketReceipt : PublicMarketReceipt
acccSupermarketReceipt = publicMarketReceipt
  "Australian Competition and Consumer Commission"
  "ACCC's compliance and enforcement priorities update 2025-26 address"
  2025
  "no DOI asserted"
  "supports a highly concentrated supermarket-retail structure and approximate aggregate sales shares; does not itself establish coercion, collusion or a universal effective duopoly"

------------------------------------------------------------------------
-- The source supports concentration, not a literal theorem that only two
-- supermarket actors exist.
------------------------------------------------------------------------

colesWoolworthsApproxShare : Nat
colesWoolworthsApproxShare = 67

largestFourApproxShare : Nat
largestFourApproxShare = 83

australianSupermarketField : Concentration.EffectiveChoiceField
australianSupermarketField = Concentration.effectiveChoiceField
  4
  4
  2
  colesWoolworthsApproxShare
  1
  2
  3
  Concentration.concentratedPlural

record SupermarketObserverGeometry : Set where
  constructor supermarketObserverGeometry
  field
    consumerProjection : Concentration.ObserverChoiceProjection
    supplierProjection : Concentration.ObserverChoiceProjection
    workerProjection : Concentration.ObserverChoiceProjection

open SupermarketObserverGeometry public

canonicalSupermarketObserverGeometry : SupermarketObserverGeometry
canonicalSupermarketObserverGeometry = supermarketObserverGeometry
  (Concentration.observerChoiceProjection Concentration.consumerObserver 4 4)
  (Concentration.observerChoiceProjection Concentration.supplierObserver 4 2)
  (Concentration.observerChoiceProjection Concentration.workerObserver 4 3)

------------------------------------------------------------------------
-- The projection numbers above are a finite DASHI witness illustrating that
-- observer-relative substitutability can differ.  They are not empirical ACCC
-- estimates of supplier/worker option counts.
------------------------------------------------------------------------

data AustralianConcentrationPromotesLiteralDuopoly : Set where

data AustralianConcentrationPromotesCoercion : Set where

data ConsumerOptionsDetermineSupplierOptions : Set where

concentrationDoesNotPromoteLiteralDuopoly :
  AustralianConcentrationPromotesLiteralDuopoly → ⊥
concentrationDoesNotPromoteLiteralDuopoly ()

concentrationDoesNotPromoteCoercion :
  AustralianConcentrationPromotesCoercion → ⊥
concentrationDoesNotPromoteCoercion ()

consumerOptionsDoNotDetermineSupplierOptions :
  ConsumerOptionsDetermineSupplierOptions → ⊥
consumerOptionsDoNotDetermineSupplierOptions ()

record AustralianSupermarketChoiceBoundary : Set where
  constructor australianSupermarketChoiceBoundary
  field
    acccConcentrationReceiptInstalled : Bool
    dominantPairShareEqualsLiteralDuopoly : Bool
    concentratedRetailEqualsCoercion : Bool
    observerRelativeSubstitutabilityRetained : Bool
    finiteObserverCountsAreEmpiricalClaims : Bool

canonicalAustralianSupermarketChoiceBoundary :
  AustralianSupermarketChoiceBoundary
canonicalAustralianSupermarketChoiceBoundary =
  australianSupermarketChoiceBoundary true false false true false
