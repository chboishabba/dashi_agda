module DASHI.Economics.WealthInheritanceVacancyTaxMaxCut20261027Exact where

-- Tax-policy base separation and finite counterexamples, 2026-10-27.
-- Original historical/empirical sources retain authorship.  DASHI's typed
-- policy split and small arithmetic witnesses are source-written formal work:
-- Johl Brown (research direction) with OpenAI ChatGPT assistance.
-- No aggregate economic effect, legislative status or universal causal claim
-- is inferred from definitional equality or finite arithmetic.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_∸_)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- TAX BASES: A SIMILAR NUMBER OR BENEFICIARY DOES NOT COLLAPSE POLICY.
------------------------------------------------------------------------

data TaxBase : Set where
  annualPersonalIncome : TaxBase
  currentNetWealth : TaxBase
  wealthTransferredAtDeath : TaxBase
  statusOfVacantResidentialProperty : TaxBase
  gainsRealisedOnSale : TaxBase
  annualChangeInAssetValue : TaxBase
  collateralisedLoanProceeds : TaxBase

data Policy : Set where
  incomeHundredAboveThreshold : Policy
  wealthHundredAboveThreshold : Policy
  recurringNetWealthLevy : Policy
  inheritanceTransferLevy : Policy
  vacantHomesStatusLevy : Policy
  realisedGainsLevy : Policy
  markToMarketGainsLevy : Policy

taxBase : Policy → TaxBase
taxBase incomeHundredAboveThreshold = annualPersonalIncome
taxBase wealthHundredAboveThreshold = currentNetWealth
taxBase recurringNetWealthLevy = currentNetWealth
taxBase inheritanceTransferLevy = wealthTransferredAtDeath
taxBase vacantHomesStatusLevy = statusOfVacantResidentialProperty
taxBase realisedGainsLevy = gainsRealisedOnSale
taxBase markToMarketGainsLevy = annualChangeInAssetValue

incomeTaxIsNotStockCap :
  incomeHundredAboveThreshold ≡ wealthHundredAboveThreshold → ⊥
incomeTaxIsNotStockCap ()

vacancyTaxIsNotWealthCap :
  vacantHomesStatusLevy ≡ wealthHundredAboveThreshold → ⊥
vacancyTaxIsNotWealthCap ()

inheritanceTaxIsNotAnnualWealthLevy :
  inheritanceTransferLevy ≡ recurringNetWealthLevy → ⊥
inheritanceTaxIsNotAnnualWealthLevy ()

------------------------------------------------------------------------
-- EXACT FINITE DEFINITIONS: 100% RATE ON AMOUNTS ABOVE A THRESHOLD.
-- Amounts are arbitrary NONNEGATIVE units.  The policy base remains typed.
------------------------------------------------------------------------

record PersonalIncome : Set where
  constructor personal-income
  field
    units : Nat
open PersonalIncome public renaming (units to incomeUnits)

record OwnedNetWealth : Set where
  constructor owned-net-wealth
  field
    units : Nat
open OwnedNetWealth public renaming (units to wealthUnits)

hundredPercentIncomeExcess : Nat → PersonalIncome → Nat
hundredPercentIncomeExcess threshold i = incomeUnits i ∸ threshold

hundredPercentWealthExcess : Nat → OwnedNetWealth → Nat
hundredPercentWealthExcess threshold w = wealthUnits w ∸ threshold

netWealthAfterExcessTax : Nat → OwnedNetWealth → Nat
netWealthAfterExcessTax threshold w =
  wealthUnits w ∸ hundredPercentWealthExcess threshold w

incomeExample : hundredPercentIncomeExcess 3 (personal-income 5) ≡ 2
incomeExample = refl

wealthExample : hundredPercentWealthExcess 3 (owned-net-wealth 5) ≡ 2
wealthExample = refl

wealthRemainingExample :
  netWealthAfterExcessTax 3 (owned-net-wealth 5) ≡ 3
wealthRemainingExample = refl

wealthUnderThreshold :
  netWealthAfterExcessTax 3 (owned-net-wealth 2) ≡ 2
wealthUnderThreshold = refl

-- Numerically equal liabilities cannot identify the tax-base object.
sameAmountDifferentBases :
  hundredPercentIncomeExcess 3 (personal-income 5) ≡
  hundredPercentWealthExcess 3 (owned-net-wealth 5)
sameAmountDifferentBases = refl

-- Same flow tax, different wealth tax: the annual income coordinate does not
-- suffice to recover the current stock-coordinate liability.
sameFlowObservation :
  hundredPercentIncomeExcess 2 (personal-income 2) ≡
  hundredPercentIncomeExcess 2 (personal-income 2)
sameFlowObservation = refl

wealthLiabilitiesDiffer :
  hundredPercentWealthExcess 2 (owned-net-wealth 4) ≡
  hundredPercentWealthExcess 2 (owned-net-wealth 7) → ⊥
wealthLiabilitiesDiffer ()

------------------------------------------------------------------------
-- SAME LIABILITY DOES NOT DETERMINE CORPORATE CONTROL / VOTING RIGHTS.
------------------------------------------------------------------------

record OwnershipSnapshot : Set where
  constructor ownership-snapshot
  field
    totalNetWealthUnits : Nat
    votingRightsUnits : Nat
open OwnershipSnapshot public

wealthLevyFromSnapshot : Nat → OwnershipSnapshot → Nat
wealthLevyFromSnapshot threshold s = totalNetWealthUnits s ∸ threshold

sameTaxDifferentVotingPower :
  wealthLevyFromSnapshot 3 (ownership-snapshot 5 1) ≡
  wealthLevyFromSnapshot 3 (ownership-snapshot 5 7)
sameTaxDifferentVotingPower = refl

votingPowerCannotBeRecoveredFromSameLiability :
  votingRightsUnits (ownership-snapshot 5 1) ≡
  votingRightsUnits (ownership-snapshot 5 7) → ⊥
votingPowerCannotBeRecoveredFromSameLiability ()

------------------------------------------------------------------------
-- PRIMARY-SOURCE ROLES AND CLOSED/OPEN ASSERTION BOUNDARIES.
------------------------------------------------------------------------

data EvidenceKind : Set where
  originalPoliticalText : EvidenceKind
  enactedAdministrativePolicy : EvidenceKind
  governmentObservedSeries : EvidenceKind
  scholarlyEmpiricalEstimate : EvidenceKind
  expertPolicyProposal : EvidenceKind

data ClaimStrength : Set where
  enactedRule : ClaimStrength
  administrativeObservation : ClaimStrength
  conditionalResearchEstimate : ClaimStrength
  historicalAuthoredPosition : ClaimStrength
  proposedNotEnacted : ClaimStrength

record TaxSourceReceipt : Set where
  constructor tax-source-receipt
  field
    originalAuthorOrInstitution : String
    exactWorkAndDate : String
    sourceLocator : String
    evidenceKind : EvidenceKind
    claimStrength : ClaimStrength
    supportedScope : String
    prohibitedPromotion : String
open TaxSourceReceipt public

marxEngels1848 : TaxSourceReceipt
marxEngels1848 = tax-source-receipt
  "Karl Marx and Friedrich Engels"
  "Manifesto of the Communist Party, Part II (1848)"
  "https://www.marxists.org/archive/marx/works/1848/communist-manifesto/ch02.htm"
  originalPoliticalText historicalAuthoredPosition
  "proposes heavy graduated income tax and abolition of inheritance rights as transitional measures"
  "does not make a later wealth-cap proposal identical to the 1848 programme"

usTopRatesFred : TaxSourceReceipt
usTopRatesFred = tax-source-receipt
  "US tax-rate historical series, distributed by Federal Reserve Bank of St. Louis FRED"
  "US Individual Income Tax: Highest Bracket, series IITTRHB; 1944-1945"
  "https://fred.stlouisfed.org/data/IITTRHB"
  governmentObservedSeries administrativeObservation
  "top statutory marginal federal individual income tax rate 94 percent in 1944 and 1945"
  "statutory top rate is not an effective rate, income distribution, or isolated WWII causal effect"

vancouver2025 : TaxSourceReceipt
vancouver2025 = tax-source-receipt
  "City of Vancouver"
  "Empty Homes Tax Annual Report 2025, reporting 2024 vacancy reference year"
  "https://vancouver.ca/files/cov/2025-empty-homes-tax-annual-report.pdf"
  governmentObservedSeries administrativeObservation
  "2024 recorded vacant rate 0.49 percent; 67 percent fall in reported vacant homes 2017-2024"
  "city explicitly says tax-only causal attribution is difficult; not a stock-wealth tax"

victoriaRates2026 : TaxSourceReceipt
victoriaRates2026 = tax-source-receipt
  "State Revenue Office Victoria"
  "Vacant residential land tax: current rates (2026)"
  "https://sro.vic.gov.au/about-us/rates-and-statistics/current-rates/vacant-residential-land-tax-current-rates"
  enactedAdministrativePolicy enactedRule
  "capital-improved-value annual VRLT, common consecutive-year rates 1, 2, 3 percent subject to exceptions"
  "vacancy trigger is not general idle equity, and special 1 percent categories remain separate"

oecdInheritance2021 : TaxSourceReceipt
oecdInheritance2021 = tax-source-receipt
  "OECD"
  "Inheritance Taxation in OECD Countries (2021), DOI 10.1787/e2879a7d-en"
  "https://doi.org/10.1787/e2879a7d-en"
  scholarlyEmpiricalEstimate conditionalResearchEstimate
  "24 of 36 OECD countries covered levied wealth transfer taxes; 2018 mean 0.5 percent of tax revenues among levying countries"
  "cross-country prevalence and receipts do not prove dynastic concentration eliminated"

jakobsenEtAl2026 : TaxSourceReceipt
jakobsenEtAl2026 = tax-source-receipt
  "Katrine Jakobsen, Henrik Kleven, Jonas Kolsrud, Camille Landais, Mathilde Munoz"
  "Taxing Top Wealth: Migration Responses and Their Aggregate Economic Implications, AER 116(10), October 2026"
  "https://doi.org/10.1257/aer.20241596"
  scholarlyEmpiricalEstimate conditionalResearchEstimate
  "Scandinavian administrative estimate: 1 percentage point top-rate increase accompanies about 2 percent fewer wealthy residents; aggregate employment -0.02 percent, investment -0.07 percent, value added -0.10 percent"
  "not a global invariant and not evidence that all wealth taxation is economically disastrous"

zucman2024 : TaxSourceReceipt
zucman2024 = tax-source-receipt
  "Gabriel Zucman"
  "A Blueprint for a Coordinated Minimum Effective Taxation Standard for Ultra-High-Net-Worth Individuals, 25 June 2024"
  "https://taxobservatory.world/www-site/uploads/2024/06/report-g20.pdf"
  expertPolicyProposal proposedNotEnacted
  "proposes globally coordinated annual minimum tax equal to 2 percent of total wealth for billionaires"
  "proposal is not enacted law; 2 percent minimum is not a 100 percent tax above threshold"

------------------------------------------------------------------------
-- NO SOURCE OR SCENARIO CAN AUTOMATICALLY CERTIFY A CAUSAL POLICY EFFECT.
------------------------------------------------------------------------

data VacantHomesTrendProvesIsolatedTaxEffect : Set where
data HighStatutoryRateImpliesHighEffectiveRate : Set where
data TaxpayerMigrationProvesNetEconomicFailure : Set where
data WealthTaxPolicyEqualsInheritancePolicy : Set where
data AnyPoliticalTextProvesContemporaryPolicyOutcome : Set where

vacancyTrendIsNotIsolatedCausalIdentification :
  VacantHomesTrendProvesIsolatedTaxEffect → ⊥
vacancyTrendIsNotIsolatedCausalIdentification ()

statutoryRateIsNotEffectiveRate :
  HighStatutoryRateImpliesHighEffectiveRate → ⊥
statutoryRateIsNotEffectiveRate ()

migrationIsNotNetFailureProof :
  TaxpayerMigrationProvesNetEconomicFailure → ⊥
migrationIsNotNetFailureProof ()

wealthAndInheritanceDistinct :
  WealthTaxPolicyEqualsInheritancePolicy → ⊥
wealthAndInheritanceDistinct ()

authoredTheoryIsNotOutcomeProof :
  AnyPoliticalTextProvesContemporaryPolicyOutcome → ⊥
authoredTheoryIsNotOutcomeProof ()
