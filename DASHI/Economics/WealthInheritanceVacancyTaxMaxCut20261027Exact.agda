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
open import Data.Nat using (_∸_; _⊓_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties as NatFacts using (≤-total; m≤n⇒m∸n≡0; m∸[m∸n]≡n; m≤n⇒m⊓n≡m; m≥n⇒m⊓n≡n; m∸n≤m)
open import Data.Sum using (inj₁; inj₂)
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
  corporateJurisdictionalGloBEIncome : TaxBase
  securitiesTransactionValue : TaxBase
  unimprovedLandSiteValue : TaxBase
  unverifiedIdleCorporateEquityStatus : TaxBase

data Policy : Set where
  incomeHundredAboveThreshold : Policy
  wealthHundredAboveThreshold : Policy
  recurringNetWealthLevy : Policy
  inheritanceTransferLevy : Policy
  vacantHomesStatusLevy : Policy
  realisedGainsLevy : Policy
  markToMarketGainsLevy : Policy
  multinationalGloBEProfitTopUp : Policy
  securitiesPurchaseStampDuty : Policy
  landSiteValueTax : Policy
  proposedDurationEscalatingIdleEquityLevy : Policy

taxBase : Policy → TaxBase
taxBase incomeHundredAboveThreshold = annualPersonalIncome
taxBase wealthHundredAboveThreshold = currentNetWealth
taxBase recurringNetWealthLevy = currentNetWealth
taxBase inheritanceTransferLevy = wealthTransferredAtDeath
taxBase vacantHomesStatusLevy = statusOfVacantResidentialProperty
taxBase realisedGainsLevy = gainsRealisedOnSale
taxBase markToMarketGainsLevy = annualChangeInAssetValue
taxBase multinationalGloBEProfitTopUp = corporateJurisdictionalGloBEIncome
taxBase securitiesPurchaseStampDuty = securitiesTransactionValue
taxBase landSiteValueTax = unimprovedLandSiteValue
taxBase proposedDurationEscalatingIdleEquityLevy = unverifiedIdleCorporateEquityStatus

incomeTaxIsNotStockCap :
  incomeHundredAboveThreshold ≡ wealthHundredAboveThreshold → ⊥
incomeTaxIsNotStockCap ()

vacancyTaxIsNotWealthCap :
  vacantHomesStatusLevy ≡ wealthHundredAboveThreshold → ⊥
vacancyTaxIsNotWealthCap ()

inheritanceTaxIsNotAnnualWealthLevy :
  inheritanceTransferLevy ≡ recurringNetWealthLevy → ⊥
inheritanceTaxIsNotAnnualWealthLevy ()

-- Three consecutive-year PROPOSAL-ONLY rates found in a supplied AI text:
-- 1%, 2%, then 5%. This is NOT Victoria VRLT's normal 1%, 2%, 3%.
-- Neither the legal definition of "idle equity" nor a public revenue
-- receipt is specified in the source. The result below is only a rate
-- numerator in basis points. There is NO legal tax instrument here.
data ProposalTenure : Set where
  firstProposalYear : ProposalTenure
  secondProposalYear : ProposalTenure
  laterProposalYear : ProposalTenure

proposalIdleEquityRateBasisPoints : ProposalTenure → Nat
proposalIdleEquityRateBasisPoints firstProposalYear = 100
proposalIdleEquityRateBasisPoints secondProposalYear = 200
proposalIdleEquityRateBasisPoints laterProposalYear = 500

sourceAIProposedRatesAreNotVictoriaLaw :
  proposalIdleEquityRateBasisPoints laterProposalYear ≡ 300 → ⊥
sourceAIProposedRatesAreNotVictoriaLaw ()

idleEquityIsNotVacantHouse :
  proposedDurationEscalatingIdleEquityLevy ≡
  vacantHomesStatusLevy → ⊥
idleEquityIsNotVacantHouse ()

data AIIdleEquityProposalIsEnactedLaw : Set where
aiIdleEquitySuggestionCannotSelfEnact :
  AIIdleEquityProposalIsEnactedLaw → ⊥
aiIdleEquitySuggestionCannotSelfEnact ()

-- An ownership disclosure mechanism is NOT itself a tax instrument.
data OwnershipDisclosure : Set where
  beneficialOwnershipReporting : OwnershipDisclosure

corporateMinimumTaxIsNotPersonalWealthCap :
  multinationalGloBEProfitTopUp ≡ wealthHundredAboveThreshold → ⊥
corporateMinimumTaxIsNotPersonalWealthCap ()

securitiesDutyIsNotCapitalGainsTax :
  securitiesPurchaseStampDuty ≡ realisedGainsLevy → ⊥
securitiesDutyIsNotCapitalGainsTax ()

landSiteValueIsNotHousingVacancy :
  landSiteValueTax ≡ vacantHomesStatusLevy → ⊥
landSiteValueIsNotHousingVacancy ()

-- A disclosure identifier is not a fiscal liability or legal permission.
data RegistryIdentificationImpliesLegalTaxDue : Set where
beneficialOwnerNameDoesNotDetermineTaxDue :
  RegistryIdentificationImpliesLegalTaxDue → ⊥
beneficialOwnerNameDoesNotDetermineTaxDue ()

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

------------------------------------------------------------------------
-- GENERAL 100%-ABOVE-THRESHOLD STOCK LAW (A05--A08).
-- These are conditional accounting theorems for the explicitly hypothetical
-- policy at one assessment instant, not enacted law or effective collection.
-- Reuse the Agda standard-library natural-number order/truncation lemmas.
------------------------------------------------------------------------

hundredPercentLiabilityZeroBelowThreshold :
  (threshold wealth : Nat) →
  wealth ≤ threshold →
  hundredPercentWealthExcess threshold (owned-net-wealth wealth) ≡ zero
hundredPercentLiabilityZeroBelowThreshold threshold wealth wealth≤threshold =
  m≤n⇒m∸n≡0 wealth≤threshold

netWealthAfterFullyPaidExcessEqualsMin :
  (threshold wealth : Nat) →
  netWealthAfterExcessTax threshold (owned-net-wealth wealth)
    ≡ wealth ⊓ threshold
netWealthAfterFullyPaidExcessEqualsMin threshold wealth
  with ≤-total wealth threshold
... | inj₁ wealth≤threshold
  rewrite m≤n⇒m∸n≡0 wealth≤threshold
        | m≤n⇒m⊓n≡m wealth≤threshold = refl
... | inj₂ threshold≤wealth
  rewrite m∸[m∸n]≡n threshold≤wealth
        | m≥n⇒m⊓n≡n threshold≤wealth = refl

wealthLiabilityNeverExceedsAssessedWealth :
  (threshold wealth : Nat) →
  hundredPercentWealthExcess threshold (owned-net-wealth wealth) ≤ wealth
wealthLiabilityNeverExceedsAssessedWealth threshold wealth =
  m∸n≤m wealth threshold

wealthLiabilityMonotoneAtFixedThreshold :
  (threshold : Nat) {smaller larger : Nat} →
  smaller ≤ larger →
  hundredPercentWealthExcess threshold (owned-net-wealth smaller)
    ≤ hundredPercentWealthExcess threshold (owned-net-wealth larger)
wealthLiabilityMonotoneAtFixedThreshold zero smaller≤larger =
  smaller≤larger
wealthLiabilityMonotoneAtFixedThreshold (suc threshold) {zero} {larger} _ =
  z≤n
wealthLiabilityMonotoneAtFixedThreshold (suc threshold) {suc smaller} {suc larger}
  (s≤s smaller≤larger) =
  wealthLiabilityMonotoneAtFixedThreshold threshold smaller≤larger

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
  internationalModelRule : EvidenceKind
  internationalStandardsGuidance : EvidenceKind

data ClaimStrength : Set where
  enactedRule : ClaimStrength
  administrativeObservation : ClaimStrength
  conditionalResearchEstimate : ClaimStrength
  historicalAuthoredPosition : ClaimStrength
  proposedNotEnacted : ClaimStrength
  adoptionDependsOnDomesticLaw : ClaimStrength
  guidanceNotBindingByItself : ClaimStrength

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
-- REUSED REGULATOR / ORIGINAL ECONOMIC AUTHOR PROVENANCE
-- RATES AND SCOPE ARE SOURCE-RELATIVE. NO UNIVERSAL TAX EFFECT.
------------------------------------------------------------------------

oecdPillarTwo2026 : TaxSourceReceipt
oecdPillarTwo2026 = tax-source-receipt
  "OECD Inclusive Framework"
  "Global Minimum Tax (Pillar Two), 2026 guidance and model rules"
  "https://www.oecd.org/en/topics/global-minimum-tax.html"
  internationalModelRule adoptionDependsOnDomesticLaw
  "qualified large MNE groups: jurisdictional ETR and 15 percent minimum top-up subject to GloBE base and substance exclusions; application depends on implemented domestic legislation"
  "not a personal wealth levy, automatic universal participation, or a tax on every firm's turnover"

hmrcSDRT : TaxSourceReceipt
hmrcSDRT = tax-source-receipt
  "HM Revenue and Customs, United Kingdom"
  "Tax when you buy shares: Overview, online guidance accessed 2026-10-27"
  "https://www.gov.uk/tax-buy-shares"
  enactedAdministrativePolicy enactedRule
  "normally 0.5 percent stamp duty or SDRT on specified taxable share purchases, with different rates and exemptions for other transfers"
  "not a 0.1 percent universal all-derivatives FTT, nor harmless to every investor"

fatfBO2023 : TaxSourceReceipt
fatfBO2023 = tax-source-receipt
  "Financial Action Task Force"
  "Guidance on Beneficial Ownership of Legal Persons, 10 March 2023"
  "https://www.fatf-gafi.org/en/publications/Fatfrecommendations/Guidance-Beneficial-Ownership-Legal-Persons.html"
  internationalStandardsGuidance guidanceNotBindingByItself
  "Recommendation 24 calls for adequate accurate up-to-date beneficial ownership information accessible to competent authorities; national laws vary"
  "not proof that each national beneficial-owner register is public or all holdings are found"

henryGeorge1879 : TaxSourceReceipt
henryGeorge1879 = tax-source-receipt
  "Henry George"
  "Progress and Poverty (1879); original complete text reprinted in 1898 edition"
  "https://www.progress.org/wiki/progress-and-poverty-full-text/"
  originalPoliticalText historicalAuthoredPosition
  "land rent / site value and the proposed single tax are distinct from improvements or wealth in general"
  "not a practical zero-harm proof for all land value tax regimes"

smithWealthNations1776 : TaxSourceReceipt
smithWealthNations1776 = tax-source-receipt
  "Adam Smith"
  "An Inquiry into the Nature and Causes of the Wealth of Nations (1776), Book V, Chapter II, Part II, Article I"
  "https://en.wikisource.org/wiki/The_Wealth_of_Nations/Book_V/Chapter_2"
  originalPoliticalText historicalAuthoredPosition
  "distinguishes rent from profit and wages, favours taxing ground rent as a public-finance source, and says uninhabited houses ought to pay no house-rent tax"
  "Smith's 1776 normative view of house-rent taxation does not invalidate, establish effects of, or describe enacted modern Vancouver vacancy taxes"

piketty2015 : TaxSourceReceipt
piketty2015 = tax-source-receipt
  "Thomas Piketty"
  "Putting Distribution Back at the Center of Economics (2015); DOI 10.1257/jep.29.1.67"
  "https://doi.org/10.1257/jep.29.1.67"
  scholarlyEmpiricalEstimate historicalAuthoredPosition
  "Piketty's original author clarification: r greater than g is one explanatory force among others, not a uniquely sufficient determinant of inequality"
  "no mathematically unavoidable cumulative inequality trajectory or particular tax-rate theorem"

------------------------------------------------------------------------
-- 2026 PARETO SNOWBALL: DISTINCT MODEL / PANEL / ADMINISTRATIVE ROOTS
-- These are independent author teams/data surfaces, not three replications
-- of any one policy estimate. Do not promote working papers into enacted law.
------------------------------------------------------------------------

oecdSocialProtection2026 : TaxSourceReceipt
oecdSocialProtection2026 = tax-source-receipt
  "Organisation for Economic Co-operation and Development"
  "Financing of Social Protection, Chapter 3 (9 September 2026), DOI 10.1787/b384fd31-en"
  "https://www.oecd.org/en/publications/financing-of-social-protection_b384fd31-en/full-report/securing-the-revenue-base-for-social-protection_fee691c9.html"
  governmentObservedSeries administrativeObservation
  "2024 OECD unweighted average recurrent net-wealth taxes at 0.4 percent of revenue, estate/inheritance/gift taxes at 0.4 percent; discusses AI labour-share pressure and comparative funding bases"
  "descriptive 2024 revenue shares do not measure a hypothetical 100 percent threshold levy or predict AI job displacement"

fagerengGuisoRing2026 : TaxSourceReceipt
fagerengGuisoRing2026 = tax-source-receipt
  "Andreas Fagereng; Luigi Guiso; Marius A. K. Ring"
  "How Much and How Fast Do Investors Respond to Equity Premium Changes? Evidence from Wealth Taxation, NBER Working Paper 35262 (May 2026), DOI 10.3386/w35262"
  "https://www.nber.org/papers/w35262"
  scholarlyEmpiricalEstimate conditionalResearchEstimate
  "Norwegian administrative portfolio study reports initially small but slower larger portfolio adjustments from tax-induced equity-premium changes"
  "not a kernel theorem, not necessarily peer reviewed, and not the measured effect of a 100 percent stock ceiling"

chatzouzIMF2026 : TaxSourceReceipt
chatzouzIMF2026 = tax-source-receipt
  "Moustafa Chatzouz"
  "Public Debt, Wealth Inequality, and the Burden of Taxation, IMF Working Paper (14 August 2026), DOI 10.5089/9798229055925.001"
  "https://www.imf.org/en/publications/wp/issues/2026/08/14/public-debt-wealth-inequality-and-the-burden-of-taxation-578868"
  scholarlyEmpiricalEstimate conditionalResearchEstimate
  "regime-conditional stylised overlapping-generations model and cross-country supporting evidence of public-debt/tax-progressivity/wealth-inequality mechanisms"
  "IMF working-paper author view and model-conditioned result; not IMF institutional policy or universal debt-to-inequality law"

euCommissionWealthTax2026 : TaxSourceReceipt
euCommissionWealthTax2026 = tax-source-receipt
  "European Commission Directorate-General for Taxation and Customs Union; CASE; WIFO; PwC; IEB; ifo; VATT; Robaszewski et al."
  "Wealth Taxation, including net wealth, capital and exit taxes, Volume I, published 15 April 2026, DOI 10.2778/0817231"
  "https://op.europa.eu/en/publication-detail/-/publication/b3294f0c-386f-11f1-be39-01aa75ed71a1/language-en"
  scholarlyEmpiricalEstimate conditionalResearchEstimate
  "2026 comparative wealth-related-tax designs and jurisdictional examples; existence of review does not establish effects for each instrument"
  "individual authors and European Commission sponsor retain original work; the report does not prove that a synthetic hard cap works"


------------------------------------------------------------------------
-- 2026-10-28 PRIMARY-SOURCE SNOWBALL, ORIGINAL ESTIMAND BOUNDARIES.
-- A sole-author contemporary Norwegian study must not be collapsed into
-- the different May coauthored portfolio study or October AER panel.
------------------------------------------------------------------------

ringEntrepreneurialNorway2026 : TaxSourceReceipt
ringEntrepreneurialNorway2026 = tax-source-receipt
  "Marius A. K. Ring (sole original author)"
  "Taxing Entrepreneurial Wealth: Evidence from Norway, 2021-2025; NBER Working Paper 35854; October 2026; DOI 10.3386/w35854"
  "https://www.nber.org/papers/w35854"
  scholarlyEmpiricalEstimate conditionalResearchEstimate
  "Norwegian 2021-2024 reforms combining business-wealth, dividends and migration-related capital-gains rules; estimated reform-related migration reduced modeled 2021-2024 wealth-tax revenue increase from 75 percent without migration to 71.5 percent; study reports no evidence of post-reform lower firm investment, higher dividends or more bankruptcies in analyzed samples"
  "Working-paper estimated short-run nulls and reforms jointly varying policy instruments; not proof of universal zero effect, no migration, a single wealth-tax isolated coefficient, or a hypothetical 100 percent hard cap"

data WealthTaxStudyEstimand : Set where
  norwegianPortfolioEquityPremiumAllocation : WealthTaxStudyEstimand
  norwegianJointReformFirmMigrationResponse : WealthTaxStudyEstimand
  scandinavianRateMigrationAggregateResponse : WealthTaxStudyEstimand

ringFirmResponseIsNotFagerengPortfolioResponse :
  norwegianJointReformFirmMigrationResponse
    ≡ norwegianPortfolioEquityPremiumAllocation → ⊥
ringFirmResponseIsNotFagerengPortfolioResponse ()

ringFirmResponseIsNotJakobsenAggregateResponse :
  norwegianJointReformFirmMigrationResponse
    ≡ scandinavianRateMigrationAggregateResponse → ⊥
ringFirmResponseIsNotJakobsenAggregateResponse ()

fagerengPortfolioIsNotJakobsenMigrationEstimate :
  norwegianPortfolioEquityPremiumAllocation
    ≡ scandinavianRateMigrationAggregateResponse → ⊥
fagerengPortfolioIsNotJakobsenMigrationEstimate ()

-- Sharing one coauthor or Norwegian data does not make independent
-- estimands identical. Equally, disjoint estimands alone do not establish
-- independent sampling, independent verification or causal truth.

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
