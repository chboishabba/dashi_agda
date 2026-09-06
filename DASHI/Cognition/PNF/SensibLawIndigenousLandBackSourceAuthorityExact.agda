module DASHI.Cognition.PNF.SensibLawIndigenousLandBackSourceAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Source-attribution constitution for the global LAND BACK evidence lane.
--
-- Peer-reviewed causal studies, peer-reviewed comparative studies, official
-- administrative receipts, economic valuation reports, historical policy
-- analyses and working papers are intentionally non-interchangeable.
------------------------------------------------------------------------

data SourceAuthorityKind : Set where
  peerReviewedCausalStudy
  peerReviewedComparativeStudy
  peerReviewedSystematicReview
  officialAdministrativeReceipt
  officialPolicyStudy
  economicValuationReport
  historicalPolicyAnalysis
  workingPaperCausalClaim
  criticalInterpretation
  normativeDecolonialHypothesis
  : SourceAuthorityKind

data PublicationStatus : Set where
  peerReviewedPublished
  officialPublished
  institutionalReportPublished
  workingPaperNotPeerReviewed
  interpretiveLayerOnly
  : PublicationStatus

record SourceAuthorityReceipt : Set where
  constructor sourceAuthorityReceipt
  field
    sourceId : String
    citation : String
    year : Nat
    authorityKind : SourceAuthorityKind
    publicationStatus : PublicationStatus
    directClaimBoundary : String
    peerReviewed : Bool
    officialGovernmentSource : Bool
    causalClaimAllowed : Bool
    universalGeneralisationAllowed : Bool
    universalGeneralisationAllowedIsFalse : universalGeneralisationAllowed ≡ false
    sourceAttributionRequired : Bool
    sourceAttributionRequiredIsTrue : sourceAttributionRequired ≡ true
open SourceAuthorityReceipt public

-- 2024 Brazilian Legal Amazon competing-land-use comparison.
denBraber2024Authority : SourceAuthorityReceipt
denBraber2024Authority = sourceAuthorityReceipt
  "den-braber-2024-amazon-tradeoffs"
  "den Braber et al., Nature Ecology & Evolution 8 (2024) 1482-1492, doi:10.1038/s41559-024-02458-w"
  2024
  peerReviewedComparativeStudy
  peerReviewedPublished
  "matched census-tract comparison of deforestation, income, Gini, literacy and sanitation across protected-area/Indigenous-territory treatments and competing land-use controls in the Brazilian Legal Amazon; not a universal causal theorem about Indigenous governance"
  true false false false refl true refl

-- U.S. land-back economic study: causal methods claimed, but still an SSRN working paper.
arcoiteJohnson2025Authority : SourceAuthorityReceipt
arcoiteJohnson2025Authority = sourceAuthorityReceipt
  "arcoite-johnson-2025-landback-working-paper"
  "Arcoite & Johnson, Land-Back to Move Forward?, SSRN 5189600, posted 28 Apr 2025"
  2025
  workingPaperCausalClaim
  workingPaperNotPeerReviewed
  "authors report IV and endogenous-treatment estimates across more than 1,700 Indigenous communities with reductions in low-income share and unemployment; working-paper status must remain visible"
  false false true false refl true refl

-- U.S. Department of the Interior program totals are administrative facts, not outcome estimates.
doiLandBuyBackAuthority : SourceAuthorityReceipt
doiLandBuyBackAuthority = sourceAuthorityReceipt
  "doi-land-buyback-program-conclusion"
  "U.S. Department of the Interior, Land Buy-Back Program for Tribal Nations conclusion / program history"
  2023
  officialAdministrativeReceipt
  officialPublished
  "nearly 3 million acres restored to Tribal trust ownership; $1.69 billion paid to more than 123,000 interested individuals; no causal socioeconomic effect inferred from these totals alone"
  false true false false refl true refl

-- WRI valuation is an economic valuation report, not a causal experiment.
wriTenureEconomicValuationAuthority : SourceAuthorityReceipt
wriTenureEconomicValuationAuthority = sourceAuthorityReceipt
  "wri-2016-climate-benefits-tenure-costs"
  "WRI, Climate Benefits, Tenure Costs / Protecting Indigenous Land Rights Makes Good Economic Sense (2016)"
  2016
  economicValuationReport
  institutionalReportPublished
  "economic valuation of tenure-secure Indigenous lands in Bolivia, Brazil and Colombia; reports 20-year ecosystem-service/climate benefits and tenure-security costs; not a causal trial of land return"
  false false false false refl true refl

-- Contemporary official/policy evidence on subsidized rural credit and deforestation.
cpi2024RuralCreditAuthority : SourceAuthorityReceipt
cpi2024RuralCreditAuthority = sourceAuthorityReceipt
  "cpi-2024-rural-credit-deforestation"
  "Climate Policy Initiative / PUC-Rio, subsidized rural credit and deforestation, 3 Jul 2024"
  2024
  officialPolicyStudy
  institutionalReportPublished
  "31% of properties with deforestation received subsidized rural credit during 2020-2022; R$14 billion/year of subsidized credit was associated with deforestation; association/policy exposure is not by itself proof that the entire income differential in another study is subsidy-caused"
  false false false false refl true refl

-- Historical policy distortion literature is retained as historical, not projected into every current case.
binswanger1991Authority : SourceAuthorityReceipt
binswanger1991Authority = sourceAuthorityReceipt
  "binswanger-1991-brazil-policy-deforestation"
  "Binswanger, Brazilian policies that encourage deforestation in the Amazon, World Development 19(7) (1991) 821-829"
  1991
  historicalPolicyAnalysis
  peerReviewedPublished
  "historical tax, land-allocation, tax-credit and subsidized-credit incentives accelerated deforestation; temporal scope must not be silently treated as current-policy identity"
  true false false false refl true refl

margulis2003Authority : SourceAuthorityReceipt
margulis2003Authority = sourceAuthorityReceipt
  "margulis-2003-causes-amazon-deforestation"
  "Sergio Margulis, Causes of Deforestation of the Brazilian Amazon, World Bank Working Paper 22 / report 27715"
  2003
  officialPolicyStudy
  institutionalReportPublished
  "documents the private viability/risk/liquidity rationale for cattle ranching in significant parts of the Amazon while distinguishing private gains from social/environmental desirability; rejects simplistic universal subsidy-only explanation"
  false false false false refl true refl

------------------------------------------------------------------------
-- Source-proposition firewalls.
------------------------------------------------------------------------

data WorkingPaperEqualsPeerReviewedResult : Set where
data AdministrativeAcreageEqualsEconomicOutcome : Set where
data EconomicValuationEqualsCausalEffect : Set where
data SubsidizedCreditAssociationExplainsAllIncomeDifference : Set where
data HistoricalSubsidyMechanismEqualsCurrentUniversalMechanism : Set where
data ComparativeIncomeResultProvesGovernanceDeficiency : Set where

workingPaperDoesNotEqualPeerReview : WorkingPaperEqualsPeerReviewedResult → ⊥
workingPaperDoesNotEqualPeerReview ()

acreageDoesNotEqualEconomicOutcome : AdministrativeAcreageEqualsEconomicOutcome → ⊥
acreageDoesNotEqualEconomicOutcome ()

valuationDoesNotEqualCausalEffect : EconomicValuationEqualsCausalEffect → ⊥
valuationDoesNotEqualCausalEffect ()

creditAssociationDoesNotExplainAllIncomeDifference : SubsidizedCreditAssociationExplainsAllIncomeDifference → ⊥
creditAssociationDoesNotExplainAllIncomeDifference ()

historicalMechanismDoesNotAutoGeneralise : HistoricalSubsidyMechanismEqualsCurrentUniversalMechanism → ⊥
historicalMechanismDoesNotAutoGeneralise ()

incomeResultDoesNotProveGovernanceDeficiency : ComparativeIncomeResultProvesGovernanceDeficiency → ⊥
incomeResultDoesNotProveGovernanceDeficiency ()
