module DASHI.Economics.AICoreWeaveContributionMarginExpectation20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- COREWEAVE CONTRIBUTION-MARGIN EXPECTATION BOUNDARY
--
-- September-2026 financing materials give a genuine company-defined unit-
-- economics expectation for Q2-signed contracts.  It is forward/expected and
-- contract-cohort scoped.  It must not be collapsed into realised accounting
-- margin, provider marginal serving cost, or whole-firm capital return.
------------------------------------------------------------------------

companyFinancingPresentationKind : Source.SourceKind
companyFinancingPresentationKind = Source.namedSourceKind "company financing presentation filed with SEC"

coreWeaveConvertiblePresentationSource : Source.AttributedSource
coreWeaveConvertiblePresentationSource = Source.mkNoDOISource
  "CoreWeave, Inc."
  "2026 convertible financing presentation"
  "SEC-filed investor presentation"
  "2026-09"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000429/crwv2026convertpresentat.htm"
  companyFinancingPresentationKind
  "company states Q2-signed contracts carry expected contribution margins 5-10 percentage points higher than recent quarters / approximately 25 percent higher, with approximately 70 percent price increase across SKUs in July 2026"
  Source.publicAttribution

record ContributionMarginExpectation : Set where
  constructor contribution-margin-expectation
  field
    company : String
    cohort : String
    expectedImprovementLowerPercentagePoints : Nat
    expectedImprovementUpperPercentagePoints : Nat
    expectedRelativeImprovementPercent : Nat
    julyPriceIncreasePercent : Nat
    companyDefinedContributionMarginExpectationPaid : Bool
    realisedContributionMarginPaid : Bool
    gaapGrossMarginPaidByThisSource : Bool
    providerMarginalServingCostPaid : Bool
    wholeFirmCapitalRecoveryPaid : Bool

open ContributionMarginExpectation public

coreWeaveQ2SignedContractExpectation : ContributionMarginExpectation
coreWeaveQ2SignedContractExpectation = contribution-margin-expectation
  "CoreWeave"
  "contracts signed in Q2-2026"
  5 10 25 70
  true false false false false

expectedContributionMarginImprovementLowerPtIs5 :
  expectedImprovementLowerPercentagePoints coreWeaveQ2SignedContractExpectation ≡ 5
expectedContributionMarginImprovementLowerPtIs5 = refl

expectedContributionMarginImprovementUpperPtIs10 :
  expectedImprovementUpperPercentagePoints coreWeaveQ2SignedContractExpectation ≡ 10
expectedContributionMarginImprovementUpperPtIs10 = refl

expectedRelativeContributionMarginImprovementIs25Percent :
  expectedRelativeImprovementPercent coreWeaveQ2SignedContractExpectation ≡ 25
expectedRelativeContributionMarginImprovementIs25Percent = refl

julyPriceIncreaseAcrossSKUsIs70Percent :
  julyPriceIncreasePercent coreWeaveQ2SignedContractExpectation ≡ 70
julyPriceIncreaseAcrossSKUsIs70Percent = refl

realisedContributionMarginPaidIsFalse :
  realisedContributionMarginPaid coreWeaveQ2SignedContractExpectation ≡ false
realisedContributionMarginPaidIsFalse = refl

providerMarginalServingCostPaidIsFalse :
  providerMarginalServingCostPaid coreWeaveQ2SignedContractExpectation ≡ false
providerMarginalServingCostPaidIsFalse = refl

data ExpectedMarginImpliesRealisedMarginPermission : Set where
data ContributionMarginImpliesMarginalServingCostPermission : Set where
data PriceIncreaseImpliesCapitalRecoveryPermission : Set where

expectedMarginDoesNotCreateRealisedMargin :
  ExpectedMarginImpliesRealisedMarginPermission → ⊥
expectedMarginDoesNotCreateRealisedMargin ()

contributionMarginDoesNotCreateMarginalServingCost :
  ContributionMarginImpliesMarginalServingCostPermission → ⊥
contributionMarginDoesNotCreateMarginalServingCost ()

priceIncreaseDoesNotCreateCapitalRecovery :
  PriceIncreaseImpliesCapitalRecoveryPermission → ⊥
priceIncreaseDoesNotCreateCapitalRecovery ()

boundary : String
boundary =
  "CoreWeave's September-2026 SEC-filed financing presentation reports that Q2-signed contracts are expected to have contribution margins 5-10 percentage points higher than recent quarters, described as about 25 percent higher expected contribution margin, alongside about a 70 percent July price increase across SKUs. This is scoped company expectation evidence. It is not realised contribution margin, GAAP gross margin, provider marginal serving cost, or whole-firm capital-recovery authority."
