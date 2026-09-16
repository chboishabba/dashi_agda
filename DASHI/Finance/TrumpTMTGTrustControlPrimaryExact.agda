module DASHI.Finance.TrumpTMTGTrustControlPrimaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- TMTG TRUST CONTROL / BENEFICIAL-INTEREST REFINEMENT
--
-- The SEC record distinguishes several relations that should not be collapsed:
--
--   * Donald J. Trump: settlor and sole beneficiary of the Trust;
--   * Donald J. Trump Jr.: trustee with sole voting and investment power over
--     TMTG securities owned by the Trust;
--   * the Trust: holder of 114,750,000 TMTG shares.
--
-- This pays a specific securities-control proposition.  It does not establish
-- who decides every trade, what information was shared, or any policy quid pro
-- quo, motive, MNPI use, legality or realised gain.
------------------------------------------------------------------------

trustControlPrimary : Atlas.TradeEvidenceClaim
trustControlPrimary =
  Atlas.tradeEvidenceClaim
    "TMTG-2026-trust-control-10KA"
    "Donald J. Trump Revocable Trust / Donald J. Trump / Donald J. Trump Jr."
    "114,750,000 Trump Media & Technology Group Corp. shares"
    Atlas.trustOwnershipClaim
    "status described in 2026 Form 10-K/A; underlying transfer 2024-12-17"
    "2026-04"
    "TMTG's SEC-filed annual-report amendment states that President Donald J. Trump transferred 114,750,000 shares to the Donald J. Trump Revocable Trust in a transfer not involving a purchase or sale; President Trump is the settlor and sole beneficiary; Donald J. Trump Jr. is trustee and has sole voting and investment power over all securities owned by the Trust."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "Trump Media & Technology Group Corp.; filed with U.S. Securities and Exchange Commission"
      "Form 10-K/A for fiscal year ended December 31, 2025 — security ownership / Trust footnote"
      "2026-04"
      "no DOI"
      "https://www.sec.gov/Archives/edgar/data/1849635/000114036126018230/ef20071731_10ka.htm"
      Atlas.ownershipSchedule)
    (Atlas.secArtifact
      "TMTG-2026-10KA-trust-control"
      "https://www.sec.gov/Archives/edgar/data/1849635/000114036126018230/ef20071731_10ka.htm")
    "Pays the Trust share quantity, Donald Trump's settlor/sole-beneficiary relation, and Donald Trump Jr.'s trustee/sole voting-and-investment-power relation for Trust-owned TMTG securities only."
    true false false false

trustSchedule13DControl : Atlas.TradeEvidenceClaim
trustSchedule13DControl =
  Atlas.tradeEvidenceClaim
    "TMTG-Trust-13D-control-2025-12"
    "Donald J. Trump Revocable Trust dated April 7, 2014"
    "Trump Media & Technology Group Corp. common stock"
    Atlas.trustOwnershipClaim
    "status as of 2025-12-15 denominator / Schedule 13D"
    "2025-12"
    "A Schedule 13D for the Donald J. Trump Revocable Trust reports 114,750,000 TMTG shares, approximately 41.5% under the filing's stated denominator, and states that Donald J. Trump is settlor and sole beneficiary while Donald J. Trump Jr. is trustee with sole voting and investment power over all securities owned by the Trust."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "Donald J. Trump Revocable Trust; filed with U.S. Securities and Exchange Commission"
      "Schedule 13D — Donald J. Trump Revocable Trust / Trump Media & Technology Group Corp."
      "2025-12"
      "no DOI"
      "https://www.sec.gov/Archives/edgar/data/947033/000114036125046424/xslSCHEDULE_13D_X01/primary_doc.xml"
      Atlas.ownershipSchedule)
    (Atlas.secArtifact
      "0001140361-25-046424"
      "https://www.sec.gov/Archives/edgar/data/947033/000114036125046424/xslSCHEDULE_13D_X01/primary_doc.xml")
    "Corroborates the Trust ownership/voting-investment control structure within a separate SEC filing. It does not establish information sharing or specific transaction instructions."
    true false false false

------------------------------------------------------------------------
-- Exact control is proposition-local.
------------------------------------------------------------------------

data VotingInvestmentPowerAutomaticallyMeansEveryTradeDirected : Set where
data TrusteeControlAutomaticallyMeansBeneficiarySharesPrivateInformation : Set where
data SoleBeneficiaryAutomaticallyMeansOperationalManagement : Set where
\data TrustControlAutomaticallyMeansPresidentialPolicyInfluence : Set where

votingPowerDoesNotProveEveryTradeDirected :
  VotingInvestmentPowerAutomaticallyMeansEveryTradeDirected → ⊥
votingPowerDoesNotProveEveryTradeDirected ()

trusteeControlDoesNotProveSharedPrivateInformation :
  TrusteeControlAutomaticallyMeansBeneficiarySharesPrivateInformation → ⊥
trusteeControlDoesNotProveSharedPrivateInformation ()

beneficiaryDoesNotMeanOperationalManagement :
  SoleBeneficiaryAutomaticallyMeansOperationalManagement → ⊥
beneficiaryDoesNotMeanOperationalManagement ()

trustControlDoesNotProvePolicyInfluence :
  TrustControlAutomaticallyMeansPresidentialPolicyInfluence → ⊥
trustControlDoesNotProvePolicyInfluence ()

record TrumpTMTGTrustControlPrimaryBoundary : Set where
  constructor trump-tmtg-trust-control-primary-boundary
  field
    trustShareQuantityPaid : Bool
    beneficiaryRelationPaid : Bool
    trusteeVotingPowerPaid : Bool
    trusteeInvestmentPowerPaid : Bool
    everyTradeDecisionStillUnpaid : Bool
    privateInformationSharingStillUnpaid : Bool
    policyInfluenceStillUnpaid : Bool

canonicalTrumpTMTGTrustControlPrimaryBoundary :
  TrumpTMTGTrustControlPrimaryBoundary
canonicalTrumpTMTGTrustControlPrimaryBoundary =
  trump-tmtg-trust-control-primary-boundary
    true true true true true true true
