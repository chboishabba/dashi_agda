module DASHI.Finance.TrumpFamilyTradeSourceQualityRound3Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas
import DASHI.Finance.TrumpFamilyTradeSourceQualityExact as Quality
import DASHI.Finance.TrumpFamilyTradePrimarySourceRound3Exact as Round3
import DASHI.Finance.TrumpTMTGTrustControlPrimaryExact as Trust
import DASHI.Finance.TruthAPIIndependentCorroborationExact as Independent
import DASHI.Finance.TruthAPILitigationAllegationExact as Litigation

------------------------------------------------------------------------
-- PROPOSITION-INDEXED QUALITY REFINEMENT
--
-- Evidence quality is not attached to an entity or topic globally.  The same
-- Truth API evidence graph can strongly support launch/customer-count/revenue,
-- weakly support customer class/pricing, and leave legal merits or customer
-- identities unresolved.  Likewise a filed transaction can be exact for event
-- identity while remaining silent about decision-maker or source of capital.
------------------------------------------------------------------------

coinbaseSaleEventQuality :
  Quality.ClaimEvidenceQuality Round3.trumpCoinbaseSale20260212
coinbaseSaleEventQuality =
  Quality.claim-evidence-quality
    true true true true true false false false false

truthAPILaunchQuality :
  Quality.ClaimEvidenceQuality Round3.truthAPIRealisedLaunchAndCustomers
truthAPILaunchQuality =
  Quality.claim-evidence-quality
    true true true true true true false false false

trustControlQuality :
  Quality.ClaimEvidenceQuality Trust.trustControlPrimary
trustControlQuality =
  Quality.claim-evidence-quality
    true true true true true false false false false

litigationFilingQuality :
  Quality.ClaimEvidenceQuality Litigation.truthAPIConstitutionalChallengeFiled
litigationFilingQuality =
  Quality.claim-evidence-quality
    true true true true true false false false false

coinbaseSalePromotionReady :
  Quality.PromotionReadyFor Round3.trumpCoinbaseSale20260212 coinbaseSaleEventQuality
coinbaseSalePromotionReady =
  Quality.promotion-ready-for refl refl refl refl

truthAPILaunchPromotionReady :
  Quality.PromotionReadyFor Round3.truthAPIRealisedLaunchAndCustomers truthAPILaunchQuality
truthAPILaunchPromotionReady =
  Quality.promotion-ready-for refl refl refl refl

------------------------------------------------------------------------
-- The independent source axis is itself paid by an independent claim, rather
-- than copied into the issuer claim by fiat.
------------------------------------------------------------------------

truthAPICorroborationWitness :
  Atlas.independentCorroborationPaid Independent.truthAPIReutersCorroboration ≡ true
truthAPICorroborationWitness = refl

------------------------------------------------------------------------
-- Non-inheritance across neighboring propositions.
------------------------------------------------------------------------

data LaunchCorroborationAutomaticallyPaysCustomerIdentity : Set where
data LaunchCorroborationAutomaticallyPaysContractTerms : Set where
data FilingPrecisionAutomaticallyPaysFundingSource : Set where
data TrustControlAutomaticallyPaysInformationSharing : Set where
data ComplaintIdentityAutomaticallyPaysLegalMerits : Set where

launchCorroborationDoesNotPayCustomerIdentity :
  LaunchCorroborationAutomaticallyPaysCustomerIdentity → ⊥
launchCorroborationDoesNotPayCustomerIdentity ()

launchCorroborationDoesNotPayContractTerms :
  LaunchCorroborationAutomaticallyPaysContractTerms → ⊥
launchCorroborationDoesNotPayContractTerms ()

filingPrecisionDoesNotPayFundingSource :
  FilingPrecisionAutomaticallyPaysFundingSource → ⊥
filingPrecisionDoesNotPayFundingSource ()

trustControlDoesNotPayInformationSharing :
  TrustControlAutomaticallyPaysInformationSharing → ⊥
trustControlDoesNotPayInformationSharing ()

complaintIdentityDoesNotPayLegalMerits :
  ComplaintIdentityAutomaticallyPaysLegalMerits → ⊥
complaintIdentityDoesNotPayLegalMerits ()

record TrumpFamilyTradeSourceQualityRound3Boundary : Set where
  constructor trump-family-trade-source-quality-round3-boundary
  field
    sourceQualityIsPropositionIndexed : Bool
    coinbaseEventHasPrimaryDocumentQuality : Bool
    truthAPILaunchHasPrimaryAndIndependentQuality : Bool
    trustVotingInvestmentControlHasPrimaryQuality : Bool
    complaintHasPrimaryForAllegationQuality : Bool
    customerIdentityDoesNotInheritLaunchQuality : Bool
    fundingSourceDoesNotInheritTransactionQuality : Bool
    legalMeritsDoNotInheritPleadingIdentityQuality : Bool

canonicalTrumpFamilyTradeSourceQualityRound3Boundary :
  TrumpFamilyTradeSourceQualityRound3Boundary
canonicalTrumpFamilyTradeSourceQualityRound3Boundary =
  trump-family-trade-source-quality-round3-boundary
    true true true true true true true true
