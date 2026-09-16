module DASHI.Finance.TrumpTradeOversightAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Source
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas
import DASHI.Finance.TrumpPortfolioManagementAttributionExact as Defense

------------------------------------------------------------------------
-- PRIMARY OVERSIGHT REQUEST / DECISION-MAKER ACQUISITION FRONTIER
--
-- Senator Elizabeth Warren and Representative Robert Garcia publicly released
-- an August 2026 letter asking President Trump to identify the third-party
-- financial institutions and money managers responsible for his investment
-- accounts and to address examples of transaction/policy timing that they said
-- raised conflict/self-enrichment concerns.
--
-- The letter is a primary source for the lawmakers' questions, requested
-- information and concerns.  It is not a finding that insider trading,
-- self-enrichment, market manipulation or any other violation occurred.
------------------------------------------------------------------------

oversightLetterArtifact : Source.SourceArtifact
oversightLetterArtifact =
  Source.sourceArtifact
    "Warren-Garcia-Trump-stock-trades-letter-2026-08"
    Source.documentaryArtifact
    "https://www.warren.senate.gov/newsroom/press-releases/warren-garcia-press-trump-on-thousands-of-stock-trades-question-him-on-self-enrichment-from-government-actions/"
    "Office of U.S. Senator Elizabeth Warren / House Oversight Democratic staff"

managerIdentityAcquisitionRequest : Atlas.TradeEvidenceClaim
managerIdentityAcquisitionRequest =
  Atlas.tradeEvidenceClaim
    "Warren-Garcia-2026-manager-identity-request"
    "Senator Elizabeth Warren and Representative Robert Garcia"
    "third-party institutions and money managers for President Trump's investment accounts"
    Atlas.regulatoryConcernClaim
    "request publicized 2026-08-13"
    "2026-08-13"
    "Warren and Garcia asked President Trump to identify the third-party financial institutions and money managers directing his investment accounts and sought information about selected reported transactions and their relationship to government actions or market-moving statements. This claim records the request and attributed concern only."
    Atlas.attributedConcernSupport
    (Atlas.sourceCitation
      "Office of U.S. Senator Elizabeth Warren; U.S. House Committee on Oversight and Government Reform Democratic staff"
      "Warren, Garcia Press Trump on Thousands of Stock Trades, Question Him on Self-Enrichment from Government Actions"
      "2026-08-13"
      "no DOI"
      "https://www.warren.senate.gov/newsroom/press-releases/warren-garcia-press-trump-on-thousands-of-stock-trades-question-him-on-self-enrichment-from-government-actions/"
      Atlas.attributedRegulatoryConcern)
    oversightLetterArtifact
    "Pays existence/content of the official information request and lawmakers' attributed concerns. It does not establish the alleged conflict, self-enrichment, insider trading, market manipulation or policy causation."
    true false false false

record DecisionProvenanceResidual : Set where
  constructor decision-provenance-residual
  field
    defenseClaim : Atlas.TradeEvidenceClaim
    acquisitionRequest : Atlas.TradeEvidenceClaim
    namedInstitutionIdentityPaid : Bool
    namedHumanManagerIdentityPaid : Bool
    accountMandatePaid : Bool
    investmentModelRulesPaid : Bool
    transactionLevelDecisionPathPaid : Bool

open DecisionProvenanceResidual public

currentDecisionProvenanceResidual : DecisionProvenanceResidual
currentDecisionProvenanceResidual =
  decision-provenance-residual
    Defense.thirdPartyManagementDefense
    managerIdentityAcquisitionRequest
    false false false false false

------------------------------------------------------------------------
-- The defense and inquiry coexist without collapsing into either guilt or
-- exoneration.  They identify the next source obligations.
------------------------------------------------------------------------

data CongressionalQuestionAutomaticallyProvesViolation : Set where
data ManagementDefenseAutomaticallyClosesInquiry : Set where
data UnresolvedManagerIdentityAutomaticallyProvesPersonalDirection : Set where

questionDoesNotProveViolation :
  CongressionalQuestionAutomaticallyProvesViolation → ⊥
questionDoesNotProveViolation ()

defenseDoesNotAutomaticallyCloseInquiry :
  ManagementDefenseAutomaticallyClosesInquiry → ⊥
defenseDoesNotAutomaticallyCloseInquiry ()

unresolvedManagerDoesNotProvePersonalDirection :
  UnresolvedManagerIdentityAutomaticallyProvesPersonalDirection → ⊥
unresolvedManagerDoesNotProvePersonalDirection ()

record TrumpTradeOversightAcquisitionBoundary : Set where
  constructor trump-trade-oversight-acquisition-boundary
  field
    attributedManagementDefenseRetained : Bool
    officialManagerIdentityRequestRetained : Bool
    managerIdentityResidualExplicit : Bool
    accountMandateResidualExplicit : Bool
    transactionDecisionPathResidualExplicit : Bool
    oversightConcernDoesNotBecomeFinding : Bool
    defenseDoesNotBecomeIndependentVerification : Bool

canonicalTrumpTradeOversightAcquisitionBoundary :
  TrumpTradeOversightAcquisitionBoundary
canonicalTrumpTradeOversightAcquisitionBoundary =
  trump-trade-oversight-acquisition-boundary
    true true true true true true true
