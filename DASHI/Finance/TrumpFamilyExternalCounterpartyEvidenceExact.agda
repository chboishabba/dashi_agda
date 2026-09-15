module DASHI.Finance.TrumpFamilyExternalCounterpartyEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Source
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas
import DASHI.Finance.TrumpFamilyTradePrimarySourceExtensionExact as Primary

------------------------------------------------------------------------
-- EXTERNAL COUNTERPARTY / CROSS-BORDER FINANCIAL EDGES
--
-- These observations are retained because they can change a strategic
-- information/bargaining model.  They do not by themselves establish policy
-- influence, quid pro quo, corruption, motive, or a realised personal gain.
------------------------------------------------------------------------

data CounterpartyRelationKind : Set where
  stablecoinSettlementRelation : CounterpartyRelationKind
  tokenInvestmentRelation : CounterpartyRelationKind
  attributedPolicyConcernRelation : CounterpartyRelationKind

record CounterpartyEvidence : Set₁ where
  constructor counterpartyEvidence
  field
    leftParty rightParty : String
    relationKind : CounterpartyRelationKind
    eventDate : String
    proposition : String
    citation : Atlas.SourceCitation
    sourceArtifact : Source.SourceArtifact
    directPrimaryCounterpartySourcePaid : Bool
    independentReportingPaid : Bool
    policyInfluenceEstablished : Bool
    motiveEstablished : Bool

open CounterpartyEvidence public

mgxBinanceUSD1Settlement : CounterpartyEvidence
mgxBinanceUSD1Settlement =
  counterpartyEvidence
    "MGX (Abu Dhabi)"
    "Binance / World Liberty Financial USD1 settlement rail"
    stablecoinSettlementRelation
    "2025-05-01 announcement"
    "Reuters reported that World Liberty Financial co-founder Zach Witkoff announced that USD1 had been selected to settle MGX's $2 billion investment in Binance."
    (Atlas.sourceCitation
      "Reuters"
      "Trump-linked stablecoin to close Abu Dhabi investment in Binance, co-founder says"
      "2025-05-01"
      "no DOI"
      "https://www.reuters.com/world/middle-east/wlfs-zach-witkoff-usd1-selected-official-stablecoin-mgx-investment-binance-2025-05-01/"
      Atlas.independentReporting)
    (Source.sourceArtifact
      "Reuters-2025-05-01-MGX-Binance-USD1"
      Source.derivedArtifact
      "https://www.reuters.com/world/middle-east/wlfs-zach-witkoff-usd1-selected-official-stablecoin-mgx-investment-binance-2025-05-01/"
      "Reuters")
    false true false false

aqua1WLFIInvestment : CounterpartyEvidence
aqua1WLFIInvestment =
  counterpartyEvidence
    "Aqua 1 Foundation (UAE-based fund)"
    "World Liberty Financial WLFI token"
    tokenInvestmentRelation
    "2025-06-27 reporting"
    "Reuters reported that Aqua 1 Foundation purchased $100 million of WLFI tokens, making it the largest publicly known investor identified in that report."
    (Atlas.sourceCitation
      "Reuters"
      "UAE fund buys $100 million of Trump's World Liberty tokens"
      "2025-06-27"
      "no DOI"
      "https://www.reuters.com/business/finance/uae-fund-buys-100-million-trumps-world-liberty-tokens-2025-06-27/"
      Atlas.independentReporting)
    (Source.sourceArtifact
      "Reuters-2025-06-27-Aqua1-WLFI"
      Source.derivedArtifact
      "https://www.reuters.com/business/finance/uae-fund-buys-100-million-trumps-world-liberty-tokens-2025-06-27/"
      "Reuters")
    false true false false

uaeArmsCryptoConcern : CounterpartyEvidence
uaeArmsCryptoConcern =
  counterpartyEvidence
    "named Democratic members of Congress"
    "UAE arms sales / Trump-linked crypto ties"
    attributedPolicyConcernRelation
    "2025-05-15"
    "Reuters reported that Democratic lawmakers seeking to block UAE arms sales cited, among other concerns, ties involving the UAE-linked MGX transaction and Trump-linked cryptocurrency ventures. This is an attributed political concern, not a finding of influence or illegality."
    (Atlas.sourceCitation
      "Reuters"
      "Democrats look to block UAE arms sales, as Trump announces new deals"
      "2025-05-15"
      "no DOI"
      "https://www.reuters.com/business/finance/democrats-look-block-uae-arms-sales-trump-announces-new-deals-2025-05-15/"
      Atlas.independentReporting)
    (Source.sourceArtifact
      "Reuters-2025-05-15-UAE-arms-crypto-concern"
      Source.derivedArtifact
      "https://www.reuters.com/business/finance/democrats-look-block-uae-arms-sales-trump-announces-new-deals-2025-05-15/"
      "Reuters")
    false true false false

------------------------------------------------------------------------
-- Cross-source relevance: the OGE source independently establishes a WLF
-- economic-interest/proceeds structure.  This makes external WLF counterparties
-- relevant to the financial-interest graph, but still does not identify the
-- magnitude, direction or causal effect of any specific counterparty event on
-- the filer's realised income or public policy.
------------------------------------------------------------------------

ogeEconomicInterestAnchor : Atlas.TradeEvidenceClaim
ogeEconomicInterestAnchor = Primary.trumpWLFEconomicInterest

record ExternalCounterpartyRelevance : Set where
  constructor external-counterparty-relevance
  field
    economicInterestEvidence : Atlas.TradeEvidenceClaim
    counterpartyEvidence : CounterpartyEvidence
    sameBusinessSurfaceReference : String
    exactPersonalGainFromCounterpartyPaid : Bool
    exactPersonalGainFromCounterpartyPaidIsFalse :
      exactPersonalGainFromCounterpartyPaid ≡ false
    policyCausationPaid : Bool
    policyCausationPaidIsFalse : policyCausationPaid ≡ false

open ExternalCounterpartyRelevance public

mgxWLFRelevance : ExternalCounterpartyRelevance
mgxWLFRelevance =
  external-counterparty-relevance
    ogeEconomicInterestAnchor
    mgxBinanceUSD1Settlement
    "OGE WLF economic-interest/proceeds entries and Reuters MGX/USD1 settlement reporting refer to the World Liberty financial surface but pay different propositions"
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CounterpartyRelationMeansPolicyInfluence : Set where
data StateLinkedCounterpartyMeansStatePolicyTrade : Set where
data StablecoinSettlementMeansPersonalReceipt : Set where
data AttributedConflictConcernMeansConflictProved : Set where

counterpartyDoesNotProvePolicyInfluence : CounterpartyRelationMeansPolicyInfluence → ⊥
counterpartyDoesNotProvePolicyInfluence ()

stateLinkedCounterpartyDoesNotCreatePolicyTrade : StateLinkedCounterpartyMeansStatePolicyTrade → ⊥
stateLinkedCounterpartyDoesNotCreatePolicyTrade ()

settlementDoesNotEqualPersonalReceipt : StablecoinSettlementMeansPersonalReceipt → ⊥
settlementDoesNotEqualPersonalReceipt ()

concernDoesNotProveConflict : AttributedConflictConcernMeansConflictProved → ⊥
concernDoesNotProveConflict ()

record TrumpFamilyExternalCounterpartyBoundary : Set where
  constructor trump-family-external-counterparty-boundary
  field
    externalCounterpartiesAreTypedRelations : Bool
    ogeInterestAndCounterpartyEventRemainSeparate : Bool
    stateLinkedCounterpartyDoesNotProvePolicyInfluence : Bool
    stablecoinSettlementDoesNotEqualPersonalGain : Bool
    attributedConcernDoesNotBecomeFinding : Bool
    primaryCounterpartyDocumentDebtRemainsVisible : Bool

canonicalTrumpFamilyExternalCounterpartyBoundary :
  TrumpFamilyExternalCounterpartyBoundary
canonicalTrumpFamilyExternalCounterpartyBoundary =
  trump-family-external-counterparty-boundary true true true true true true
