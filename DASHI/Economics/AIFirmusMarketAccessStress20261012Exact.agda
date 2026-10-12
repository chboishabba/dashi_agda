module DASHI.Economics.AIFirmusMarketAccessStress20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

secondaryMarketReportingKind : Source.SourceKind
secondaryMarketReportingKind = Source.namedSourceKind "secondary current capital-markets reporting"

firmusReutersSource : Source.AttributedSource
firmusReutersSource = Source.mkNoDOISource
  "Reuters"
  "Nvidia-backed Firmus scraps $5 billion Australia IPO amid growing AI scrutiny"
  "current capital-markets reporting"
  "2026-10-08"
  "https://www.reuters.com/world/asia-pacific/australian-nvidia-backed-ai-data-centre-operator-firmus-shelves-ipo-2026-10-08/"
  secondaryMarketReportingKind
  "reports withdrawal of planned USD 5B Firmus IPO implying about USD 30.6B valuation amid tepid investor interest and concerns over debt, execution and sustainability of AI-infrastructure valuations"
  Source.publicAttribution

record MarketAccessStress : Set where
  constructor market-access-stress
  field
    issuer : String
    plannedIPOBillionUSD : Nat
    impliedValuationTenthBillionUSD : Nat
    ipoWithdrawn : Bool
    investorSelectivityStress : Bool
    debtConcernReported : Bool
    executionConcernReported : Bool
    valuationSustainabilityConcernReported : Bool
    sectorBubbleEstablished : Bool
    systemicFundingClosureEstablished : Bool

open MarketAccessStress public

firmusOctober2026Stress : MarketAccessStress
firmusOctober2026Stress = market-access-stress
  "Firmus"
  5
  306
  true true true true true false false

plannedIPOBillionUSDIs5 : plannedIPOBillionUSD firmusOctober2026Stress ≡ 5
plannedIPOBillionUSDIs5 = refl

impliedValuationTenthBillionUSDIs306 :
  impliedValuationTenthBillionUSD firmusOctober2026Stress ≡ 306
impliedValuationTenthBillionUSDIs306 = refl

ipoWithdrawnObserved : ipoWithdrawn firmusOctober2026Stress ≡ true
ipoWithdrawnObserved = refl

investorSelectivityStressObserved :
  investorSelectivityStress firmusOctober2026Stress ≡ true
investorSelectivityStressObserved = refl

sectorBubbleEstablishedIsFalse :
  sectorBubbleEstablished firmusOctober2026Stress ≡ false
sectorBubbleEstablishedIsFalse = refl

data OneIssuerWithdrawalImpliesSectorBubblePermission : Set where
data MarketStressImpliesSystemicFundingClosurePermission : Set where

oneIssuerWithdrawalDoesNotCreateSectorBubble :
  OneIssuerWithdrawalImpliesSectorBubblePermission → ⊥
oneIssuerWithdrawalDoesNotCreateSectorBubble ()

marketStressDoesNotCreateSystemicFundingClosure :
  MarketStressImpliesSystemicFundingClosurePermission → ⊥
marketStressDoesNotCreateSystemicFundingClosure ()

boundary : String
boundary =
  "Firmus's withdrawn planned USD 5B Australian IPO at an implied USD 30.6B valuation is a realised AI-infrastructure market-access stress observation, with Reuters reporting investor concerns over debt, execution and valuation sustainability. It demonstrates capital-market selectivity/repricing for one issuer; it does not establish a sector-wide bubble or systemic funding closure."
