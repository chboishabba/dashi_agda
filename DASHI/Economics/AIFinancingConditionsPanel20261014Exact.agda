module DASHI.Economics.AIFinancingConditionsPanel20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

secondaryCurrentReporting : Source.SourceKind
secondaryCurrentReporting = Source.namedSourceKind "secondary current financial reporting"

firmusSource : Source.AttributedSource
firmusSource = Source.mkNoDOISource
  "Reuters"
  "Nvidia-backed Firmus scraps $5 billion Australia IPO amid growing AI scrutiny"
  "current financial reporting"
  "2026-10-08"
  "https://www.reuters.com/world/asia-pacific/australian-nvidia-backed-ai-data-centre-operator-firmus-shelves-ipo-2026-10-08/"
  secondaryCurrentReporting
  "reports withdrawal of planned A$5B Firmus IPO amid tepid investor interest and AI-infrastructure valuation/debt/execution concerns"
  Source.publicAttribution

imfSource : Source.AttributedSource
imfSource = Source.mkNoDOISource
  "Reuters"
  "IMF cites AI slowdown, spiking yields as looming global market risks"
  "current financial reporting"
  "2026-10-13"
  "https://www.reuters.com/business/finance/imf-cites-ai-slowdown-spiking-yields-looming-global-market-risks-2026-10-13/"
  secondaryCurrentReporting
  "reports IMF warning that an AI-investment slowdown combined with sector leverage could amplify market volatility; banking stress tests remain broadly resilient"
  Source.publicAttribution

goldmanSource : Source.AttributedSource
goldmanSource = Source.mkNoDOISource
  "Reuters"
  "Goldman CEO watching for election-driven volatility around data centers"
  "current financial reporting"
  "2026-10-13"
  "https://www.reuters.com/business/goldman-ceo-watching-election-driven-volatility-around-data-centers-2026-10-13/"
  secondaryCurrentReporting
  "reports Goldman Sachs CEO comments that large AI/data-centre financing needs and higher interest rates can pressure project returns and long-term viability"
  Source.publicAttribution

record FinancingConditionsPanel : Set where
  constructor financing-conditions-panel
  field
    firmusIPOWithdrawal : Bool
    imfAISlowdownLeverageWarning : Bool
    goldmanFinancingPressure : Bool
    issuerDefaultObserved : Bool
    sectorDefaultRatePaid : Bool
    harmonisedCreditSpreadPanelPaid : Bool
    systemicBankFailureEstablished : Bool
    sectorBubbleEstablished : Bool

open FinancingConditionsPanel public

currentFinancingConditionsPanel : FinancingConditionsPanel
currentFinancingConditionsPanel = financing-conditions-panel
  true true true false false false false false

firmusWithdrawalObserved : firmusIPOWithdrawal currentFinancingConditionsPanel ≡ true
firmusWithdrawalObserved = refl

imfAISlowdownLeverageWarningObserved : imfAISlowdownLeverageWarning currentFinancingConditionsPanel ≡ true
imfAISlowdownLeverageWarningObserved = refl

goldmanFinancingPressureObserved : goldmanFinancingPressure currentFinancingConditionsPanel ≡ true
goldmanFinancingPressureObserved = refl

data FinancingStressPanelImpliesSectorBubblePermission : Set where
data WarningImpliesDefaultPermission : Set where

panelDoesNotCreateSectorBubble : FinancingStressPanelImpliesSectorBubblePermission → ⊥
panelDoesNotCreateSectorBubble ()

warningDoesNotCreateDefault : WarningImpliesDefaultPermission → ⊥
warningDoesNotCreateDefault ()

boundary : String
boundary =
  "By 2026-10-13 the financing-stress surface is broader than a single failed IPO: Firmus withdrawal, an IMF AI-slowdown/leverage risk warning, and Goldman commentary on financing/rate pressure are independently observed secondary-current-reporting coordinates. They do not supply issuer defaults, a harmonised AI-credit-spread/default panel, systemic bank failure, or a sector-bubble theorem."
