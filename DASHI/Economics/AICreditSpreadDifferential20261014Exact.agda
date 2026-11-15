module DASHI.Economics.AICreditSpreadDifferential20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

secondaryCurrentMarketReporting : Source.SourceKind
secondaryCurrentMarketReporting = Source.namedSourceKind "secondary current market reporting"

reutersSpreadSource : Source.AttributedSource
reutersSpreadSource = Source.mkNoDOISource
  "Reuters"
  "Corporate bond buyers get picky with flood of AI debt"
  "current credit-market reporting"
  "2026-09-22"
  "https://www.reuters.com/business/finance/corporate-bond-buyers-get-picky-with-flood-ai-debt-2026-09-22/"
  secondaryCurrentMarketReporting
  "reports average spreads of roughly 115 basis points for AI-linked corporate bonds versus roughly 78 basis points for the broader investment-grade market"
  Source.publicAttribution

record CreditSpreadDifferential : Set where
  constructor credit-spread-differential
  field
    aiLinkedAverageSpreadBp : Nat
    broaderIGAverageSpreadBp : Nat
    spreadPremiumBp : Nat
    sameDateCrossSectionObserved : Bool
    issuerMatchedPanelPaid : Bool
    defaultRatePaid : Bool
    causalAIPremiumIdentified : Bool
    sectorBubbleEstablished : Bool

open CreditSpreadDifferential public

currentAICreditSpreadDifferential : CreditSpreadDifferential
currentAICreditSpreadDifferential = credit-spread-differential
  115 78 37 true false false false false

aiLinkedAverageSpreadBpIs115 :
  aiLinkedAverageSpreadBp currentAICreditSpreadDifferential ≡ 115
aiLinkedAverageSpreadBpIs115 = refl

broaderIGAverageSpreadBpIs78 :
  broaderIGAverageSpreadBp currentAICreditSpreadDifferential ≡ 78
broaderIGAverageSpreadBpIs78 = refl

spreadPremiumBpIs37 :
  spreadPremiumBp currentAICreditSpreadDifferential ≡ 37
spreadPremiumBpIs37 = refl

spreadReconciliation : 78 + 37 ≡ 115
spreadReconciliation = refl

data SpreadPremiumCreatesDefaultPermission : Set where
data SpreadPremiumCreatesBubblePermission : Set where
data CrossSectionIdentifiesCausalAIPremiumPermission : Set where

spreadPremiumDoesNotCreateDefault : SpreadPremiumCreatesDefaultPermission → ⊥
spreadPremiumDoesNotCreateDefault ()

spreadPremiumDoesNotCreateBubble : SpreadPremiumCreatesBubblePermission → ⊥
spreadPremiumDoesNotCreateBubble ()

crossSectionDoesNotIdentifyCausalAIPremium : CrossSectionIdentifiesCausalAIPremiumPermission → ⊥
crossSectionDoesNotIdentifyCausalAIPremium ()

boundary : String
boundary =
  "Reuters reports a contemporaneous cross-sectional credit-market coordinate of roughly 115 bp average spread for AI-linked corporate bonds versus roughly 78 bp for broader investment grade, a DASHI-derived 37 bp premium. This materially advances the financing-condition panel beyond anecdotes. It is not an issuer-matched causal estimate, default-rate observation, systemic-stress theorem or sector-bubble proof."
