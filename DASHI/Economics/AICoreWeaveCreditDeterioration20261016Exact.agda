module DASHI.Economics.AICoreWeaveCreditDeterioration20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

secondaryMarketReporting : Source.SourceKind
secondaryMarketReporting = Source.namedSourceKind "secondary market reporting"

reutersCreditSource : Source.AttributedSource
reutersCreditSource = Source.mkNoDOISource
  "Reuters"
  "AI credit worries send default insurance to record high"
  "secondary market / credit reporting"
  "2026-10-15"
  "https://www.reuters.com/business/media-telecom/global-markets-cds-ai-urgent-2026-10-15/"
  secondaryMarketReporting
  "reports CoreWeave five-year CDS above 1100bp, market-implied five-year default probability around 64 percent versus about 30 percent a year earlier, and selected bond yields peaking around 16 percent; market-implied stress is not an occurred default or audited probability model"
  Source.publicAttribution

record CoreWeaveCreditTrajectory : Set where
  constructor coreweave-credit-trajectory
  field
    priorYearFiveYearDefaultProbabilityPct : Nat
    currentFiveYearDefaultProbabilityPct : Nat
    probabilityIncreasePercentagePoints : Nat
    currentCDSSpreadLowerBoundBp : Nat
    selectedBondYieldPeakPct : Nat
    sameIssuerLongitudinalDeteriorationObserved : Bool
    actualDefaultOccurred : Bool
    refinancingFailureObserved : Bool
    causalAIOnlyAttributionPaid : Bool
    bubbleEstablished : Bool
    source : Source.AttributedSource

open CoreWeaveCreditTrajectory public

coreWeaveCreditTrajectory : CoreWeaveCreditTrajectory
coreWeaveCreditTrajectory = coreweave-credit-trajectory
  30 64 34 1100 16 true false false false false reutersCreditSource

probabilityIncreasePaid :
  currentFiveYearDefaultProbabilityPct coreWeaveCreditTrajectory ≡
  priorYearFiveYearDefaultProbabilityPct coreWeaveCreditTrajectory +
  probabilityIncreasePercentagePoints coreWeaveCreditTrajectory
probabilityIncreasePaid = refl

sameIssuerCreditDeteriorationPaid : sameIssuerLongitudinalDeteriorationObserved coreWeaveCreditTrajectory ≡ true
sameIssuerCreditDeteriorationPaid = refl

defaultStillUnrealised : actualDefaultOccurred coreWeaveCreditTrajectory ≡ false
defaultStillUnrealised = refl

data CDSImpliesDefaultPermission : Set where
data CDSTrajectoryImpliesBubblePermission : Set where
data CreditDeteriorationImpliesAICausalAttributionPermission : Set where

cdsDoesNotCreateOccurredDefault : CDSImpliesDefaultPermission → ⊥
cdsDoesNotCreateOccurredDefault ()

cdsTrajectoryDoesNotCreateBubble : CDSTrajectoryImpliesBubblePermission → ⊥
cdsTrajectoryDoesNotCreateBubble ()

creditDeteriorationDoesNotCreateAICausalAttribution : CreditDeteriorationImpliesAICausalAttributionPermission → ⊥
creditDeteriorationDoesNotCreateAICausalAttribution ()

boundary : String
boundary =
  "Reuters' October-15-2026 market reporting supplies a same-issuer longitudinal credit-stress coordinate for CoreWeave: five-year CDS-implied default probability is reported around 64 percent versus roughly 30 percent a year earlier, with CDS above 1100bp and selected bond yields peaking near 16 percent. DASHI derives the 34-percentage-point change. These are market-implied credit observations, not an occurred default, realised refinancing failure, issuer-causal AI-only effect or bubble theorem."
