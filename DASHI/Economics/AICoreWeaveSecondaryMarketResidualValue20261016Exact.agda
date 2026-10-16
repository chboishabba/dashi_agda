module DASHI.Economics.AICoreWeaveSecondaryMarketResidualValue20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

commercialMarketKind : Source.SourceKind
commercialMarketKind = Source.namedSourceKind "commercial secondary-market / pricing index"

usedGPUIndexSource : Source.AttributedSource
usedGPUIndexSource = Source.mkNoDOISource
  "Sell Server Equipment"
  "Used Server & GPU Price Index"
  "commercial used-hardware price index"
  "2026-07-25"
  "https://sellserverequipment.com/price-index/"
  commercialMarketKind
  "indicative used-market ranges: H100 SXM5 USD18k-30k, H200 SXM USD26k-38k, B200 SXM USD32k-48k; commercial market indication rather than audited transaction ledger or CoreWeave-specific sale"
  Source.publicAttribution

cloudPriceIndexSource : Source.AttributedSource
cloudPriceIndexSource = Source.mkNoDOISource
  "CCIR"
  "GPU Price Pages: H100, H200, B200, A100"
  "commercial cloud/secondary hardware price instrument"
  "2026-10-14"
  "https://ccir.io/chips"
  commercialMarketKind
  "selected T2 neocloud spot median GPU-hour observations: H100 USD3.33, H200 USD4.47, B200 USD6.69; market index rather than CoreWeave realised ASP or utilisation"
  Source.publicAttribution

record SecondaryResidualObservation : Set where
  constructor secondary-residual-observation
  field
    generation : String
    usedLowUSD : Nat
    usedHighUSD : Nat
    spotMedianCentsPerGPUHour : Nat
    lowGrossRentalHoursToUsedValue : Nat
    highGrossRentalHoursToUsedValue : Nat
    currentSecondaryMarketExists : Bool
    currentRentalMarketExists : Bool
    coreWeaveOwnedUnitIdentified : Bool
    realisedCoreWeaveSalePaid : Bool
    realisedUtilisationPaid : Bool
    fullTCOIncluded : Bool
    impairmentEstablished : Bool

open SecondaryResidualObservation public

h100ResidualObservation : SecondaryResidualObservation
h100ResidualObservation = secondary-residual-observation
  "H100 SXM" 18000 30000 333 5405 9009 true true false false false false false

h200ResidualObservation : SecondaryResidualObservation
h200ResidualObservation = secondary-residual-observation
  "H200 SXM" 26000 38000 447 5816 8501 true true false false false false false

b200ResidualObservation : SecondaryResidualObservation
b200ResidualObservation = secondary-residual-observation
  "B200 SXM" 32000 48000 669 4783 7174 true true false false false false false

secondaryMarketSurvivalPaid :
  (currentSecondaryMarketExists h100ResidualObservation ≡ true) ×
  (currentSecondaryMarketExists h200ResidualObservation ≡ true) ×
  (currentSecondaryMarketExists b200ResidualObservation ≡ true)
secondaryMarketSurvivalPaid = refl , refl , refl

coreWeaveResidualValueStillOpen : realisedCoreWeaveSalePaid h100ResidualObservation ≡ false
coreWeaveResidualValueStillOpen = refl

utilisationStillOpen : realisedUtilisationPaid h100ResidualObservation ≡ false
utilisationStillOpen = refl

data SecondaryQuoteDeterminesCoreWeaveResidualPermission : Set where
data GrossRentalHoursDetermineProfitabilityPermission : Set where
data SecondaryMarketImpliesNoObsolescencePermission : Set where

secondaryQuoteDoesNotDetermineCoreWeaveResidual : SecondaryQuoteDeterminesCoreWeaveResidualPermission → ⊥
secondaryQuoteDoesNotDetermineCoreWeaveResidual ()

grossRentalHoursDoNotDetermineProfitability : GrossRentalHoursDetermineProfitabilityPermission → ⊥
grossRentalHoursDoNotDetermineProfitability ()

secondaryMarketDoesNotEraseObsolescence : SecondaryMarketImpliesNoObsolescencePermission → ⊥
secondaryMarketDoesNotEraseObsolescence ()

boundary : String
boundary =
  "Commercial 2026 market indices show an active secondary market and ongoing rental market for H100/H200/B200. Combining indicative used-unit ranges with contemporaneous spot GPU-hour medians yields a hardware-only gross-rental-hours envelope of roughly 4.8k-9.0k hours, or about 0.55-1.03 years at hypothetical 100-percent utilisation. This is evidence that older accelerators can retain economic option value, not a CoreWeave realised residual-value ledger, utilisation observation, impairment test, profitability estimate or replacement-capex payment. Electricity, host/network/storage, PUE, labour, financing, taxes, downtime, maintenance and margin are excluded."