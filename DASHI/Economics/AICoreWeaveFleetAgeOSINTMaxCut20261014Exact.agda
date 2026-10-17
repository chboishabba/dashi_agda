module DASHI.Economics.AICoreWeaveFleetAgeOSINTMaxCut20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Economics.AICoreWeaveOSINTCapacityVintage20261014Exact as Capacity
import DASHI.Economics.AICoreWeaveCapacityHardwareAgeNonDescent20261014Exact as NonDescent
import DASHI.Economics.AICoreWeaveGPUGenerationCadence20261014Exact as Generation
import DASHI.Economics.AICoreWeaveBookStockYouth20261014Exact as Book
import DASHI.Economics.AICoreWeaveVintageWall20261014Exact as Wall
import DASHI.Economics.AICoreWeaveMultiGenerationCommercialCoexistence20261014Exact as Coexistence
import DASHI.Economics.AICoreWeaveGenerationPriceLadder20261014Exact as Price
import DASHI.Economics.AICoreWeaveSameObjectFinancingClock20261016Exact as FinanceClock

record FleetAgeOSINTStatus : Set where
  constructor fleet-age-osint-status
  field
    capacityVintageDistributionPaid : Bool
    capacityMedianAgeIntervalPaid : Bool
    capacityWeightedMeanAgeIntervalPaid : Bool
    bookStockYouthProxyPaid : Bool
    frontierGenerationCadencePaid : Bool
    multiGenerationCommercialCoexistencePaid : Bool
    commercialGenerationPriceCrossSectionPaid : Bool
    capacityToHardwareNonDescentPaid : Bool
    selected36To48MonthVintageWallPaid : Bool
    sameObjectFinancingClockCorrectionPaid : Bool
    exactSerialHardwareAgeDistributionPaid : Bool
    actualRefreshRetirementHistoryPaid : Bool
    growthVsReplacementCapitalisationPaid : Bool
    longitudinalGenerationPriceDecayPaid : Bool
    economicObsolescenceCashBurdenPaid : Bool

open FleetAgeOSINTStatus public

coreWeaveFleetAgeOSINTStatus : FleetAgeOSINTStatus
coreWeaveFleetAgeOSINTStatus = fleet-age-osint-status
  true true true true true true true true true true
  false false false false false

capacityVintageIsNowPaid : capacityVintageDistributionPaid coreWeaveFleetAgeOSINTStatus ≡ true
capacityVintageIsNowPaid = refl

exactHardwareAgeStillOpen : exactSerialHardwareAgeDistributionPaid coreWeaveFleetAgeOSINTStatus ≡ false
exactHardwareAgeStillOpen = refl

refreshHistoryStillOpen : actualRefreshRetirementHistoryPaid coreWeaveFleetAgeOSINTStatus ≡ false
refreshHistoryStillOpen = refl

selectedCapacityMedianIs6To12Months :
  (Capacity.medianCapacityVintageAgeLowerMonths Capacity.coreWeaveJune2026CapacityVintage ≡ 6) ×
  (Capacity.medianCapacityVintageAgeUpperMonths Capacity.coreWeaveJune2026CapacityVintage ≡ 12)
selectedCapacityMedianIs6To12Months = Capacity.medianCapacityVintageAgeLowerMonthsIs6 , Capacity.medianCapacityVintageAgeUpperMonthsIs12

selectedCapacityMeanIs748To1470HundredthsMonths :
  (Capacity.weightedMeanAgeLowerHundredthsMonths Capacity.coreWeaveJune2026CapacityVintage ≡ 748) ×
  (Capacity.weightedMeanAgeUpperHundredthsMonths Capacity.coreWeaveJune2026CapacityVintage ≡ 1470)
selectedCapacityMeanIs748To1470HundredthsMonths = Capacity.weightedMeanAgeLowerHundredthsIs748 , Capacity.weightedMeanAgeUpperHundredthsIs1470

capacityCannotRecoverHardwareAge : Descent.FactorsThrough NonDescent.capacityObserver NonDescent.hardwareAgeConsumer → ⊥
capacityCannotRecoverHardwareAge = NonDescent.capacityVintageCannotFactorHardwareAge

frontierCadencePressurePaid : Generation.frontierSuccessorArrivesBeforeBookLife Generation.coreWeaveSelectedFrontierCadence ≡ true
frontierCadencePressurePaid = Generation.frontierCadenceShorterThanBookLife

multiGenerationCommercialCoexistenceIsPaid : Coexistence.h100StillOffered Coexistence.coreWeaveCurrentCommercialCoexistence ≡ true
multiGenerationCommercialCoexistenceIsPaid = Coexistence.h100StillOfferedReceipt

currentA100CommercialPriceCoordinatePaid : Price.a100PerGPUHourMills Price.coreWeaveCurrentGenerationPriceLadder ≡ 2700
currentA100CommercialPriceCoordinatePaid = Price.a100PerGPUHourMillsIs2700

bookStockProxyDoesNotCloseHardwareAge : Book.identifiesHardwareAge Book.coreWeaveBookStockYouth ≡ false
bookStockProxyDoesNotCloseHardwareAge = refl

selectedVintageWallShareIs5666Bp : Wall.selectedCumulativeShareBp Wall.coreWeaveSelectedVintageWall ≡ 5666
selectedVintageWallShareIs5666Bp = Wall.selectedShareBpIs5666

sameObjectFinancingClockCorrectionIsPaid : sameObjectFinancingClockCorrectionPaid coreWeaveFleetAgeOSINTStatus ≡ true
sameObjectFinancingClockCorrectionIsPaid = refl

sameObjectSixYearClockPaid : FinanceClock.commonObservedContractualGPUUsefulLifeMonths FinanceClock.coreWeaveSameObjectFinancingClock ≡ 72
sameObjectSixYearClockPaid = FinanceClock.sameObjectSixYearDepreciationPaid

longitudinalPriceDecayStillOpen : longitudinalGenerationPriceDecayPaid coreWeaveFleetAgeOSINTStatus ≡ false
longitudinalPriceDecayStillOpen = refl

boundary : String
boundary =
  "The CoreWeave installed-age residual is materially reduced rather than simply unknown. Public power disclosures pay a capacity-vintage distribution with a selected June-2026 median in the 6-12 month band and an interval-weighted mean of about 7.48-14.70 months. Filing book-stock growth independently indicates a rapidly expanding/young capital base, while public H100/H200/GB200/GB300/Rubin milestones pay a frontier-generation cadence much shorter than the 72-month accounting life. Current commercial listings simultaneously show older and Blackwell generations and supply a same-date selected per-GPU listed-price ladder, blocking a hard successor-arrival retirement cliff. The selected 36/48-month vintage wall is retained only as a generic market-horizon stress scenario: primary CoreWeave GPU-backed credit agreements now pay same-object contractual depreciation bases of roughly 66-78 months, commonly six years, so the earlier 24-36 month CoreWeave accounting-versus-financing mismatch is not promotable. Canonical non-descent still blocks exact hardware-age recovery when in-place refresh is possible. Serial-level age/generation shares, actual retirements/refreshes, replacement-vs-growth capitalisation, longitudinal realised utilisation/ASP/resale and economic-obsolescence cash burden remain empirical."
