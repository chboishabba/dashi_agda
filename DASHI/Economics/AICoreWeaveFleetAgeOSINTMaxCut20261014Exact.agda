module DASHI.Economics.AICoreWeaveFleetAgeOSINTMaxCut20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICoreWeaveOSINTCapacityVintage20261014Exact as Capacity
import DASHI.Economics.AICoreWeaveCapacityHardwareAgeNonDescent20261014Exact as NonDescent
import DASHI.Economics.AICoreWeaveGPUGenerationCadence20261014Exact as Generation
import DASHI.Economics.AICoreWeaveBookStockYouth20261014Exact as Book

record FleetAgeOSINTStatus : Set where
  constructor fleet-age-osint-status
  field
    capacityVintageDistributionPaid : Bool
    capacityMedianAgeIntervalPaid : Bool
    capacityWeightedMeanAgeIntervalPaid : Bool
    bookStockYouthProxyPaid : Bool
    frontierGenerationCadencePaid : Bool
    capacityToHardwareNonDescentPaid : Bool
    exactSerialHardwareAgeDistributionPaid : Bool
    actualRefreshRetirementHistoryPaid : Bool
    growthVsReplacementCapitalisationPaid : Bool
    economicObsolescenceCashBurdenPaid : Bool

open FleetAgeOSINTStatus public

coreWeaveFleetAgeOSINTStatus : FleetAgeOSINTStatus
coreWeaveFleetAgeOSINTStatus = fleet-age-osint-status
  true true true true true true
  false false false false

capacityVintageIsNowPaid :
  capacityVintageDistributionPaid coreWeaveFleetAgeOSINTStatus ≡ true
capacityVintageIsNowPaid = refl

exactHardwareAgeStillOpen :
  exactSerialHardwareAgeDistributionPaid coreWeaveFleetAgeOSINTStatus ≡ false
exactHardwareAgeStillOpen = refl

refreshHistoryStillOpen :
  actualRefreshRetirementHistoryPaid coreWeaveFleetAgeOSINTStatus ≡ false
refreshHistoryStillOpen = refl

selectedCapacityMedianIs6To12Months :
  (Capacity.medianCapacityVintageAgeLowerMonths Capacity.coreWeaveJune2026CapacityVintage ≡ 6) ×
  (Capacity.medianCapacityVintageAgeUpperMonths Capacity.coreWeaveJune2026CapacityVintage ≡ 12)
selectedCapacityMedianIs6To12Months =
  Capacity.medianCapacityVintageAgeLowerMonthsIs6 ,
  Capacity.medianCapacityVintageAgeUpperMonthsIs12

selectedCapacityMeanIs748To1470HundredthsMonths :
  (Capacity.weightedMeanAgeLowerHundredthsMonths Capacity.coreWeaveJune2026CapacityVintage ≡ 748) ×
  (Capacity.weightedMeanAgeUpperHundredthsMonths Capacity.coreWeaveJune2026CapacityVintage ≡ 1470)
selectedCapacityMeanIs748To1470HundredthsMonths =
  Capacity.weightedMeanAgeLowerHundredthsIs748 ,
  Capacity.weightedMeanAgeUpperHundredthsIs1470

capacityCannotRecoverHardwareAge :
  NonDescent.Descent.FactorsThrough NonDescent.capacityObserver NonDescent.hardwareAgeConsumer → ⊥
capacityCannotRecoverHardwareAge = NonDescent.capacityVintageCannotFactorHardwareAge

frontierCadencePressurePaid :
  Generation.frontierSuccessorArrivesBeforeBookLife Generation.coreWeaveSelectedFrontierCadence ≡ true
frontierCadencePressurePaid = Generation.frontierCadenceShorterThanBookLife

bookStockProxyDoesNotCloseHardwareAge :
  Book.identifiesHardwareAge Book.coreWeaveBookStockYouth ≡ false
bookStockProxyDoesNotCloseHardwareAge = refl

boundary : String
boundary =
  "The CoreWeave installed-age residual is materially reduced rather than simply unknown. Public power disclosures pay a capacity-vintage distribution with a selected June-2026 median in the 6-12 month band and an interval-weighted mean of about 7.48-14.70 months. Filing book-stock growth independently indicates a rapidly expanding/young capital base, while public H100/H200/GB200/GB300/Rubin milestones pay a frontier-generation cadence much shorter than the 72-month accounting life. Canonical non-descent proves these observers still cannot recover exact hardware age when in-place refresh is possible. Serial-level age, actual retirements/refreshes, replacement-vs-growth capitalisation and realised economic-obsolescence cash burden remain empirical."
