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

record FleetAgeOSINTStatus : Set where
  constructor fleet-age-osint-status
  field
    capacityVintageDistributionPaid : Bool
    capacityMedianAgeIntervalPaid : Bool
    capacityWeightedMeanAgeIntervalPaid : Bool
    bookStockYouthProxyPaid : Bool
    frontierGenerationCadencePaid : Bool
    multiGenerationCommercialCoexistencePaid : Bool
    capacityToHardwareNonDescentPaid : Bool
    selected36To48MonthVintageWallPaid : Bool
    exactSerialHardwareAgeDistributionPaid : Bool
    actualRefreshRetirementHistoryPaid : Bool
    growthVsReplacementCapitalisationPaid : Bool
    economicObsolescenceCashBurdenPaid : Bool

open FleetAgeOSINTStatus public

coreWeaveFleetAgeOSINTStatus : FleetAgeOSINTStatus
coreWeaveFleetAgeOSINTStatus = fleet-age-osint-status
  true true true true true true true true
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
  Descent.FactorsThrough NonDescent.capacityObserver NonDescent.hardwareAgeConsumer → ⊥
capacityCannotRecoverHardwareAge = NonDescent.capacityVintageCannotFactorHardwareAge

frontierCadencePressurePaid :
  Generation.frontierSuccessorArrivesBeforeBookLife Generation.coreWeaveSelectedFrontierCadence ≡ true
frontierCadencePressurePaid = Generation.frontierCadenceShorterThanBookLife

multiGenerationCommercialCoexistenceIsPaid :
  Coexistence.h100StillOffered Coexistence.coreWeaveCurrentCommercialCoexistence ≡ true
multiGenerationCommercialCoexistenceIsPaid = Coexistence.h100StillOfferedReceipt

bookStockProxyDoesNotCloseHardwareAge :
  Book.identifiesHardwareAge Book.coreWeaveBookStockYouth ≡ false
bookStockProxyDoesNotCloseHardwareAge = refl

selectedVintageWallShareIs5666Bp :
  Wall.selectedCumulativeShareBp Wall.coreWeaveSelectedVintageWall ≡ 5666
selectedVintageWallShareIs5666Bp = Wall.selectedShareBpIs5666

boundary : String
boundary =
  "The CoreWeave installed-age residual is materially reduced rather than simply unknown. Public power disclosures pay a capacity-vintage distribution with a selected June-2026 median in the 6-12 month band and an interval-weighted mean of about 7.48-14.70 months. Filing book-stock growth independently indicates a rapidly expanding/young capital base, while public H100/H200/GB200/GB300/Rubin milestones pay a frontier-generation cadence much shorter than the 72-month accounting life. Current commercial listings simultaneously show A100/H100/H200 and Blackwell generations remaining offered after Rubin production began, so the appropriate obsolescence model is not a hard successor-arrival retirement cliff. Composing capacity vintages with the separately sourced 36-48 month lender horizon yields a dated exposure wall: 56.66 percent of the selected 1.5GW floor has entered the 36-month window by end-2028, and the same share has entered the 48-month window by end-2029. Canonical non-descent still blocks exact hardware-age recovery when in-place refresh is possible. Serial-level age/generation shares, actual retirements/refreshes, replacement-vs-growth capitalisation, generation-specific utilisation/price decay and realised economic-obsolescence cash burden remain empirical."
