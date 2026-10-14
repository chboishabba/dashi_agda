module DASHI.Economics.AICoreWeaveOSINTCapacityVintage20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- COREWEAVE OSINT CAPACITY-VINTAGE INFERENCE
--
-- Public cumulative active-power disclosures can recover a capacity-weighted
-- deployment-vintage distribution without an internal asset register.  This is
-- useful evidence about the age of deployed capacity, but it is deliberately
-- NOT identified with serial-level GPU age: refresh/replacement/repurposing can
-- happen inside an already-active MW footprint, and net MW growth can hide
-- retirements.
------------------------------------------------------------------------

secFilingKind : Source.SourceKind
secFilingKind = Source.namedSourceKind "primary SEC filing / investor presentation"

coreWeave2025AnnualReportSource : Source.AttributedSource
coreWeave2025AnnualReportSource = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Annual report for year ended December 31 2025"
  "SEC Form 10-K"
  "2026-03-02"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000104/crwv-20251231.htm"
  secFilingKind
  "primary carrier for cumulative active power: about 70 MW at 2023-12-31, more than 360 MW at 2024-12-31, and more than 850 MW at 2025-12-31; also carrier for six-year technology-equipment accounting life"
  Source.publicAttribution

coreWeaveQ12025PresentationSource : Source.AttributedSource
coreWeaveQ12025PresentationSource = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Q1 2025 investor presentation"
  "SEC furnished presentation"
  "2025"
  "https://www.sec.gov/Archives/edgar/data/1769628/000119312525122115/d19327dex992.htm"
  secFilingKind
  "primary carrier for about 10 MW at 2022-12-31 and about 420 MW at 2025-03-31, together with historical GPU-online counts"
  Source.publicAttribution

coreWeaveJune2025Source : Source.AttributedSource
coreWeaveJune2025Source = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Registration statement / June 30 2025 infrastructure disclosure"
  "SEC filing"
  "2025"
  "https://www.sec.gov/Archives/edgar/data/1769628/000114036125032095/ny20053122x1_s4.htm"
  secFilingKind
  "primary carrier for approximately 470 MW active power as of 2025-06-30"
  Source.publicAttribution

coreWeaveJune2026PresentationSource : Source.AttributedSource
coreWeaveJune2026PresentationSource = Source.mkNoDOISource
  "CoreWeave, Inc."
  "2026 convertible financing presentation"
  "SEC furnished presentation"
  "2026"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000429/crwv2026convertpresentat.htm"
  secFilingKind
  "primary carrier for 51 active data centers and 1.5GW+ active power as of 2026-06-30; the 1.5GW value is used only as a conservative floor"
  Source.publicAttribution

record CapacityVintageCohort : Set where
  constructor capacity-vintage-cohort
  field
    label : String
    incrementalMW : Nat
    minimumAgeMonths : Nat
    maximumAgeMonths : Nat
    sourceRef : String

open CapacityVintageCohort public

through2022 : CapacityVintageCohort
through2022 = capacity-vintage-cohort "through-2022" 10 42 54 "~10 MW at 2022-12-31"

cohort2023 : CapacityVintageCohort
cohort2023 = capacity-vintage-cohort "2023" 60 30 42 "70 - 10 MW cumulative increment"

cohort2024 : CapacityVintageCohort
cohort2024 = capacity-vintage-cohort "2024" 290 18 30 "360 - 70 MW cumulative increment"

cohort2025Q1 : CapacityVintageCohort
cohort2025Q1 = capacity-vintage-cohort "2025-Q1" 60 15 18 "420 - 360 MW cumulative increment"

cohort2025Q2 : CapacityVintageCohort
cohort2025Q2 = capacity-vintage-cohort "2025-Q2" 50 12 15 "470 - 420 MW cumulative increment"

cohort2025H2 : CapacityVintageCohort
cohort2025H2 = capacity-vintage-cohort "2025-H2" 380 6 12 "850 - 470 MW conservative-floor increment"

cohort2026H1 : CapacityVintageCohort
cohort2026H1 = capacity-vintage-cohort "2026-H1" 650 0 6 "1500 - 850 MW conservative-floor increment"

record CapacityVintageInference : Set where
  constructor capacity-vintage-inference
  field
    company : String
    asOf : String
    conservativeTotalActiveMW : Nat
    capacityAddedSince2025MW : Nat
    capacityAddedSince2025ShareBp : Nat
    capacityAddedSince2024MW : Nat
    capacityAddedSince2024ShareBp : Nat
    medianCapacityVintageAgeLowerMonths : Nat
    medianCapacityVintageAgeUpperMonths : Nat
    weightedMeanAgeLowerHundredthsMonths : Nat
    weightedMeanAgeUpperHundredthsMonths : Nat
    capacityVintageDistributionPaid : Bool
    hardwareAgeDistributionPaid : Bool
    capacityVintageIsHardwareVintage : Bool
    retirementRefreshHistoryPaid : Bool
    activePowerIsGPUCount : Bool
    netCapacityIncrementCanHideRetirement : Bool

open CapacityVintageInference public

coreWeaveJune2026CapacityVintage : CapacityVintageInference
coreWeaveJune2026CapacityVintage = capacity-vintage-inference
  "CoreWeave"
  "2026-06-30"
  1500
  1140 7600
  1430 9533
  6 12
  748 1470
  true false false false false true

capacityAddedSince2025ShareBpIs7600 :
  capacityAddedSince2025ShareBp coreWeaveJune2026CapacityVintage ≡ 7600
capacityAddedSince2025ShareBpIs7600 = refl

capacityAddedSince2024ShareBpIs9533 :
  capacityAddedSince2024ShareBp coreWeaveJune2026CapacityVintage ≡ 9533
capacityAddedSince2024ShareBpIs9533 = refl

medianCapacityVintageAgeLowerMonthsIs6 :
  medianCapacityVintageAgeLowerMonths coreWeaveJune2026CapacityVintage ≡ 6
medianCapacityVintageAgeLowerMonthsIs6 = refl

medianCapacityVintageAgeUpperMonthsIs12 :
  medianCapacityVintageAgeUpperMonths coreWeaveJune2026CapacityVintage ≡ 12
medianCapacityVintageAgeUpperMonthsIs12 = refl

weightedMeanAgeLowerHundredthsIs748 :
  weightedMeanAgeLowerHundredthsMonths coreWeaveJune2026CapacityVintage ≡ 748
weightedMeanAgeLowerHundredthsIs748 = refl

weightedMeanAgeUpperHundredthsIs1470 :
  weightedMeanAgeUpperHundredthsMonths coreWeaveJune2026CapacityVintage ≡ 1470
weightedMeanAgeUpperHundredthsIs1470 = refl

data CapacityVintageImpliesHardwareAgePermission : Set where
data NetCapacityGrowthImpliesNoRetirementsPermission : Set where
data ActivePowerImpliesGPUCountPermission : Set where

data YoungCapacityImpliesNoObsolescencePermission : Set where

capacityVintageDoesNotIdentifyHardwareAge :
  CapacityVintageImpliesHardwareAgePermission → ⊥
capacityVintageDoesNotIdentifyHardwareAge ()

netCapacityGrowthDoesNotIdentifyNoRetirements :
  NetCapacityGrowthImpliesNoRetirementsPermission → ⊥
netCapacityGrowthDoesNotIdentifyNoRetirements ()

activePowerDoesNotIdentifyGPUCount : ActivePowerImpliesGPUCountPermission → ⊥
activePowerDoesNotIdentifyGPUCount ()

youngCapacityDoesNotEliminateObsolescence : YoungCapacityImpliesNoObsolescencePermission → ⊥
youngCapacityDoesNotEliminateObsolescence ()

boundary : String
boundary =
  "Public cumulative active-power disclosures recover a conservative capacity-vintage distribution at 2026-06-30: 76 percent of the selected 1.5GW floor was added since 2025-01-01 and 95.33 percent since 2024-01-01; the capacity-weighted median vintage lies in 6-12 months and the interval-weighted mean in about 7.48-14.70 months. This identifies deployment-capacity age, not serial-level hardware age. Refreshes, replacements, repurposing, density changes and retirements can occur inside an existing MW footprint, so actual GPU installed-age and replacement history remain separate empirical coordinates."
