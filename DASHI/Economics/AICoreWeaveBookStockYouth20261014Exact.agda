module DASHI.Economics.AICoreWeaveBookStockYouth20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

secFilingKind : Source.SourceKind
secFilingKind = Source.namedSourceKind "primary SEC filing"

coreWeave2025AnnualReportSource : Source.AttributedSource
coreWeave2025AnnualReportSource = Source.mkNoDOISource
  "CoreWeave, Inc." "Annual report for year ended December 31 2025" "SEC Form 10-K" "2026-03-02"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000104/crwv-20251231.htm"
  secFilingKind
  "primary carrier for gross technology equipment USD20.903B vs USD9.146B, total gross PP&E USD33.941B, construction-in-progress USD9.376B, accumulated depreciation/amortization USD3.384B, and net PP&E USD30.557B"
  Source.publicAttribution

coreWeaveQ22026Source : Source.AttributedSource
coreWeaveQ22026Source = Source.mkNoDOISource
  "CoreWeave, Inc." "Quarterly report for quarter ended June 30 2026" "SEC Form 10-Q" "2026-08-12"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000366/crwv-20260630.htm"
  secFilingKind
  "primary carrier for net PP&E USD46.736B at June 30 2026"
  Source.publicAttribution

record BookStockYouthObservation : Set where
  constructor book-stock-youth-observation
  field
    technologyEquipment2024MillionUSD : Nat
    technologyEquipment2025MillionUSD : Nat
    technologyEquipmentNetGrowthMillionUSD : Nat
    technologyEquipmentNetGrowthShareBpOf2025Stock : Nat
    grossPPE2025MillionUSD : Nat
    constructionInProgress2025MillionUSD : Nat
    accumulatedDA2025MillionUSD : Nat
    accumulatedDAShareBpOfDepreciableGrossPPE : Nat
    netPPE2025MillionUSD : Nat
    netPPEH12026MillionUSD : Nat
    h12026NetPPEGrowthBpVs2025 : Nat
    identifiesHardwareAge : Bool
    identifiesReplacementCapex : Bool
    identifiesRetirementHistory : Bool

open BookStockYouthObservation public

coreWeaveBookStockYouth : BookStockYouthObservation
coreWeaveBookStockYouth = book-stock-youth-observation
  9146 20903 11757 5624
  33941 9376 3384 1377
  30557 46736 5294
  false false false

technologyEquipmentNetGrowthShareBpIs5624 :
  technologyEquipmentNetGrowthShareBpOf2025Stock coreWeaveBookStockYouth ≡ 5624
technologyEquipmentNetGrowthShareBpIs5624 = refl

accumulatedDAShareBpIs1377 :
  accumulatedDAShareBpOfDepreciableGrossPPE coreWeaveBookStockYouth ≡ 1377
accumulatedDAShareBpIs1377 = refl

h12026NetPPEGrowthBpIs5294 :
  h12026NetPPEGrowthBpVs2025 coreWeaveBookStockYouth ≡ 5294
h12026NetPPEGrowthBpIs5294 = refl

data BookStockYouthImpliesHardwareAgePermission : Set where
data GrossGrowthImpliesReplacementCapexPermission : Set where

bookStockYouthDoesNotIdentifyHardwareAge : BookStockYouthImpliesHardwareAgePermission → ⊥
bookStockYouthDoesNotIdentifyHardwareAge ()

grossGrowthDoesNotIdentifyReplacementCapex : GrossGrowthImpliesReplacementCapexPermission → ⊥
grossGrowthDoesNotIdentifyReplacementCapex ()

boundary : String
boundary =
  "CoreWeave's book stock is also very rapidly expanding: gross technology equipment rose from USD9.146B to USD20.903B during 2025, a net increase equal to 56.24 percent of the ending gross technology-equipment balance; accumulated D&A was 13.77 percent of gross PP&E excluding CIP; net PP&E then rose another 52.94 percent by June 30 2026. These are book-stock youth/expansion proxies, not an installed-hardware age register: mixed asset classes, useful lives, CIP, disposals, reclassifications and replacement/growth capex remain unresolved."
