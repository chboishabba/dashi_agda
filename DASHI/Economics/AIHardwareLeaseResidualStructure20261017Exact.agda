module DASHI.Economics.AIHardwareLeaseResidualStructure20261017Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

primaryFiledLeaseDisclosure : Source.SourceKind
primaryFiledLeaseDisclosure = Source.namedSourceKind "GPU lease disclosure in SEC-filed annual report"

irenLeaseSource : Source.AttributedSource
irenLeaseSource = Source.mkNoDOISource
  "IREN Limited"
  "Annual Report for year ended June 30 2026 — GPU equipment leasing arrangements"
  "SEC-filed annual report"
  "2026-06-30"
  "https://www.sec.gov/Archives/edgar/data/1878848/000187884826000052/iren-20260630.htm"
  primaryFiledLeaseDisclosure
  "IREN disclosed an approximately 102 million dollar 36-month GPU lease with a purchase option at the lower of fair market value and 18 percent of initial purchase price; a separate approximately 96 million dollar 24-month GPU lease and an approximately 200 million dollar 24-month lease each include a 1 dollar purchase option at maturity."
  Source.publicAttribution

record HardwareLeaseResidualStructure : Set where
  constructor hardware-lease-residual-structure
  field
    label : String
    initialFinancingUSDm : Nat
    termMonths : Nat
    fmvOrPercentOption : Bool
    percentCapOfInitialPrice : Nat
    percentCapOptionUSDhundredthsM : Nat
    oneDollarBuyout : Bool
    realisedExercisePaid : Bool
    realisedMarketResalePaid : Bool
    economicResidualValuePaid : Bool

open HardwareLeaseResidualStructure public

iren36MonthLease : HardwareLeaseResidualStructure
iren36MonthLease = hardware-lease-residual-structure
  "IREN Aug-2025 36-month GPU lease" 102 36 true 18 1836 false false false false

iren24MonthLease : HardwareLeaseResidualStructure
iren24MonthLease = hardware-lease-residual-structure
  "IREN Aug-2025 24-month GPU lease" 96 24 false 0 0 true false false false

irenDell24MonthLease : HardwareLeaseResidualStructure
irenDell24MonthLease = hardware-lease-residual-structure
  "IREN Nov-2025 24-month GPU lease" 200 24 false 0 0 true false false false

fmvCappedOptionPaid : fmvOrPercentOption iren36MonthLease ≡ true
fmvCappedOptionPaid = refl

oneDollarOptionPaid : oneDollarBuyout iren24MonthLease ≡ true
oneDollarOptionPaid = refl

contractual18PercentCapIs1836HundredthsM : percentCapOptionUSDhundredthsM iren36MonthLease ≡ 1836
contractual18PercentCapIs1836HundredthsM = refl

record LeaseResidualBoundary : Set where
  constructor lease-residual-boundary
  field
    optionPriceEqualsMarketResidual : Bool
    oneDollarBuyoutMeansZeroEconomicValue : Bool
    leaseTerminalStructureCanStandInForResaleReceipt : Bool
    oneResidualRateFitsAllGPUFinance : Bool

open LeaseResidualBoundary public

currentLeaseResidualBoundary : LeaseResidualBoundary
currentLeaseResidualBoundary = lease-residual-boundary false false false false

optionDoesNotEqualMarketResidual : optionPriceEqualsMarketResidual currentLeaseResidualBoundary ≡ false
optionDoesNotEqualMarketResidual = refl

data OptionPriceEqualsSalvagePermission : Set where
data OneDollarMeansZeroValuePermission : Set where

optionPriceDoesNotCreateSalvage : OptionPriceEqualsSalvagePermission → ⊥
optionPriceDoesNotCreateSalvage ()

oneDollarBuyoutDoesNotCreateZeroValue : OneDollarMeansZeroValuePermission → ⊥
oneDollarBuyoutDoesNotCreateZeroValue ()

boundary : String
boundary =
  "IREN's primary SEC filing supplies same-company GPU lease structures with very different contractual terminal-value allocations: one 36-month lease has a purchase option at the lower of fair market value and 18 percent of initial price, while separate 24-month leases use one-dollar buyouts. DASHI derives only the 18-percent-of-102-million contractual cap of 18.36 million dollars. These are financing-contract terminal terms, not realised market resale values or audited salvage proceeds. A one-dollar buyout does not imply the GPU has zero economic value; an FMV-or-18-percent option does not imply realised salvage equals 18 percent; and no universal GPU residual-rate assumption is promoted across financing structures."
