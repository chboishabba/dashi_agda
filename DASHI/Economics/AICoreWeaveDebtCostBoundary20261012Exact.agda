module DASHI.Economics.AICoreWeaveDebtCostBoundary20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AttributedSourceCore as Source

secFilingKind : Source.SourceKind
secFilingKind = Source.namedSourceKind "primary SEC filing"

coreWeaveDebtSource : Source.AttributedSource
coreWeaveDebtSource = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Quarterly report for period ended June 30 2026"
  "SEC Form 10-Q"
  "2026"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000366/crwv-20260630.htm"
  secFilingKind
  "primary carrier for H1 contractual/reported debt interest, total principal maturity schedule, and effective/stated rates on selected debt instruments"
  Source.publicAttribution

record DebtCostBoundary : Set where
  constructor debtCostBoundary
  field
    contractualInterestMillionUSD : Nat
    reportedInterestMillionUSD : Nat
    futurePrincipalMillionUSD : Nat
    selectedNonconvertibleRateMinBp : Nat
    selectedNonconvertibleRateMaxBp : Nat
    debtCostSurfaceClosed : Bool
    waccClosed : Bool
    realisedROICClosed : Bool
    roicMinusWaccClosed : Bool

open DebtCostBoundary public

coreWeaveDebtCostBoundary : DebtCostBoundary
coreWeaveDebtCostBoundary = debtCostBoundary
  1075 985 35551 850 1500 true false false false

data DebtCostImpliesWACCPermission : Set where
data DebtCostImpliesROICPermission : Set where

debtCostDoesNotAutoCreateWACC : DebtCostImpliesWACCPermission → ⊥
debtCostDoesNotAutoCreateWACC ()

debtCostDoesNotAutoCreateROIC : DebtCostImpliesROICPermission → ⊥
debtCostDoesNotAutoCreateROIC ()

debtSurfaceIsPaid : debtCostSurfaceClosed coreWeaveDebtCostBoundary ≡ true
debtSurfaceIsPaid = refl

waccStillOpen : waccClosed coreWeaveDebtCostBoundary ≡ false
waccStillOpen = refl

capitalSpreadStillOpen : roicMinusWaccClosed coreWeaveDebtCostBoundary ≡ false
capitalSpreadStillOpen = refl
