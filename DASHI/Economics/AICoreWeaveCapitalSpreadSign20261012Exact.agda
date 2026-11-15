module DASHI.Economics.AICoreWeaveCapitalSpreadSign20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICompanyReturnRolloverTrajectory2026Exact as Company
import DASHI.Economics.AICoreWeaveDebtCostBoundary20261012Exact as DebtCost

------------------------------------------------------------------------
-- COREWEAVE SIGN-ONLY CAPITAL-SPREAD MAX-CUT
--
-- A precise realised ROIC and WACC point still needs a declared invested-
-- capital convention, equity cost and capital weights.  The sign of the spread
-- is cheaper: H1-2026 operating income is source-paid negative, while positive
-- debt principal and positive debt rates are source-paid.  Under explicitly
-- declared standard sign conditions (positive invested capital/debt weight,
-- positive after-tax debt-cost contribution, non-negative equity contribution)
-- ROIC is negative, WACC is positive, hence ROIC-WACC is negative.
--
-- This is a qualitative/conditional capital-recovery result, not a numerical
-- WACC, ROIC, insolvency or default estimate.
------------------------------------------------------------------------

data Sign : Set where
  neg zeroSign pos unknown : Sign

positiveNat : Nat → Bool
positiveNat zero = false
positiveNat (suc _) = true

record StandardWACCSignConditions : Set where
  constructor mkStandardWACCSignConditions
  field
    investedCapitalPositive : Bool
    debtWeightPositive : Bool
    afterTaxDebtCostContributionPositive : Bool
    equityContributionNonnegative : Bool

open StandardWACCSignConditions public

inferROICSign : Bool → StandardWACCSignConditions → Sign
inferROICSign true (mkStandardWACCSignConditions true _ _ _) = neg
inferROICSign _ _ = unknown

inferWACCSign : StandardWACCSignConditions → Sign
inferWACCSign (mkStandardWACCSignConditions _ true true true) = pos
inferWACCSign _ = unknown

inferSpreadSign : Sign → Sign → Sign
inferSpreadSign neg pos = neg
inferSpreadSign _ _ = unknown

------------------------------------------------------------------------
-- Source-paid coordinates.
------------------------------------------------------------------------

coreWeaveOperatingLossObserved :
  Company.negative (Company.operatingIncome Company.coreWeaveH12026) ≡ true
coreWeaveOperatingLossObserved = refl

coreWeaveDebtPrincipalPositive :
  positiveNat (DebtCost.futurePrincipalMillionUSD DebtCost.coreWeaveDebtCostBoundary) ≡ true
coreWeaveDebtPrincipalPositive = refl

coreWeaveDebtRatePositive :
  positiveNat (DebtCost.selectedNonconvertibleRateMinBp DebtCost.coreWeaveDebtCostBoundary) ≡ true
coreWeaveDebtRatePositive = refl

------------------------------------------------------------------------
-- Standard sign-model declaration.
--
-- Positive invested capital and debt weight are justified here only at sign
-- level by the source-paid positive debt principal.  The positive after-tax
-- debt contribution and non-negative equity contribution are explicit model
-- conditions; they are not silently promoted to measured WACC inputs.
------------------------------------------------------------------------

standardWACCSignConditions : StandardWACCSignConditions
standardWACCSignConditions = mkStandardWACCSignConditions
  (positiveNat (DebtCost.futurePrincipalMillionUSD DebtCost.coreWeaveDebtCostBoundary))
  (positiveNat (DebtCost.futurePrincipalMillionUSD DebtCost.coreWeaveDebtCostBoundary))
  (positiveNat (DebtCost.selectedNonconvertibleRateMinBp DebtCost.coreWeaveDebtCostBoundary))
  true

coreWeaveROICSignNegative :
  inferROICSign
    (Company.negative (Company.operatingIncome Company.coreWeaveH12026))
    standardWACCSignConditions
  ≡ neg
coreWeaveROICSignNegative = refl

coreWeaveWACCSignPositive :
  inferWACCSign standardWACCSignConditions ≡ pos
coreWeaveWACCSignPositive = refl

coreWeaveCapitalSpreadSignNegative :
  inferSpreadSign
    (inferROICSign
      (Company.negative (Company.operatingIncome Company.coreWeaveH12026))
      standardWACCSignConditions)
    (inferWACCSign standardWACCSignConditions)
  ≡ neg
coreWeaveCapitalSpreadSignNegative = refl

------------------------------------------------------------------------
-- Numerical closure remains separate.
------------------------------------------------------------------------

record CapitalSpreadClosureBoundary : Set where
  constructor capitalSpreadClosureBoundary
  field
    signClosedUnderDeclaredConditions : Bool
    numericROICClosed : Bool
    numericWACCClosed : Bool
    numericROICMinusWACCClosed : Bool
    insolvencyEstablished : Bool

open CapitalSpreadClosureBoundary public

coreWeaveCapitalSpreadClosure : CapitalSpreadClosureBoundary
coreWeaveCapitalSpreadClosure = capitalSpreadClosureBoundary true false false false false

numericROICStillOpen : numericROICClosed coreWeaveCapitalSpreadClosure ≡ false
numericROICStillOpen = refl

numericWACCStillOpen : numericWACCClosed coreWeaveCapitalSpreadClosure ≡ false
numericWACCStillOpen = refl

data NegativeSpreadImpliesInsolvencyPermission : Set where

data SignClosureImpliesNumericClosurePermission : Set where

negativeSpreadDoesNotAutoProveInsolvency : NegativeSpreadImpliesInsolvencyPermission → ⊥
negativeSpreadDoesNotAutoProveInsolvency ()

signClosureDoesNotAutoCreateNumericSpread : SignClosureImpliesNumericClosurePermission → ⊥
signClosureDoesNotAutoCreateNumericSpread ()

boundary : String
boundary =
  "CoreWeave H1-2026 has a source-paid operating loss and source-paid positive debt principal/rates. Under declared standard sign conditions this is sufficient to close the sign of ROIC-WACC as negative. Numerical realised ROIC, WACC and spread remain open and require invested-capital/equity-cost/weight measurements."
