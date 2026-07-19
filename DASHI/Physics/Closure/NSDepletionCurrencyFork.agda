module DASHI.Physics.Closure.NSDepletionCurrencyFork where

open import Agda.Primitive using (Set)

import DASHI.Physics.Closure.NSCoherenceBudgetResidenceReduction as Residence

------------------------------------------------------------------------
-- Replacement-currency fork for the coherence-budget residence argument.
--
-- The first empirical candidate
--
--   max (- A-dot-self-advective) 0
--
-- was falsified on the positive-transfer Galerkin triad.  The analytic lane
-- may instead prove dangerous-transfer expenditure in any one of four
-- gauge-invariant candidate currencies.  This module does not assert that a
-- currency works.  It proves that a selected, proved currency lower bound
-- plugs into the already verified residence reduction without changing the
-- downstream algebra.
------------------------------------------------------------------------

data DepletionCurrencyBranch : Set where
  directionTurnoverCurrency : DepletionCurrencyBranch
  spectralProjectorTurnoverCurrency : DepletionCurrencyBranch
  crossShellCoherenceCurrency : DepletionCurrencyBranch
  middleSimpleSpectrumCurrency : DepletionCurrencyBranch

record DepletionCurrencyFamily
    (A : Residence.OrderedBudgetArithmetic) : Set₁ where
  field
    directionTurnover : Residence.Scalar A
    spectralProjectorTurnover : Residence.Scalar A
    crossShellCoherence : Residence.Scalar A
    middleSimpleSpectrumAlignment : Residence.Scalar A

open DepletionCurrencyFamily public

currencyValue :
  {A : Residence.OrderedBudgetArithmetic} →
  DepletionCurrencyFamily A →
  DepletionCurrencyBranch →
  Residence.Scalar A
currencyValue family directionTurnoverCurrency =
  directionTurnover family
currencyValue family spectralProjectorTurnoverCurrency =
  spectralProjectorTurnover family
currencyValue family crossShellCoherenceCurrency =
  crossShellCoherence family
currencyValue family middleSimpleSpectrumCurrency =
  middleSimpleSpectrumAlignment family

record SelectedCurrencyResidenceInputs
    (A : Residence.OrderedBudgetArithmetic) : Set₁ where
  field
    currencies : DepletionCurrencyFamily A
    selectedCurrency : DepletionCurrencyBranch

    absorptionMargin : Residence.Scalar A
    dangerCost : Residence.Scalar A
    dangerousResidence : Residence.Scalar A
    budgetUpper : Residence.Scalar A

    absorptionMarginNonnegative :
      Residence._≤_ A (Residence.zero A) absorptionMargin

    dangerousTransferConsumesSelectedCurrency :
      Residence._≤_ A
        (Residence._*_ A dangerCost dangerousResidence)
        (currencyValue currencies selectedCurrency)

    selectedCurrencyRemainderAbsorbed :
      Residence._≤_ A
        (Residence._*_ A absorptionMargin
          (currencyValue currencies selectedCurrency))
        budgetUpper

open SelectedCurrencyResidenceInputs public

toCoherenceBudgetResidenceInputs :
  (A : Residence.OrderedBudgetArithmetic) →
  SelectedCurrencyResidenceInputs A →
  Residence.CoherenceBudgetResidenceInputs A
toCoherenceBudgetResidenceInputs A I =
  record
    { absorptionMargin = absorptionMargin I
    ; dangerCost = dangerCost I
    ; dangerousResidence = dangerousResidence I
    ; localDepletion = currencyValue (currencies I) (selectedCurrency I)
    ; budgetUpper = budgetUpper I
    ; absorptionMarginNonnegative = absorptionMarginNonnegative I
    ; dangerousTransferConsumesDepletion =
        dangerousTransferConsumesSelectedCurrency I
    ; pressureRemainderAbsorbedIntoBudget =
        selectedCurrencyRemainderAbsorbed I
    }

selectedDepletionCurrencyForcesResidenceBound :
  (A : Residence.OrderedBudgetArithmetic) →
  (I : SelectedCurrencyResidenceInputs A) →
  Residence._≤_ A
    (Residence._*_ A
      (Residence._*_ A (absorptionMargin I) (dangerCost I))
      (dangerousResidence I))
    (budgetUpper I)
selectedDepletionCurrencyForcesResidenceBound A I =
  Residence.coherenceBudgetForcesResidenceBound A
    (toCoherenceBudgetResidenceInputs A I)
