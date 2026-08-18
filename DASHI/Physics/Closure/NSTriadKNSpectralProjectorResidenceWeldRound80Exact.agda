module DASHI.Physics.Closure.NSTriadKNSpectralProjectorResidenceWeldRound80Exact where

------------------------------------------------------------------------
-- ROUND80 / C4 -> C5 CROSS-POLLINATION
--
-- Repository archaeology found that NSDepletionCurrencyFork already contains
-- exactly the basis-invariant candidate suggested by Davis--Kahan:
--
--   spectralProjectorTurnoverCurrency.
--
-- NSCoherenceBudgetResidenceReduction already proves the deterministic
-- residence composition once a selected physical currency satisfies
--
--   dangerCost * dangerousResidence <= localDepletion
--   margin * localDepletion <= budgetUpper.
--
-- Therefore Round80 does not create a statistical or parallel C5 mechanism.
-- It proves that selecting spectral projector turnover feeds the existing C5
-- theorem unchanged.  The only source-facing seam is now physical: construct
-- the actual projector-turnover scalar on the selected NS trajectory and prove
-- the two inequalities above.  Davis--Kahan can help on separated clusters;
-- degeneracy must instead use a cluster-invariant turnover or a residual.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSCoherenceBudgetResidenceReduction as Residence
import DASHI.Physics.Closure.NSDepletionCurrencyFork as Currency

projectorCurrencyValue :
  {A : Residence.OrderedBudgetArithmetic} →
  (family : Currency.DepletionCurrencyFamily A) →
  Currency.currencyValue family Currency.spectralProjectorTurnoverCurrency
  ≡ Currency.spectralProjectorTurnover family
projectorCurrencyValue family = refl

record SpectralProjectorResidenceInputs
    (A : Residence.OrderedBudgetArithmetic) : Set₁ where
  field
    currencies : Currency.DepletionCurrencyFamily A
    absorptionMargin : Residence.Scalar A
    dangerCost : Residence.Scalar A
    dangerousResidence : Residence.Scalar A
    budgetUpper : Residence.Scalar A

    absorptionMarginNonnegative :
      Residence._≤_ A (Residence.zero A) absorptionMargin

    dangerousTransferConsumesProjectorTurnover :
      Residence._≤_ A
        (Residence._*_ A dangerCost dangerousResidence)
        (Currency.spectralProjectorTurnover currencies)

    projectorTurnoverRemainderAbsorbed :
      Residence._≤_ A
        (Residence._*_ A absorptionMargin
          (Currency.spectralProjectorTurnover currencies))
        budgetUpper

open SpectralProjectorResidenceInputs public

toSelectedCurrencyResidenceInputs :
  (A : Residence.OrderedBudgetArithmetic) →
  SpectralProjectorResidenceInputs A →
  Currency.SelectedCurrencyResidenceInputs A
toSelectedCurrencyResidenceInputs A I = record
  { currencies = currencies I
  ; selectedCurrency = Currency.spectralProjectorTurnoverCurrency
  ; absorptionMargin = absorptionMargin I
  ; dangerCost = dangerCost I
  ; dangerousResidence = dangerousResidence I
  ; budgetUpper = budgetUpper I
  ; absorptionMarginNonnegative = absorptionMarginNonnegative I
  ; dangerousTransferConsumesSelectedCurrency =
      dangerousTransferConsumesProjectorTurnover I
  ; selectedCurrencyRemainderAbsorbed =
      projectorTurnoverRemainderAbsorbed I
  }

spectralProjectorTurnoverForcesResidenceBound :
  (A : Residence.OrderedBudgetArithmetic) →
  (I : SpectralProjectorResidenceInputs A) →
  Residence._≤_ A
    (Residence._*_ A
      (Residence._*_ A (absorptionMargin I) (dangerCost I))
      (dangerousResidence I))
    (budgetUpper I)
spectralProjectorTurnoverForcesResidenceBound A I =
  Currency.selectedDepletionCurrencyForcesResidenceBound A
    (toSelectedCurrencyResidenceInputs A I)

round80SpectralProjectorTurnoverCurrencyAlreadyPresent : Bool
round80SpectralProjectorTurnoverCurrencyAlreadyPresent = true

round80ProjectorTurnoverFeedsExistingResidenceTheorem : Bool
round80ProjectorTurnoverFeedsExistingResidenceTheorem = true

round80FoiasStatisticalSojournNeededForDeterministicResidenceAlgebra : Bool
round80FoiasStatisticalSojournNeededForDeterministicResidenceAlgebra = false

round80ProjectorTurnoverFeedsExistingResidenceTheoremIsTrue :
  round80ProjectorTurnoverFeedsExistingResidenceTheorem ≡ true
round80ProjectorTurnoverFeedsExistingResidenceTheoremIsTrue = refl
