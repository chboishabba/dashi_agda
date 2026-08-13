module DASHI.Physics.YangMills.BalabanSelectedCorrelatedPairBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- G2's singleton allowance is tiny.  Bounding the four surviving correlated
-- owners separately can destroy cancellation that is still present in the two
-- physically meaningful groups
--
--   raw localization  = localization + transport,
--   multiplier defect = near Green + far Green.
--
-- This module delays majorisation one step further.  It proves that rigorous
-- bounds on those TWO signed grouped quantities suffice to close the exact
-- correlated residual against the same 55/18874368 singleton allowance.
-- No absolute value is inserted between the two members of either pair.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualBoundsExact as Bounds

record CorrelatedPairBudgets
    (family : Ownership.CorrelatedResidualFamily)
    (charge : ℚ) : Set where
  field
    localizationPairCoefficient : ℚ
    multiplierPairCoefficient : ℚ

    localizationPairUpper :
      Bounds.rawLocalizationSpillover family
      ≤ localizationPairCoefficient * charge

    multiplierPairUpper :
      Bounds.selectedMultiplierDefectContribution family
      ≤ multiplierPairCoefficient * charge

    pairCoefficientTotalFits :
      localizationPairCoefficient + multiplierPairCoefficient
      ≤ Selector.remainingSingletonCoefficient

    chargeNonnegative : 0ℚ ≤ charge

open CorrelatedPairBudgets public

pairCoefficientsTimesChargeFit :
  ∀ {family charge}
    (budgets : CorrelatedPairBudgets family charge) →
  (localizationPairCoefficient budgets
    + multiplierPairCoefficient budgets) * charge
  ≤ Selector.remainingSingletonCoefficient * charge
pairCoefficientsTimesChargeFit {charge = charge} budgets =
  let
    instance
      chargeNN = ℚ.nonNegative (chargeNonnegative budgets)
  in
  ℚP.*-monoʳ-≤-nonNeg charge (pairCoefficientTotalFits budgets)

correlatedPairBudgetsCloseResidual :
  ∀ {family charge} →
  Ownership.ExactCorrelatedCancellation family →
  CorrelatedPairBudgets family charge →
  Ownership.correlatedResidualTotal family
  ≤ Selector.remainingSingletonCoefficient * charge
correlatedPairBudgetsCloseResidual {family} {charge} cancellation budgets =
  let
    grouped :
      Ownership.correlatedResidualTotal family
      ≡ Bounds.rawLocalizationSpillover family
        + Bounds.selectedMultiplierDefectContribution family
    grouped = Bounds.selectedCorrelatedResidualAtomCancellationExact cancellation

    pairUpper :
      Bounds.rawLocalizationSpillover family
        + Bounds.selectedMultiplierDefectContribution family
      ≤ (localizationPairCoefficient budgets
          + multiplierPairCoefficient budgets) * charge
    pairUpper =
      subst
        (λ upper →
          Bounds.rawLocalizationSpillover family
            + Bounds.selectedMultiplierDefectContribution family
          ≤ upper)
        (ℚRing.solve-∀
          (localizationPairCoefficient budgets)
          (multiplierPairCoefficient budgets) charge)
        (ℚP.+-mono-≤
          (localizationPairUpper budgets)
          (multiplierPairUpper budgets))
  in
  subst
    (λ lower →
      lower ≤ Selector.remainingSingletonCoefficient * charge)
    grouped
    (ℚP.≤-trans pairUpper (pairCoefficientsTimesChargeFit budgets))

selectedCorrelatedPairDelayedMajorisationLevel : ProofLevel
selectedCorrelatedPairDelayedMajorisationLevel = machineChecked
