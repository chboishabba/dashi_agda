module DASHI.Physics.YangMills.BalabanClayGate4FederbushAsymmetricQuarterBudgetExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Asymmetric four-channel Federbush budget.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- J. M. Holtzman,
-- "Explicit epsilon and delta for the Implicit Function Theorem",
-- SIAM Review 12 (1970), 284--286. DOI: 10.1137/1012051.
--
-- Equal 1/16 allocations are convenient but analytically unnatural.  The
-- curvature/geometry channel is expected to dominate, while the exact inverse
-- seed may have much smaller defect.  This module allows arbitrary named
-- allocations whose sum is the selected quarter target.
------------------------------------------------------------------------

record AsymmetricFourChannelAlgebra (Bound : Set) : Set₁ where
  field
    add : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    geometryAllowance contourAllowance chartAllowance inverseAllowance : Bound
    quarter : Bound

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

    allocationMeaning :
      add geometryAllowance
        (add contourAllowance
          (add chartAllowance inverseAllowance))
      ≡ quarter

open AsymmetricFourChannelAlgebra public

record FederbushAsymmetricBudget
    {Bound : Set} (algebra : AsymmetricFourChannelAlgebra Bound) : Set₁ where
  field
    geometry contourTransport chart inverseSeed total : Bound

    totalMeaning :
      total
      ≡ add algebra geometry
          (add algebra contourTransport
            (add algebra chart inverseSeed))

    geometryWithinAllowance :
      LessEqual algebra geometry (geometryAllowance algebra)
    contourWithinAllowance :
      LessEqual algebra contourTransport (contourAllowance algebra)
    chartWithinAllowance :
      LessEqual algebra chart (chartAllowance algebra)
    inverseWithinAllowance :
      LessEqual algebra inverseSeed (inverseAllowance algebra)

open FederbushAsymmetricBudget public

federbushAsymmetricTotalBelowQuarter :
  ∀ {Bound}
    {algebra : AsymmetricFourChannelAlgebra Bound} →
  (budget : FederbushAsymmetricBudget algebra) →
  LessEqual algebra (total budget) (quarter algebra)
federbushAsymmetricTotalBelowQuarter {algebra = algebra} budget =
  subst
    (λ selected → LessEqual algebra selected (quarter algebra))
    (sym (totalMeaning budget))
    (subst
      (λ selected →
        LessEqual algebra
          (add algebra (geometry budget)
            (add algebra (contourTransport budget)
              (add algebra (chart budget) (inverseSeed budget))))
          selected)
      (allocationMeaning algebra)
      (addMonotone algebra
        (geometryWithinAllowance budget)
        (addMonotone algebra
          (contourWithinAllowance budget)
          (addMonotone algebra
            (chartWithinAllowance budget)
            (inverseWithinAllowance budget)))))

record FederbushContractionAndForcing
    {Bound : Set} (algebra : AsymmetricFourChannelAlgebra Bound) : Set₁ where
  field
    contraction forcing : FederbushAsymmetricBudget algebra

open FederbushContractionAndForcing public

federbushAsymmetricContractionBelowQuarter :
  ∀ {Bound} {algebra : AsymmetricFourChannelAlgebra Bound} →
  (dataSet : FederbushContractionAndForcing algebra) →
  LessEqual algebra
    (total (contraction dataSet))
    (quarter algebra)
federbushAsymmetricContractionBelowQuarter dataSet =
  federbushAsymmetricTotalBelowQuarter (contraction dataSet)

federbushAsymmetricForcingBelowQuarter :
  ∀ {Bound} {algebra : AsymmetricFourChannelAlgebra Bound} →
  (dataSet : FederbushContractionAndForcing algebra) →
  LessEqual algebra
    (total (forcing dataSet))
    (quarter algebra)
federbushAsymmetricForcingBelowQuarter dataSet =
  federbushAsymmetricTotalBelowQuarter (forcing dataSet)

federbushAsymmetricBudgetArithmeticLevel : ProofLevel
federbushAsymmetricBudgetArithmeticLevel = machineChecked

physicalFederbushAsymmetricChannelInputsLevel : ProofLevel
physicalFederbushAsymmetricChannelInputsLevel = conditional
