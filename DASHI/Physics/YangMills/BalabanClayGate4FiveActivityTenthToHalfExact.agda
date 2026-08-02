module DASHI.Physics.YangMills.BalabanClayGate4FiveActivityTenthToHalfExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact five-channel allocation into Delta/2.
--
-- The determinant, interaction, chart, gauge and localization activities each
-- receive Delta/10.  Their total is therefore exactly Delta/2.  This removes a
-- free final allocation premise from the H-R_beta adapter; only the five local
-- channel estimates remain analytic inputs.
------------------------------------------------------------------------

oneTenthℚ halfℚ : ℚ
oneTenthℚ = + 1 / 10
halfℚ = + 1 / 2

fiveTenthsEqualsHalf : ∀ delta →
  delta * oneTenthℚ
  + (delta * oneTenthℚ
  + (delta * oneTenthℚ
  + (delta * oneTenthℚ
  + delta * oneTenthℚ)))
  ≡ delta * halfℚ
fiveTenthsEqualsHalf = ℚRing.solve-∀

record RationalAdditiveOrder : Set₁ where
  field
    LessEqual : ℚ → ℚ → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (left + right) (leftUpper + rightUpper)

open RationalAdditiveOrder public

record FiveActivityTenthAllocation
    (order : RationalAdditiveOrder) : Set₁ where
  field
    delta determinant interaction chart gauge localization total : ℚ

    totalMeaning :
      total
      ≡ determinant
        + (interaction + (chart + (gauge + localization)))

    determinantBelowTenth :
      LessEqual order determinant (delta * oneTenthℚ)
    interactionBelowTenth :
      LessEqual order interaction (delta * oneTenthℚ)
    chartBelowTenth :
      LessEqual order chart (delta * oneTenthℚ)
    gaugeBelowTenth :
      LessEqual order gauge (delta * oneTenthℚ)
    localizationBelowTenth :
      LessEqual order localization (delta * oneTenthℚ)

open FiveActivityTenthAllocation public

fiveActivityTotalBelowHalf :
  ∀ {order : RationalAdditiveOrder} →
  (allocation : FiveActivityTenthAllocation order) →
  LessEqual order
    (total allocation)
    (delta allocation * halfℚ)
fiveActivityTotalBelowHalf {order = order} allocation =
  subst
    (λ selected → LessEqual order selected (delta allocation * halfℚ))
    (sym (totalMeaning allocation))
    (subst
      (λ selected →
        LessEqual order
          (determinant allocation
            + (interaction allocation
              + (chart allocation
                + (gauge allocation + localization allocation))))
          selected)
      (fiveTenthsEqualsHalf (delta allocation))
      (addMonotone order
        (determinantBelowTenth allocation)
        (addMonotone order
          (interactionBelowTenth allocation)
          (addMonotone order
            (chartBelowTenth allocation)
            (addMonotone order
              (gaugeBelowTenth allocation)
              (localizationBelowTenth allocation))))))

fiveActivityTenthArithmeticLevel : ProofLevel
fiveActivityTenthArithmeticLevel = machineChecked

fiveActivityHalfAllocationLevel : ProofLevel
fiveActivityHalfAllocationLevel = machineChecked

physicalFiveActivityTenthEstimatesInputsLevel : ProofLevel
physicalFiveActivityTenthEstimatesInputsLevel = conditional
