module DASHI.Physics.Closure.NSPeriodicDiffuseLowHighSplit where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicDiffuseDissipationCharging as Charge
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Concrete low/high split for diffuse-spectrum BKM control.
--
-- The vorticity envelope on a diffuse interval is divided at a selected shell J:
--
--   Vdiff = Vlow(J) + Vhigh(J).
--
-- Diffuseness must bound the finite low-shell part by an integrable remainder;
-- viscous regularity must charge the high-shell tail to an absorbable fraction of
-- dissipation.  This module combines those two genuinely analytic estimates and
-- constructs the common dissipation-charge endpoint.
------------------------------------------------------------------------

record PeriodicDiffuseLowHighInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    orderReflexive : ∀ value → _≤_ A value value

    diffuseVorticity lowShellVorticity highShellVorticity : Scalar A
    chargedDissipation absorbedDissipation : Scalar A
    lowShellRemainder totalDiffuseBudget : Scalar A

    exactLowHighSplit :
      diffuseVorticity ≡
      _+_ A lowShellVorticity highShellVorticity

    -- Analytic low-shell use of the diffuse hypothesis.
    diffuseLowShellEstimate :
      _≤_ A lowShellVorticity lowShellRemainder

    -- Analytic high-shell use of viscous dissipation and geometric decay.
    diffuseHighShellEstimate :
      _≤_ A highShellVorticity chargedDissipation

    chargedPartIsAbsorbable :
      _≤_ A chargedDissipation absorbedDissipation

    absorbedDissipationAndRemainderFitBudget :
      _≤_ A
        (_+_ A absorbedDissipation lowShellRemainder)
        totalDiffuseBudget

    VorticityExpenditureFinite : Set

    totalBudgetBoundImpliesFinite :
      _≤_ A diffuseVorticity totalDiffuseBudget →
      VorticityExpenditureFinite

open PeriodicDiffuseLowHighInputs public

lowHighPiecesBelowChargeAndRemainder :
  ∀ {A : AbsorptionArithmetic} →
  (D : PeriodicDiffuseLowHighInputs A) →
  _≤_ A
    (_+_ A (lowShellVorticity D) (highShellVorticity D))
    (_+_ A (chargedDissipation D) (lowShellRemainder D))
lowHighPiecesBelowChargeAndRemainder {A = A} D =
  ≤-trans A
    (additionMonotoneRight A (diffuseLowShellEstimate D))
    (≤-trans A
      (additionMonotoneLeft A (diffuseHighShellEstimate D))
      reordered)
  where
  reordered :
    _≤_ A
      (_+_ A (lowShellRemainder D) (chargedDissipation D))
      (_+_ A (chargedDissipation D) (lowShellRemainder D))
  reordered =
    subst
      (λ rhs →
        _≤_ A
          (_+_ A (lowShellRemainder D) (chargedDissipation D))
          rhs)
      (addCommutative A
        (lowShellRemainder D) (chargedDissipation D))
      (orderReflexive D
        (_+_ A (lowShellRemainder D) (chargedDissipation D)))

diffuseVorticityBelowChargeAndRemainder :
  ∀ {A : AbsorptionArithmetic} →
  (D : PeriodicDiffuseLowHighInputs A) →
  _≤_ A
    (diffuseVorticity D)
    (_+_ A (chargedDissipation D) (lowShellRemainder D))
diffuseVorticityBelowChargeAndRemainder {A = A} D =
  subst
    (λ lhs →
      _≤_ A lhs
        (_+_ A (chargedDissipation D) (lowShellRemainder D)))
    (sym (exactLowHighSplit D))
    (lowHighPiecesBelowChargeAndRemainder D)

lowHighSplitToDissipationCharge :
  ∀ {A : AbsorptionArithmetic} →
  PeriodicDiffuseLowHighInputs A →
  Charge.PeriodicDiffuseDissipationChargeInputs A
lowHighSplitToDissipationCharge D = record
  { vorticityExpenditure = diffuseVorticity D
  ; chargedDissipation = chargedDissipation D
  ; absorbedDissipation = absorbedDissipation D
  ; diffuseRemainder = lowShellRemainder D
  ; totalDiffuseBudget = totalDiffuseBudget D
  ; diffuseVorticityCharge =
      diffuseVorticityBelowChargeAndRemainder D
  ; chargedPartIsAbsorbable = chargedPartIsAbsorbable D
  ; absorbedDissipationAndRemainderFitBudget =
      absorbedDissipationAndRemainderFitBudget D
  ; VorticityExpenditureFinite = VorticityExpenditureFinite D
  ; totalBudgetBoundImpliesFinite = totalBudgetBoundImpliesFinite D
  }

diffuseLowHighSplitGivesFiniteVorticity :
  ∀ {A : AbsorptionArithmetic} →
  (D : PeriodicDiffuseLowHighInputs A) →
  VorticityExpenditureFinite D
diffuseLowHighSplitGivesFiniteVorticity D =
  Charge.diffuseDissipationChargeGivesFiniteVorticity
    (lowHighSplitToDissipationCharge D)

------------------------------------------------------------------------
-- Status: the diffuse route is reduced to two literal analytic estimates at a
-- selected split shell: finite low-shell control from diffuseness and an
-- absorbable high-shell tail from dissipation.  Their ordered assembly is closed.
------------------------------------------------------------------------

diffuseLowHighSplitLevel : ProofLevel
diffuseLowHighSplitLevel = machineChecked
