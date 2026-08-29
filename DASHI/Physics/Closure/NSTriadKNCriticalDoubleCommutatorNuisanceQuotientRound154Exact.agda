module DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorNuisanceQuotientRound154Exact where

------------------------------------------------------------------------
-- ROUND154 / QUOTIENT THE COMMON SLOT MODE BEFORE ESTIMATING
--
-- Cross-pollination:
--   * RH G21 / PR #622: quotient the nuisance span before asking whether the
--     two surviving channels separate the signal.
--   * Yang--Mills Round42 / PR #507: reduce to a quotient/reopening carrier
--     before trying to invert or estimate the redundant raw presentation.
--
-- Round138 proves that the three critical radial coefficients sum to zero.
-- Consequently the complete helicity-slot production is invariant under a
-- COMMON additive shift of all three slot amplitudes.  This is not merely a
-- convenient rewriting: it identifies an exact one-dimensional nuisance
-- direction which the critical production cannot see.
--
-- Round144 already identifies the physical slot amplitudes with normalized-
-- curl insertions.  Therefore any common coarse component may be removed
-- BEFORE absolute values or Cauchy--Schwarz.  Only the residual/reopening
-- coordinates can contribute to the critical production.
--
-- No analytic estimate is asserted.  Package A remains open: the next task is
-- to control the trajectory quadratic variation of these residual slot modes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNCriticalHelicitySlotCommutatorRound138Exact as R138

private
  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

centeredSlotProduction :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F
centeredSlotProduction rk rp rq common bk bp bq =
  R138.helicitySlotProduction rk rp rq
    (sub bk common) (sub bp common) (sub bq common)

slotProductionInvariantUnderCommonShift :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq common bk bp bq : C3.Carrier F) →
  R138.helicitySlotProduction rk rp rq bk bp bq
  ≡ centeredSlotProduction rk rp rq common bk bp bq
slotProductionInvariantUnderCommonShift {F = F}
    rk rp rq common bk bp bq =
  R.solve 7
    (λ rk rp rq common bk bp bq →
      ((((rk R.⊗ (rp R.⊕ (R.⊝ rq))) R.⊗ bk)
        R.⊕ (((rp R.⊗ (rq R.⊕ (R.⊝ rk))) R.⊗ bp)
          R.⊕ ((rq R.⊗ (rk R.⊕ (R.⊝ rp))) R.⊗ bq)))
      R.⊜
      ((((rk R.⊗ (rp R.⊕ (R.⊝ rq))) R.⊗ (bk R.⊕ (R.⊝ common)))
        R.⊕ (((rp R.⊗ (rq R.⊕ (R.⊝ rk))) R.⊗ (bp R.⊕ (R.⊝ common)))
          R.⊕ ((rq R.⊗ (rk R.⊕ (R.⊝ rp))) R.⊗ (bq R.⊕ (R.⊝ common))))))
    refl rk rp rq common bk bp bq
  where module R = Field.Solver F

commonShiftDoesNotChangeCriticalProduction :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq shift bk bp bq : C3.Carrier F) →
  R138.helicitySlotProduction rk rp rq
    (C3.add F bk shift) (C3.add F bp shift) (C3.add F bq shift)
  ≡ R138.helicitySlotProduction rk rp rq bk bp bq
commonShiftDoesNotChangeCriticalProduction {F = F}
    rk rp rq shift bk bp bq =
  R.solve 7
    (λ rk rp rq shift bk bp bq →
      ((((rk R.⊗ (rp R.⊕ (R.⊝ rq))) R.⊗ (bk R.⊕ shift))
        R.⊕ (((rp R.⊗ (rq R.⊕ (R.⊝ rk))) R.⊗ (bp R.⊕ shift))
          R.⊕ ((rq R.⊗ (rk R.⊕ (R.⊝ rp))) R.⊗ (bq R.⊕ shift))))
      R.⊜
      ((((rk R.⊗ (rp R.⊕ (R.⊝ rq))) R.⊗ bk)
        R.⊕ (((rp R.⊗ (rq R.⊕ (R.⊝ rk))) R.⊗ bp)
          R.⊕ ((rq R.⊗ (rk R.⊕ (R.⊝ rp))) R.⊗ bq))))
    refl rk rp rq shift bk bp bq
  where module R = Field.Solver F

record SlotReopening
    {r} (F : C3.RealField r) : Set r where
  constructor slot-reopening
  field
    coarse : C3.Carrier F
    residualK residualP residualQ : C3.Carrier F

open SlotReopening public

reopenedK reopenedP reopenedQ :
  ∀ {r} {F : C3.RealField r} → SlotReopening F → C3.Carrier F
reopenedK {F = F} R = C3.add F (coarse R) (residualK R)
reopenedP {F = F} R = C3.add F (coarse R) (residualP R)
reopenedQ {F = F} R = C3.add F (coarse R) (residualQ R)

reopenedProductionIsResidualProduction :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq : C3.Carrier F)
    (Ropen : SlotReopening F) →
  R138.helicitySlotProduction rk rp rq
    (reopenedK Ropen) (reopenedP Ropen) (reopenedQ Ropen)
  ≡ R138.helicitySlotProduction rk rp rq
      (residualK Ropen) (residualP Ropen) (residualQ Ropen)
reopenedProductionIsResidualProduction {F = F} rk rp rq Ropen =
  commonShiftDoesNotChangeCriticalProduction
    rk rp rq (coarse Ropen)
    (residualK Ropen) (residualP Ropen) (residualQ Ropen)

-- Combining the quotient identity with Round138 gives the already-reduced
-- two-residual form, but now the residual meaning is explicit.
residualProductionIsTwoDifferences :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq : C3.Carrier F)
    (Ropen : SlotReopening F) →
  R138.helicitySlotProduction rk rp rq
      (residualK Ropen) (residualP Ropen) (residualQ Ropen)
  ≡
  C3.add F
    (C3.multiply F
      (R138.criticalRadialCoefficientK rk rp rq)
      (sub (residualK Ropen) (residualQ Ropen)))
    (C3.multiply F
      (R138.criticalRadialCoefficientP rk rp rq)
      (sub (residualP Ropen) (residualQ Ropen)))
residualProductionIsTwoDifferences rk rp rq Ropen =
  R138.helicitySlotCommutatorForm rk rp rq
    (residualK Ropen) (residualP Ropen) (residualQ Ropen)

round154CommonSlotNuisanceQuotientClosed : Bool
round154CommonSlotNuisanceQuotientClosed = true

round154ExactReopeningLeavesOnlyResidualProduction : Bool
round154ExactReopeningLeavesOnlyResidualProduction = true

round154AbsoluteValueBeforeNuisanceQuotientRequired : Bool
round154AbsoluteValueBeforeNuisanceQuotientRequired = false

round154TrajectoryResidualQuadraticVariationPaymentClosed : Bool
round154TrajectoryResidualQuadraticVariationPaymentClosed = false

round154PackageAClosed : Bool
round154PackageAClosed = false

round154CommonSlotNuisanceQuotientClosedIsTrue :
  round154CommonSlotNuisanceQuotientClosed ≡ true
round154CommonSlotNuisanceQuotientClosedIsTrue = refl

round154PackageAClosedIsFalse : round154PackageAClosed ≡ false
round154PackageAClosedIsFalse = refl
