module DASHI.Physics.Closure.NSTriadKNCriticalSlotTrajectoryTelescopeRound155Exact where

------------------------------------------------------------------------
-- ROUND155 / EXACT TRAJECTORY TELESCOPE FOR THE CRITICAL SLOT COMMUTATOR
--
-- Cross-pollination:
--   * Yang--Mills PR #522: exact multiscale covariance telescoping before
--     majorisation.
--   * Yang--Mills PR #507: fine = coarse + conditional residual, with the
--     residual kept as a proof-bearing reopening coordinate.
--   * RH PR #622: work after quotienting the nuisance direction.
--
-- Round154 proves that a common slot component is invisible.  This file adds
-- the dynamic counterpart.  An additive trajectory is a finite sequence of
-- exact reopening steps y = x + delta.
--
-- The endpoint is exactly start + sum(delta), and because the Round138 slot
-- production is linear in each of the three slot amplitudes (with fixed radial
-- coefficients), the COMPLETE endpoint production is
--
--   P(end) = P(start) + P(total residual K,
--                             total residual P,
--                             total residual Q).
--
-- No absolute value is taken stepwise.  This is the finite algebra needed to
-- make the remaining A theorem a trajectory/quadratic-variation estimate
-- rather than another instantaneous cubic majorant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNCriticalHelicitySlotCommutatorRound138Exact as R138

------------------------------------------------------------------------
-- Proof-bearing finite additive trajectory.
------------------------------------------------------------------------

data AdditiveTrajectory {r} (F : C3.RealField r) :
    C3.Carrier F → C3.Carrier F → Set r where
  stop : (x : C3.Carrier F) → AdditiveTrajectory F x x
  step : ∀ {x y z} →
    (delta : C3.Carrier F) →
    y ≡ C3.add F x delta →
    AdditiveTrajectory F y z →
    AdditiveTrajectory F x z

residualTotal :
  ∀ {r} {F : C3.RealField r} {x z} →
  AdditiveTrajectory F x z → C3.Carrier F
residualTotal {F = F} (stop x) = C3.zero F
residualTotal {F = F} (step delta equality rest) =
  C3.add F delta (residualTotal rest)

trajectoryTelescopes :
  ∀ {r} {F : C3.RealField r} {x z}
    (T : AdditiveTrajectory F x z) →
  z ≡ C3.add F x (residualTotal T)
trajectoryTelescopes {F = F} (stop x) =
  sym (Field.realAddZeroRight F x)
trajectoryTelescopes {F = F} (step {x = x} delta equality rest) =
  trans
    (trajectoryTelescopes rest)
    (trans
      (cong (λ value → C3.add F value (residualTotal rest)) equality)
      (C3.addAssociative F x delta (residualTotal rest)))

------------------------------------------------------------------------
-- Three slot trajectories and exact production transport.
------------------------------------------------------------------------

record CriticalSlotTrajectory
    {r} (F : C3.RealField r) : Set r where
  constructor critical-slot-trajectory
  field
    startK startP startQ : C3.Carrier F
    endK endP endQ : C3.Carrier F
    pathK : AdditiveTrajectory F startK endK
    pathP : AdditiveTrajectory F startP endP
    pathQ : AdditiveTrajectory F startQ endQ

open CriticalSlotTrajectory public

residualK residualP residualQ :
  ∀ {r} {F : C3.RealField r} → CriticalSlotTrajectory F → C3.Carrier F
residualK T = residualTotal (pathK T)
residualP T = residualTotal (pathP T)
residualQ T = residualTotal (pathQ T)

slotProductionTrajectoryTelescope :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq : C3.Carrier F)
    (T : CriticalSlotTrajectory F) →
  R138.helicitySlotProduction rk rp rq
    (endK T) (endP T) (endQ T)
  ≡
  C3.add F
    (R138.helicitySlotProduction rk rp rq
      (startK T) (startP T) (startQ T))
    (R138.helicitySlotProduction rk rp rq
      (residualK T) (residualP T) (residualQ T))
slotProductionTrajectoryTelescope {F = F} rk rp rq T
  rewrite trajectoryTelescopes (pathK T)
        | trajectoryTelescopes (pathP T)
        | trajectoryTelescopes (pathQ T) =
  R.solve 9
    (λ rk rp rq sk sp sq dk dp dq →
      ((((rk R.⊗ (rp R.⊕ (R.⊝ rq))) R.⊗ (sk R.⊕ dk))
        R.⊕ (((rp R.⊗ (rq R.⊕ (R.⊝ rk))) R.⊗ (sp R.⊕ dp))
          R.⊕ ((rq R.⊗ (rk R.⊕ (R.⊝ rp))) R.⊗ (sq R.⊕ dq))))
      R.⊜
      (((((rk R.⊗ (rp R.⊕ (R.⊝ rq))) R.⊗ sk)
        R.⊕ (((rp R.⊗ (rq R.⊕ (R.⊝ rk))) R.⊗ sp)
          R.⊕ ((rq R.⊗ (rk R.⊕ (R.⊝ rp))) R.⊗ sq)))
        R.⊕
       ((((rk R.⊗ (rp R.⊕ (R.⊝ rq))) R.⊗ dk)
        R.⊕ (((rp R.⊗ (rq R.⊕ (R.⊝ rk))) R.⊗ dp)
          R.⊕ ((rq R.⊗ (rk R.⊕ (R.⊝ rp))) R.⊗ dq)))))
    refl rk rp rq
      (startK T) (startP T) (startQ T)
      (residualK T) (residualP T) (residualQ T)
  where module R = Field.Solver F

-- If the initial coarse state is common across slots, Round138 kills it and
-- the complete endpoint production is exactly residual production.
commonStartTrajectoryLeavesOnlyResidual :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq common : C3.Carrier F)
    (T : CriticalSlotTrajectory F) →
  startK T ≡ common →
  startP T ≡ common →
  startQ T ≡ common →
  R138.helicitySlotProduction rk rp rq
    (endK T) (endP T) (endQ T)
  ≡ R138.helicitySlotProduction rk rp rq
      (residualK T) (residualP T) (residualQ T)
commonStartTrajectoryLeavesOnlyResidual {F = F}
    rk rp rq common T refl refl refl =
  trans
    (slotProductionTrajectoryTelescope rk rp rq T)
    (trans
      (cong
        (λ base → C3.add F base
          (R138.helicitySlotProduction rk rp rq
            (residualK T) (residualP T) (residualQ T)))
        (R138.commonHelicitySlotAmplitudeCancels rk rp rq common))
      (C3.addZeroLeft F
        (R138.helicitySlotProduction rk rp rq
          (residualK T) (residualP T) (residualQ T))))

round155FiniteSlotTrajectoryTelescopeClosed : Bool
round155FiniteSlotTrajectoryTelescopeClosed = true

round155CommonCoarseTrajectoryCancelsExactly : Bool
round155CommonCoarseTrajectoryCancelsExactly = true

round155StepwiseAbsoluteValuesRequired : Bool
round155StepwiseAbsoluteValuesRequired = false

round155PhysicalResidualQuadraticVariationBudgetClosed : Bool
round155PhysicalResidualQuadraticVariationBudgetClosed = false

round155PackageAClosed : Bool
round155PackageAClosed = false

round155FiniteSlotTrajectoryTelescopeClosedIsTrue :
  round155FiniteSlotTrajectoryTelescopeClosed ≡ true
round155FiniteSlotTrajectoryTelescopeClosedIsTrue = refl

round155PackageAClosedIsFalse : round155PackageAClosed ≡ false
round155PackageAClosedIsFalse = refl
