module DASHI.Physics.ClaySupportingFiniteShellResidueBridge where

open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties
  using ( ≤-refl; ≤-trans; *-mono-≤ )
open import DASHI.Physics.ClaySupportingShellEnergyBudget
  using (sum; sumDomination)
open import DASHI.Physics.ClaySupportingFiniteShellDissipation
  using (FiniteShellStrongBudget)

----------------------------------------------------------------------
-- §1  Pointwise residue-to-shell-norm bound (time-integrated)
--
--   (N * N) * residueInt N ≤ C_res * shellNormInt N
--
-- This is the time-integrated version of the Stage 4A pointwise
-- residue estimate: at every t,
--   N² * Residue_N(t) ≤ C_res * |x_N(t)|_s²,
-- and time-integrating preserves the inequality.
----------------------------------------------------------------------

PointwiseResidueN2Bound :
  (residueInt shellNormInt : Nat → Nat) (N C_res : Nat) → Set
PointwiseResidueN2Bound residueInt shellNormInt N C_res =
  (N * N) * residueInt N ≤ C_res * shellNormInt N

----------------------------------------------------------------------
-- §2  Lemma: individual shell norm is bounded by the sum over N≤R
--
--   shellNormInt N ≤ sum shellNormInt R    (when N ≤ R)
--
-- This is sumDomination from ClaySupportingShellEnergyBudget, re-exported
-- here for convenience.
----------------------------------------------------------------------

shellNormDomination :
  (shellNormInt : Nat → Nat) (R N : Nat) → (N ≤ R) →
  shellNormInt N ≤ sum shellNormInt R
shellNormDomination = sumDomination

----------------------------------------------------------------------
-- §3  Main composition theorem
--
--   PointwiseResidueN2Bound  +  FiniteShellStrongBudget  +  N ≤ R
--     ⇒  (N*N) * residueInt N ≤ C_res * ((C_shell * C_LP) * dissipationBudget)
--
-- Mathematical chain:
--   (N*N) * residueInt N  ≤  C_res * shellNormInt N          (pointwise bound)
--                         ≤  C_res * sum shellNormInt R      (sum domination)
--                         ≤  C_res * ((C_shell * C_LP) * dissipationBudget)
--                                                          (finite shell budget)
----------------------------------------------------------------------

integratedResidueN2BoundFromShellBudget :
  (residueInt shellNormInt : Nat → Nat) →
  (R N C_res C_shell C_LP dissipationBudget : Nat) →
  (N ≤ R) →
  PointwiseResidueN2Bound residueInt shellNormInt N C_res →
  FiniteShellStrongBudget shellNormInt R C_shell C_LP dissipationBudget →
  (N * N) * residueInt N ≤ C_res * ((C_shell * C_LP) * dissipationBudget)
integratedResidueN2BoundFromShellBudget
  residueInt shellNormInt R N C_res C_shell C_LP dissipationBudget
  N≤R residueBound shellBudget =
  let
    -- Step 1: (N*N) * residueInt N ≤ C_res * shellNormInt N (given)
    step1 : (N * N) * residueInt N ≤ C_res * shellNormInt N
    step1 = residueBound

    -- Step 2: C_res * shellNormInt N ≤ C_res * sum shellNormInt R
    step2 : C_res * shellNormInt N ≤ C_res * sum shellNormInt R
    step2 = *-mono-≤ (≤-refl {C_res})
                     (shellNormDomination shellNormInt R N N≤R)

    -- Step 3: C_res * sum shellNormInt R ≤ C_res * ((C_shell * C_LP) * dissipationBudget)
    step3 : C_res * sum shellNormInt R
            ≤ C_res * ((C_shell * C_LP) * dissipationBudget)
    step3 = *-mono-≤ (≤-refl {C_res}) shellBudget

  in ≤-trans step1 (≤-trans step2 step3)

----------------------------------------------------------------------
-- §4  Convenience lemma: extract the energy-budget inequality needed
--     by IntegratedResidueN2BoundTarget.energyBudgetBound
--
--   FiniteShellStrongBudget  ⇒  sum shellNormInt R ≤ energyBudgetConstant
--
-- where energyBudgetConstant = (C_shell * C_LP) * dissipationBudget.
----------------------------------------------------------------------

energyBudgetBoundFromShellBudget :
  (shellNormInt : Nat → Nat) (R C_shell C_LP dissipationBudget : Nat) →
  FiniteShellStrongBudget shellNormInt R C_shell C_LP dissipationBudget →
  sum shellNormInt R ≤ (C_shell * C_LP) * dissipationBudget
energyBudgetBoundFromShellBudget shellNormInt R C_shell C_LP dissipationBudget
  shellBudget = shellBudget
