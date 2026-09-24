{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119MicrocausalChargeExact where

------------------------------------------------------------------------
-- C / LOCAL STRESS CURRENT -> ROUND85 STABILIZED LOCAL-CORE CHARGE
--
-- Compose Round86's two existing compilers:
--
--   local current + shell geometry + microcausality
--      -> cutoff commutator shell
--   + vacuum-neutral Ward decomposition on A Omega
--      -> eventually stable local-core cutoff charge.
--
-- Therefore eventual stabilization is not an additional physical premise.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (_≤_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsLocalCurrentMicrocausalShellExact as Micro
import DASHI.Physics.YangMills.YangMillsLocalChargeCommutatorToCoreStabilizationExact as Charge
import DASHI.Physics.YangMills.YangMillsStressChargeLocalCoreCutoffStabilizationExact as Core

microcausalCurrentBuildsLocalCoreCutoffCharge :
  ∀ {Observable Current Target LocalVector}
    (current :
      Micro.MicrocausalLocalCurrentShell Observable Current Target)
    (ward :
      Charge.VacuumNeutralLocalChargeCore
        (Micro.microcausalShellToCutoffCommutatorShell current)
        LocalVector) →
  Core.LocalCoreCutoffCharge Observable Target
microcausalCurrentBuildsLocalCoreCutoffCharge current ward =
  Charge.observableLabelledLocalCoreCutoffCharge
    (Micro.microcausalShellToCutoffCommutatorShell current)
    ward

microcausalCurrentCutoffChargeActionStable :
  ∀ {Observable Current Target LocalVector}
    (current :
      Micro.MicrocausalLocalCurrentShell Observable Current Target)
    (ward :
      Charge.VacuumNeutralLocalChargeCore
        (Micro.microcausalShellToCutoffCommutatorShell current)
        LocalVector) →
  ∀ observable leftCutoff rightCutoff →
  Core.supportRadius
    (microcausalCurrentBuildsLocalCoreCutoffCharge current ward)
    observable
  ≤ leftCutoff →
  Core.supportRadius
    (microcausalCurrentBuildsLocalCoreCutoffCharge current ward)
    observable
  ≤ rightCutoff →
  Core.cutoffChargeAction
    (microcausalCurrentBuildsLocalCoreCutoffCharge current ward)
    leftCutoff observable
  ≡
  Core.cutoffChargeAction
    (microcausalCurrentBuildsLocalCoreCutoffCharge current ward)
    rightCutoff observable
microcausalCurrentCutoffChargeActionStable current ward =
  Core.actionStableBeyondSupport
    (microcausalCurrentBuildsLocalCoreCutoffCharge current ward)

microcausalToLocalCoreChargeCompilerLevel : ProofLevel
microcausalToLocalCoreChargeCompilerLevel = machineChecked

-- Remaining local-current physics:
-- * same-family renormalized T_0nu locality/microcausality;
-- * nested charge-shell decomposition/support geometry;
-- * Q_R(A Omega) = [Q_R,A] Omega after the vacuum term is removed.
literalStressCurrentMicrocausalWardLevel : ProofLevel
literalStressCurrentMicrocausalWardLevel = conditional
