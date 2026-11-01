module DASHI.Core.MinimalDynamicResidualExact where

------------------------------------------------------------------------
-- MINIMAL RESIDUAL FOR THE HIDDEN-PHASE COUNTEREXAMPLE
--
-- The existing HiddenPhaseDynamicInsufficiencyExact proves that the visible
-- Bool alone is not dynamically sufficient.  Here we prove a stronger static
-- no-go as well: no reopening function of the visible Bool alone can exactly
-- reconstruct every fine hidden-phase state.  Retaining only the C3 phase is
-- sufficient to reopen every state exactly.
--
-- Thus zero residual is impossible for exact reopening in this finite model,
-- while one three-valued phase coordinate suffices.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.GradedProvenanceDynamicalSystemExact as GP
import DASHI.Core.HiddenPhaseDynamicInsufficiencyExact as Hidden
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

reopenFromVisibleAndPhase :
  Bool →
  Wheel.DepthWheelPhase →
  GP.PackedState Hidden.hiddenPhaseWheel
reopenFromVisibleAndPhase visible Wheel.phase-0 = GP.at0 visible
reopenFromVisibleAndPhase visible Wheel.phase-1 = GP.at1 visible
reopenFromVisibleAndPhase visible Wheel.phase-2 = GP.at2 visible

phaseReceiptReopensExactly :
  (x : GP.PackedState Hidden.hiddenPhaseWheel) →
  reopenFromVisibleAndPhase
    (GP.observe Hidden.hiddenPhaseSystem x)
    (GP.grade x)
  ≡ x
phaseReceiptReopensExactly (GP.at0 x) = refl
phaseReceiptReopensExactly (GP.at1 x) = refl
phaseReceiptReopensExactly (GP.at2 x) = refl

phaseResidualSystem : GP.GradedProvenanceSystem
phaseResidualSystem =
  GP.gradedProvenanceSystem
    Hidden.hiddenPhaseWheel
    Bool
    Wheel.DepthWheelPhase
    Wheel.DepthWheelPhase
    (GP.observe Hidden.hiddenPhaseSystem)
    GP.grade
    GP.grade
    reopenFromVisibleAndPhase
    phaseReceiptReopensExactly

------------------------------------------------------------------------
-- Zero-residual no-go: one visible Bool cannot exactly reopen both states
-- that expose false while occupying distinct phases.
------------------------------------------------------------------------

record VisibleOnlyExactReopening : Set₁ where
  constructor visibleOnlyExactReopening
  field
    reopenVisibleOnly :
      Bool → GP.PackedState Hidden.hiddenPhaseWheel
    reopenVisibleOnlyExact :
      (x : GP.PackedState Hidden.hiddenPhaseWheel) →
      reopenVisibleOnly (GP.observe Hidden.hiddenPhaseSystem x) ≡ x

open VisibleOnlyExactReopening public

phaseZeroNotPhaseOne : Wheel.phase-0 ≡ Wheel.phase-1 → ⊥
phaseZeroNotPhaseOne ()

noVisibleOnlyExactReopening : VisibleOnlyExactReopening → ⊥
noVisibleOnlyExactReopening reopening =
  phaseZeroNotPhaseOne
    (cong GP.grade sameFineState)
  where
    sameFineState : Hidden.leftState ≡ Hidden.rightState
    sameFineState =
      trans
        (sym (reopenVisibleOnlyExact reopening Hidden.leftState))
        (reopenVisibleOnlyExact reopening Hidden.rightState)

------------------------------------------------------------------------
-- Explicit residual-cost tiering.
------------------------------------------------------------------------

data ResidualTier : Set where
  noResidual : ResidualTier
  phaseResidual : ResidualTier

tierCost : ResidualTier → Nat
tierCost noResidual = zero
tierCost phaseResidual = suc zero

phaseResidualCostIsOne : tierCost phaseResidual ≡ 1
phaseResidualCostIsOne = refl

visibleOnlyHasDynamicDefect :
  GP.DynamicInsufficiencyWitness Hidden.hiddenPhaseSystem
visibleOnlyHasDynamicDefect = Hidden.hiddenPhaseIsDynamicallyRelevant

record MinimalResidualCertificate : Set₁ where
  constructor minimalResidualCertificate
  field
    selected : ResidualTier
    selectedCost : Nat
    selectedCostExact : selectedCost ≡ tierCost selected
    exactReopeningWithSelectedResidual :
      (x : GP.PackedState Hidden.hiddenPhaseWheel) →
      reopenFromVisibleAndPhase
        (GP.observe Hidden.hiddenPhaseSystem x)
        (GP.grade x)
      ≡ x
    zeroResidualExactReopeningImpossible :
      VisibleOnlyExactReopening → ⊥

open MinimalResidualCertificate public

hiddenPhaseMinimalResidual : MinimalResidualCertificate
hiddenPhaseMinimalResidual =
  minimalResidualCertificate
    phaseResidual
    1
    refl
    phaseReceiptReopensExactly
    noVisibleOnlyExactReopening
