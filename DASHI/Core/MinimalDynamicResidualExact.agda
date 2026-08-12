module DASHI.Core.MinimalDynamicResidualExact where

------------------------------------------------------------------------
-- MINIMAL RESIDUAL FOR THE HIDDEN-PHASE COUNTEREXAMPLE
--
-- The existing HiddenPhaseDynamicInsufficiencyExact proves that the visible
-- Bool alone is not dynamically sufficient.  Here we show that retaining only
-- the C3 phase is already enough to reopen the complete finite state exactly.
--
-- Hence, in the explicit two-tier family {no residual, phase residual}, the
-- one-cell phase receipt is the minimal sufficient/reopenable choice.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

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

data ResidualTier : Set where
  noResidual : ResidualTier
  phaseResidual : ResidualTier

tierCost : ResidualTier → Nat
tierCost noResidual = zero
tierCost phaseResidual = suc zero

data FutureSufficientTier : ResidualTier → Set where
  phaseResidualIsSufficient : FutureSufficientTier phaseResidual

noResidualCannotBeCertifiedSufficient :
  FutureSufficientTier noResidual → ⊥
noResidualCannotBeCertifiedSufficient ()

phaseResidualCostIsOne : tierCost phaseResidual ≡ 1
phaseResidualCostIsOne = refl

visibleOnlyHasDynamicDefect :
  GP.DynamicInsufficiencyWitness Hidden.hiddenPhaseSystem
visibleOnlyHasDynamicDefect = Hidden.hiddenPhaseIsDynamicallyRelevant

record MinimalResidualCertificate : Set where
  constructor minimalResidualCertificate
  field
    selected : ResidualTier
    selectedIsSufficient : FutureSufficientTier selected
    selectedCost : Nat
    selectedCostExact : selectedCost ≡ tierCost selected
    zeroTierImpossible : FutureSufficientTier noResidual → ⊥

open MinimalResidualCertificate public

hiddenPhaseMinimalResidual : MinimalResidualCertificate
hiddenPhaseMinimalResidual =
  minimalResidualCertificate
    phaseResidual
    phaseResidualIsSufficient
    1
    refl
    noResidualCannotBeCertifiedSufficient
