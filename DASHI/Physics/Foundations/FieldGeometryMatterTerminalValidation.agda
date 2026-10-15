{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.FieldGeometryMatterTerminalValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.FieldGeometryMatterTerminalMaxCutExact as Terminal

terminalFrontierExists : Terminal.FieldGeometryMatterTerminalFrontier
terminalFrontierExists = Terminal.currentTerminalFrontier

monolithicRollupIntegrationIsExplicit : Terminal.FrontierStatus
monolithicRollupIntegrationIsExplicit =
  Terminal.monolithicFoundationsEverythingIntegration Terminal.currentTerminalFrontier

moreGenericAbstractionDoesNotClosePhysics :
  Terminal.moreGenericAbstractionCountsAsPhysicalClosure
    Terminal.currentTerminalFrontier ≡ false
moreGenericAbstractionDoesNotClosePhysics = refl

residualDoesNotBecomeAntigravity :
  Terminal.residualCountsAsAntigravity Terminal.currentTerminalFrontier ≡ false
residualDoesNotBecomeAntigravity = refl

energyConditionViolationDoesNotBecomeWarpCapability :
  Terminal.energyConditionViolationCountsAsWarpCapability
    Terminal.currentTerminalFrontier ≡ false
energyConditionViolationDoesNotBecomeWarpCapability = refl

teleportationDoesNotBecomeFTL :
  Terminal.teleportationCountsAsFTL Terminal.currentTerminalFrontier ≡ false
teleportationDoesNotBecomeFTL = refl
