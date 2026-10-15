{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.FieldGeometryMatterTerminalValidation where

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.Foundations.FieldGeometryMatterTerminalMaxCutExact as Terminal

terminalFrontierExists : Terminal.FieldGeometryMatterTerminalFrontier
terminalFrontierExists = Terminal.currentTerminalFrontier

monolithicRollupIntegrationIsExplicit : Terminal.FrontierStatus
monolithicRollupIntegrationIsExplicit =
  Terminal.monolithicFoundationsEverythingIntegration Terminal.currentTerminalFrontier

moreGenericAbstractionDoesNotClosePhysics : Bool
moreGenericAbstractionDoesNotClosePhysics =
  Terminal.moreGenericAbstractionCountsAsPhysicalClosure Terminal.currentTerminalFrontier
