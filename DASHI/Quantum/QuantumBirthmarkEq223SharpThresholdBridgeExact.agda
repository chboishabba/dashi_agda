{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkEq223SharpThresholdBridgeExact where

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Foundations.CMP119CosmologyMathematicalMaxCut20261003Exact as Sharp
import DASHI.Physics.Foundations.CMP119CosmologyBalabanVacuumDominatedR136Exact as Preferred

------------------------------------------------------------------------
-- TWO SOURCE-FACING SIGN CUTS ALREADY IN THE REPO
--
-- Preferred current compiler:
--   literal vacuum coefficient > 0
--   literal E/R/B numerator >= 0
--      -> positive Eq.(2.23) balance -> negative R136 -> acceleration.
--
-- Older mathematical max-cut:
--   c_V < -(M_ERB + Tail_R109(k))
--      -> negative R136 -> acceleration.
--
-- The second is a sharp dominance threshold after envelope/tail reduction.
-- There is no theorem in the current repo identifying its c_V/M_ERB/Tail_R109
-- quantities with the newer literal derivative/numerator pair in a way that
-- proves logical implication either direction.  Keep both routes distinct.
------------------------------------------------------------------------

sharpVacuumThresholdReused : Bool
sharpVacuumThresholdReused = Sharp.eq223SharpVacuumThresholdIsTerminal

sharpThresholdCompilesToExpansion : Bool
sharpThresholdCompilesToExpansion = Sharp.eq223VacuumThresholdCompilesToExpansion

preferredTwoLeafSignRouteCompilesToR136 : Bool
preferredTwoLeafSignRouteCompilesToR136 =
  Preferred.preferredVacuumDominanceLeavesAreTwoLiteralSectorSigns

preferredTwoLeafSignIsWeakerThanSharpThreshold : Bool
preferredTwoLeafSignIsWeakerThanSharpThreshold = false

twoSignCutsProvedEquivalent : Bool
twoSignCutsProvedEquivalent = false

crossIdentificationOfSharpAndLiteralSignQuantitiesStillRequired : Bool
crossIdentificationOfSharpAndLiteralSignQuantitiesStillRequired = true

noSignConventionCollapse : Bool
noSignConventionCollapse = true
