{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223VacuumTailThresholdTest where

import DASHI.Physics.Foundations.CMP119CosmologyEq223VacuumTailThresholdExact as New

vacuumThresholdForcesMarginRegression =
  New.vacuumBelowNegativeERBPlusTailForcesStrictMargin

strictMarginRecutRegression =
  New.preferredStrictMarginReducesToOneVacuumThresholdGivenEnvelope
