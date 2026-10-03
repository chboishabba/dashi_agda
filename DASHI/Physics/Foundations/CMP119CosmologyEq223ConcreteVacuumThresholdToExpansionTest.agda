{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223ConcreteVacuumThresholdToExpansionTest where

import DASHI.Physics.Foundations.CMP119CosmologyEq223ConcreteVacuumThresholdToExpansionExact as Subject

open import Agda.Builtin.Bool using (Bool; true)

concretePinnedR109VacuumThresholdRouteIsSourceWritten : Bool
concretePinnedR109VacuumThresholdRouteIsSourceWritten =
  Subject.preferredConcreteVacuumThresholdRouteEliminatesArbitraryFiniteSequence
