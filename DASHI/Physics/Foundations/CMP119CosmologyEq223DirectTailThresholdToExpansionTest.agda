{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223DirectTailThresholdToExpansionTest where

import DASHI.Physics.Foundations.CMP119CosmologyEq223DirectTailThresholdToExpansionExact as Subject

open import Agda.Builtin.Bool using (Bool; true)

directTailThresholdCompilesToExpansion : Bool
directTailThresholdCompilesToExpansion =
  Subject.directPreferredConsumerCompilesToMatterAcceleration
