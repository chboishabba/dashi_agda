{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR136TraceAnomalyOrderDominanceToExpansionTest where

import DASHI.Physics.Foundations.CMP119CosmologyR136TraceAnomalyOrderDominanceToExpansionExact as Subject

open import Agda.Builtin.Bool using (Bool; true)

orderDominanceCompilesToExpansion : Bool
orderDominanceCompilesToExpansion = Subject.anomalyOrderDominanceNowCompilesToMatterAcceleration
