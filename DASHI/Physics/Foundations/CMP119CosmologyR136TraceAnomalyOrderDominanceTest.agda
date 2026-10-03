{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR136TraceAnomalyOrderDominanceTest where

import DASHI.Physics.Foundations.CMP119CosmologyR136TraceAnomalyOrderDominanceExact as Subject

open import Agda.Builtin.Bool using (Bool; true)

exactEqualityIsNotRequired : Bool
exactEqualityIsNotRequired = Subject.anomalyFallbackExactEqualityIsParetoOverstrong
