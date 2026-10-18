{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPartitionDerivativeTailToExpansionTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyPartitionDerivativeTailToExpansionExact as Subject

partitionResponseRouteCompilesToExpansion :
  Subject.partitionDerivativeTailDominanceCompilesToMatterAcceleration ≡ true
partitionResponseRouteCompilesToExpansion = refl

intermediateNumeratorMarginNotTerminal :
  Subject.intermediateNonWilsonNumeratorMarginIsTerminalPremise ≡ false
intermediateNumeratorMarginNotTerminal = refl
