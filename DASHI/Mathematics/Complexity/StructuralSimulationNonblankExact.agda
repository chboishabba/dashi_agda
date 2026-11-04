module DASHI.Mathematics.Complexity.StructuralSimulationNonblankExact where

------------------------------------------------------------------------
-- INJECTIVE BLANK-PRESERVING STRUCTURAL SYMBOL MAPS PRESERVE NONBLANK COUNT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StructuralStandardMachineSimulationExact as Structural
import DASHI.Mathematics.Complexity.ConcreteTapeNonblankWriteBoundExact as Nonblank

nonblankBitStructuralExact :
  ∀ {SourceState SourceSymbol TargetState TargetSymbol : Set}
    {source : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
    {target : Standard.StandardSingleTapeMachine TargetState TargetSymbol}
    (sourceEnumeration : Local.FiniteEnumeration SourceSymbol)
    (targetEnumeration : Local.FiniteEnumeration TargetSymbol)
    (structural : Structural.StructuralStandardMachineSimulation source target)
    (symbol : SourceSymbol) →
  Nonblank.nonblankBit
      targetEnumeration
      (Standard.blank target)
      (Structural.symbolMap structural symbol)
  ≡
  Nonblank.nonblankBit
      sourceEnumeration
      (Standard.blank source)
      symbol
nonblankBitStructuralExact
    {source = source} {target = target}
    sourceEnumeration targetEnumeration structural symbol
    with Local.decideEqual sourceEnumeration symbol (Standard.blank source)
... | true
    with Local.decideEqualSound sourceEnumeration refl
... | refl
    rewrite Structural.blankExact structural
          | Local.decideEqualRefl targetEnumeration (Standard.blank target) =
    refl
... | false
    with Local.decideEqual targetEnumeration
      (Structural.symbolMap structural symbol)
      (Standard.blank target)
... | false = refl
... | true
    with Local.decideEqualSound targetEnumeration refl
... | mappedBlank
    with Structural.symbolMapInjective structural
      (trans mappedBlank (sym (Structural.blankExact structural)))
... | refl
    with Local.decideEqualRefl sourceEnumeration (Standard.blank source)
... | ()

structuralMapNonblankCountExact :
  ∀ {SourceState SourceSymbol TargetState TargetSymbol : Set}
    {source : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
    {target : Standard.StandardSingleTapeMachine TargetState TargetSymbol}
    (sourceEnumeration : Local.FiniteEnumeration SourceSymbol)
    (targetEnumeration : Local.FiniteEnumeration TargetSymbol)
    (structural : Structural.StructuralStandardMachineSimulation source target)
    (symbols : List SourceSymbol) →
  Nonblank.nonblankCount
      targetEnumeration
      (Standard.blank target)
      (Structural.mapList (Structural.symbolMap structural) symbols)
  ≡
  Nonblank.nonblankCount
      sourceEnumeration
      (Standard.blank source)
      symbols
structuralMapNonblankCountExact sourceEnumeration targetEnumeration structural [] =
  refl
structuralMapNonblankCountExact
    sourceEnumeration targetEnumeration structural (symbol ∷ symbols)
  rewrite nonblankBitStructuralExact
            sourceEnumeration targetEnumeration structural symbol
        | structuralMapNonblankCountExact
            sourceEnumeration targetEnumeration structural symbols =
  refl

------------------------------------------------------------------------
-- This is the information analogue of exact span preservation: structural
-- simulation cannot make source data cheaper by mapping nonblank symbols to
-- target blank or by merging distinct source symbols.
------------------------------------------------------------------------
