module DASHI.Mathematics.Complexity.StructuralStandardMachineSimulationExact where

------------------------------------------------------------------------
-- STRUCTURAL SINGLE-TAPE SIMULATION
--
-- The generic StandardMachineSimulation permits an arbitrary configuration
-- embedding. That is appropriate for semantic simulation, but too weak for
-- resource-closing compilation: an unconstrained meta-level embed could hide
-- uncharged representation work.
--
-- This owner requires the embedding to be pointwise on the literal standard
-- tape representation and faithful on tape symbols:
--
--   source state  -> target state
--   source symbol -> target symbol (injectively)
--   source blank  -> target blank exactly
--   left/right tape lists mapped elementwise
--   scanned symbol mapped directly.
--
-- Hence configuration shape and represented tape span are preserved exactly,
-- and nonblank source data cannot collapse to target blank.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardMachineSimulationExact as Simulation

mapList :
  ∀ {A B : Set} →
  (A → B) →
  List A →
  List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

listLength :
  ∀ {A : Set} →
  List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

mapListLength :
  ∀ {A B : Set}
    (f : A → B)
    (xs : List A) →
  listLength (mapList f xs) ≡ listLength xs
mapListLength f [] = refl
mapListLength f (x ∷ xs)
  rewrite mapListLength f xs = refl

configurationSpan :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol} →
  Standard.StandardConfiguration machine → Nat
configurationSpan configuration =
  listLength (Standard.left configuration)
  + suc (listLength (Standard.right configuration))

structuralEmbed :
  ∀ {SourceState SourceSymbol TargetState TargetSymbol : Set}
    {source : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
    {target : Standard.StandardSingleTapeMachine TargetState TargetSymbol} →
  (SourceState → TargetState) →
  (SourceSymbol → TargetSymbol) →
  Standard.StandardConfiguration source →
  Standard.StandardConfiguration target
structuralEmbed stateMap symbolMap configuration =
  Standard.standard-configuration
    (mapList symbolMap (Standard.left configuration))
    (stateMap (Standard.state configuration))
    (symbolMap (Standard.scanned configuration))
    (mapList symbolMap (Standard.right configuration))

structuralEmbedSpanExact :
  ∀ {SourceState SourceSymbol TargetState TargetSymbol : Set}
    {source : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
    {target : Standard.StandardSingleTapeMachine TargetState TargetSymbol}
    (stateMap : SourceState → TargetState)
    (symbolMap : SourceSymbol → TargetSymbol)
    (configuration : Standard.StandardConfiguration source) →
  configurationSpan
    (structuralEmbed {target = target} stateMap symbolMap configuration)
  ≡ configurationSpan configuration
structuralEmbedSpanExact stateMap symbolMap configuration
  rewrite mapListLength symbolMap (Standard.left configuration)
        | mapListLength symbolMap (Standard.right configuration) =
  refl

record StructuralStandardMachineSimulation
    {SourceState SourceSymbol TargetState TargetSymbol : Set}
    (source : Standard.StandardSingleTapeMachine SourceState SourceSymbol)
    (target : Standard.StandardSingleTapeMachine TargetState TargetSymbol) : Set₁ where
  field
    stateMap : SourceState → TargetState
    symbolMap : SourceSymbol → TargetSymbol

    symbolMapInjective :
      ∀ {left right} →
      symbolMap left ≡ symbolMap right →
      left ≡ right

    blankExact :
      symbolMap (Standard.blank source)
      ≡ Standard.blank target

    stepExact :
      ∀ {before after} →
      Standard.standardNext source before ≡ just after →
      Standard.standardNext target
        (structuralEmbed stateMap symbolMap before)
      ≡ just (structuralEmbed stateMap symbolMap after)

open StructuralStandardMachineSimulation public

structuralToSimulation :
  ∀ {SourceState SourceSymbol TargetState TargetSymbol : Set}
    {source : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
    {target : Standard.StandardSingleTapeMachine TargetState TargetSymbol} →
  StructuralStandardMachineSimulation source target →
  Simulation.StandardMachineSimulation source target
structuralToSimulation structural = record
  { Simulation.embed =
      structuralEmbed
        (stateMap structural)
        (symbolMap structural)
  ; Simulation.stepExact =
      stepExact structural
  }

structuralSimulationSpanExact :
  ∀ {SourceState SourceSymbol TargetState TargetSymbol : Set}
    {source : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
    {target : Standard.StandardSingleTapeMachine TargetState TargetSymbol}
    (structural : StructuralStandardMachineSimulation source target)
    (configuration : Standard.StandardConfiguration source) →
  configurationSpan
    (Simulation.embed (structuralToSimulation structural) configuration)
  ≡ configurationSpan configuration
structuralSimulationSpanExact structural =
  structuralEmbedSpanExact
    (stateMap structural)
    (symbolMap structural)

sourceNonblankMapsToTargetNonblank :
  ∀ {SourceState SourceSymbol TargetState TargetSymbol : Set}
    {source : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
    {target : Standard.StandardSingleTapeMachine TargetState TargetSymbol}
    (structural : StructuralStandardMachineSimulation source target)
    {symbol : SourceSymbol} →
  symbol ≡ Standard.blank source →
  StructuralStandardMachineSimulation.symbolMap structural symbol
    ≡ Standard.blank target
sourceNonblankMapsToTargetNonblank structural refl =
  blankExact structural

------------------------------------------------------------------------
-- RESOURCE FIREWALL
--
-- This does not assert that every semantic simulation is structural. It gives
-- the stronger interface that the Clay-critical compiler must use when it
-- claims to run a source single-tape machine inside a target single-tape
-- machine without hidden representation expansion or symbol collapse.
------------------------------------------------------------------------
