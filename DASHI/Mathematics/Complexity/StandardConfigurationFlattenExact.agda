module DASHI.Mathematics.Complexity.StandardConfigurationFlattenExact where

------------------------------------------------------------------------
-- ABSOLUTE SYMBOL-LIST VIEW OF A SPLIT-TAPE STANDARD CONFIGURATION
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeStandardCanonicalProjectionExact as Canonical
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StructuralStandardMachineSimulationExact as Structural

reverse :
  ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) =
  Local.append (reverse xs) (x ∷ [])

appendAssoc :
  ∀ {A : Set}
    (xs ys zs : List A) →
  Local.append (Local.append xs ys) zs
  ≡ Local.append xs (Local.append ys zs)
appendAssoc [] ys zs = refl
appendAssoc (x ∷ xs) ys zs
  rewrite appendAssoc xs ys zs = refl

reverseAppend :
  ∀ {A : Set}
    (xs ys : List A) →
  reverse (Local.append xs ys)
  ≡ Local.append (reverse ys) (reverse xs)
reverseAppend [] ys = refl
reverseAppend (x ∷ xs) ys
  rewrite reverseAppend xs ys
        | appendAssoc (reverse ys) (reverse xs) (x ∷ []) =
  refl

mapAppend :
  ∀ {A B : Set}
    (f : A → B)
    (xs ys : List A) →
  Structural.mapList f (Local.append xs ys)
  ≡ Local.append (Structural.mapList f xs) (Structural.mapList f ys)
mapAppend f [] ys = refl
mapAppend f (x ∷ xs) ys
  rewrite mapAppend f xs ys = refl

mapReverse :
  ∀ {A B : Set}
    (f : A → B)
    (xs : List A) →
  Structural.mapList f (reverse xs)
  ≡ reverse (Structural.mapList f xs)
mapReverse f [] = refl
mapReverse f (x ∷ xs)
  rewrite mapAppend f (reverse xs) (x ∷ [])
        | mapReverse f xs =
  refl

flattenConfiguration :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol} →
  Standard.StandardConfiguration machine →
  List Symbol
flattenConfiguration configuration =
  Local.append
    (reverse (Standard.left configuration))
    (Standard.scanned configuration ∷ Standard.right configuration)

flattenAppendSymbolFarLeft :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    (symbol : Symbol)
    (configuration : Standard.StandardConfiguration machine) →
  flattenConfiguration
    (Canonical.appendSymbolFarLeft symbol configuration)
  ≡ symbol ∷ flattenConfiguration configuration
flattenAppendSymbolFarLeft symbol configuration
  rewrite reverseAppend (Standard.left configuration) (symbol ∷ []) =
  refl

flattenStructuralEmbed :
  ∀ {SourceState SourceSymbol TargetState TargetSymbol : Set}
    {source : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
    {target : Standard.StandardSingleTapeMachine TargetState TargetSymbol}
    (stateMap : SourceState → TargetState)
    (symbolMap : SourceSymbol → TargetSymbol)
    (configuration : Standard.StandardConfiguration source) →
  flattenConfiguration
    (Structural.structuralEmbed
      {target = target}
      stateMap symbolMap configuration)
  ≡
  Structural.mapList symbolMap (flattenConfiguration configuration)
flattenStructuralEmbed stateMap symbolMap configuration
  rewrite mapReverse symbolMap (Standard.left configuration)
        | mapAppend symbolMap
            (reverse (Standard.left configuration))
            (Standard.scanned configuration ∷ Standard.right configuration) =
  refl

------------------------------------------------------------------------
-- This owner is purely representational. It lets downstream resource proofs
-- compare the literal symbol content of concrete rows and structurally embedded
-- standard configurations without collapsing head/control data into symbols.
------------------------------------------------------------------------
