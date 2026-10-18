module DASHI.Analysis.RiemannPrimitiveKernelFiltrationTransportExact where

------------------------------------------------------------------------
-- GENERIC KERNEL TRANSPORT FOR BASIS-CHANGED FILTERED FUNCTIONALS
--
-- The concrete Lean mirror instantiates this pattern over ZMod 243 for the RH
-- primitive coefficient covector.  Agda keeps the transport theorem generic:
--
--   oldFunctional (toOld y) = newFunctional y
--
-- plus a two-sided coordinate equivalence implies exact correspondence of the
-- two zero fibres.
--
-- This is the intrinsic replacement for treating a coordinate depth tuple as
-- basis invariant.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

record TwoSidedCoordinateEquivalence (Old New : Set) : Set where
  constructor two-sided-coordinate-equivalence
  field
    toOld : New -> Old
    toNew : Old -> New
    toOldAfterNew : (x : Old) -> toOld (toNew x) ≡ x
    toNewAfterOld : (y : New) -> toNew (toOld y) ≡ y

open TwoSidedCoordinateEquivalence public

record FunctionalKernelTransport
    {Old New Value : Set}
    (zeroValue : Value)
    (equiv : TwoSidedCoordinateEquivalence Old New) : Set₁ where
  constructor functional-kernel-transport
  field
    oldFunctional : Old -> Value
    newFunctional : New -> Value
    functionalCommutes :
      (y : New) ->
      oldFunctional (toOld equiv y) ≡ newFunctional y

open FunctionalKernelTransport public

OldKernel :
  {Old New Value : Set}
  {zeroValue : Value}
  {equiv : TwoSidedCoordinateEquivalence Old New} ->
  FunctionalKernelTransport zeroValue equiv ->
  Old ->
  Set
OldKernel {zeroValue = zeroValue} transport x =
  oldFunctional transport x ≡ zeroValue

NewKernel :
  {Old New Value : Set}
  {zeroValue : Value}
  {equiv : TwoSidedCoordinateEquivalence Old New} ->
  FunctionalKernelTransport zeroValue equiv ->
  New ->
  Set
NewKernel {zeroValue = zeroValue} transport y =
  newFunctional transport y ≡ zeroValue

oldKernelToNewKernel :
  {Old New Value : Set}
  {zeroValue : Value}
  {equiv : TwoSidedCoordinateEquivalence Old New}
  (transport : FunctionalKernelTransport zeroValue equiv)
  (y : New) ->
  OldKernel transport (toOld equiv y) ->
  NewKernel transport y
oldKernelToNewKernel transport y oldZero =
  trans
    (sym (functionalCommutes transport y))
    oldZero

newKernelToOldKernel :
  {Old New Value : Set}
  {zeroValue : Value}
  {equiv : TwoSidedCoordinateEquivalence Old New}
  (transport : FunctionalKernelTransport zeroValue equiv)
  (y : New) ->
  NewKernel transport y ->
  OldKernel transport (toOld equiv y)
newKernelToOldKernel transport y newZero =
  trans
    (functionalCommutes transport y)
    newZero

record KernelCorrespondence
    {Old New Value : Set}
    {zeroValue : Value}
    {equiv : TwoSidedCoordinateEquivalence Old New}
    (transport : FunctionalKernelTransport zeroValue equiv)
    (y : New) : Set where
  constructor kernel-correspondence
  field
    oldToNew :
      OldKernel transport (toOld equiv y) ->
      NewKernel transport y
    newToOld :
      NewKernel transport y ->
      OldKernel transport (toOld equiv y)

canonicalKernelCorrespondence :
  {Old New Value : Set}
  {zeroValue : Value}
  {equiv : TwoSidedCoordinateEquivalence Old New}
  (transport : FunctionalKernelTransport zeroValue equiv)
  (y : New) ->
  KernelCorrespondence transport y
canonicalKernelCorrespondence transport y =
  kernel-correspondence
    (oldKernelToNewKernel transport y)
    (newKernelToOldKernel transport y)

------------------------------------------------------------------------
-- Status / firewall.
------------------------------------------------------------------------

data CoordinateAxesAreIntrinsicKernel : Set where

coordinateAxesDoNotBecomeIntrinsicKernel :
  CoordinateAxesAreIntrinsicKernel -> ⊥
coordinateAxesDoNotBecomeIntrinsicKernel ()

record RiemannPrimitiveKernelFiltrationTransportBoundary : Set where
  constructor riemann-primitive-kernel-filtration-transport-boundary
  field
    genericTwoSidedCoordinateEquivalenceOwned : Bool
    genericFunctionalCommutationOwned : Bool
    exactKernelCorrespondenceOwned : Bool
    coordinateAxisDescriptionPromotedToInvariant : Bool
    concreteZMod243InstantiationOwnedInAgdaHere : Bool
    concreteZMod243InstantiationOwnedInLeanMirror : Bool

canonicalRiemannPrimitiveKernelFiltrationTransportBoundary :
  RiemannPrimitiveKernelFiltrationTransportBoundary
canonicalRiemannPrimitiveKernelFiltrationTransportBoundary =
  riemann-primitive-kernel-filtration-transport-boundary
    true true true false false true
