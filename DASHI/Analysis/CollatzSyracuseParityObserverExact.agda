module DASHI.Analysis.CollatzSyracuseParityObserverExact where

------------------------------------------------------------------------
-- SAME-OBJECT PARITY OBSERVER
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.Foundations.HyperformChartGluingExact as Gluing
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder

syracuseParityObserver :
  (m : Nat) →
  Gluing.ObserverWithFibre Syracuse.PositiveNat (Binary.BinaryWord m)
syracuseParityObserver m = record
  { Gluing.observe = Itinerary.parityWord m }

observerFibreIsResidueCylinder :
  (source : Cylinder.ParityCylinderSource) →
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (x : Syracuse.PositiveNat) →
  (Gluing.ObserverFibre (syracuseParityObserver m) word x →
    Syracuse.toNat x % Cylinder.pow2 m
      ≡ Cylinder.residueOfParityWord source word)
  ×
  (Syracuse.toNat x % Cylinder.pow2 m
      ≡ Cylinder.residueOfParityWord source word →
    Gluing.ObserverFibre (syracuseParityObserver m) word x)
observerFibreIsResidueCylinder source word x =
  Cylinder.parityCylinderIff source word x
  where
    open import Data.Nat.DivMod using (_%_)
    open import Data.Product using (_×_)

record ParityObserverBoundary : Set where
  constructor parityObserverBoundary
  field
    observerForgetsIntegerInformation : Nat
    observerFibreRetained : Nat
    sharedObservableImpliesKernelEquality : Nat

canonicalParityObserverBoundary : ParityObserverBoundary
canonicalParityObserverBoundary = parityObserverBoundary 1 1 0
