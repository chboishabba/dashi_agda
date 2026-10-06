module DASHI.Analysis.CollatzSyracuseCompleteBlockBijectionExact where

------------------------------------------------------------------------
-- CANONICAL COMPLETE INTEGER BLOCK <-> PARITY WORD BIJECTION COMPILER
--
-- At level m, `Fin (2^m)` indexes the literal positive starts
--
--   1, 2, ..., 2^m.
--
-- The forward map is definitionally the first-m parity word of that literal
-- Syracuse start.  The only source-specific content left here is the inverse
-- index and its two round-trip laws.  Once supplied, exact uniform word mass
-- follows from the generic finite uniform-bijection transport core.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin; toℕ)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.Core.FiniteUniformBijectionTransportExact as Uniform
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder

blockStart :
  {m : Nat} →
  Fin (Cylinder.pow2 m) →
  Syracuse.PositiveNat
blockStart index = Syracuse.positiveNat (toℕ index)

blockWord :
  {m : Nat} →
  Fin (Cylinder.pow2 m) →
  Binary.BinaryWord m
blockWord {m} index = Itinerary.parityWord m (blockStart index)

record CompleteBlockWordIndexSource (m : Nat) : Set₁ where
  field
    wordIndex : Binary.BinaryWord m → Fin (Cylinder.pow2 m)
    indexWordIndex :
      (index : Fin (Cylinder.pow2 m)) →
      wordIndex (blockWord index) ≡ index
    wordIndexWord :
      (word : Binary.BinaryWord m) →
      blockWord (wordIndex word) ≡ word

open CompleteBlockWordIndexSource public

completeBlockWordBijection :
  {m : Nat} →
  CompleteBlockWordIndexSource m →
  Uniform.ExplicitBijection
    (Fin (Cylinder.pow2 m))
    (Binary.BinaryWord m)
completeBlockWordBijection source = record
  { Uniform.to = blockWord
  ; Uniform.from = wordIndex source
  ; Uniform.fromTo = indexWordIndex source
  ; Uniform.toFrom = wordIndexWord source
  }

completeBlockUniformWordMass :
  {m : Nat} →
  CompleteBlockWordIndexSource m →
  Uniform.UniformNatMass (Binary.BinaryWord m)
completeBlockUniformWordMass source =
  Uniform.transportUnitMass (completeBlockWordBijection source)

record CompleteBlockBijectionBoundary : Set where
  constructor completeBlockBijectionBoundary
  field
    literalStartsOneThroughPow2 : Nat
    forwardWordMapOwned : Nat
    inverseIndexStillSourceSpecific : Nat
    twoRoundTripsRequired : Nat
    exactUniformTransportGeneric : Nat
    spectralMixingRequired : Nat

canonicalCompleteBlockBijectionBoundary : CompleteBlockBijectionBoundary
canonicalCompleteBlockBijectionBoundary =
  completeBlockBijectionBoundary 1 1 1 1 1 0
