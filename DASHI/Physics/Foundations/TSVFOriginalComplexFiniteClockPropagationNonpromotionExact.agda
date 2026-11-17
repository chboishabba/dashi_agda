{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOriginalComplexFiniteClockPropagationNonpromotionExact where

------------------------------------------------------------------------
-- OBS04/OBS05/OBS07: ACTUAL concrete original TSVF complex source
-- has NO time-resolving physical propagation. This is not an
-- arbitrary singleton countermodel: it uses the source-checked
-- TSVF2017OriginalComplexABLSelectedExact.finiteComplexQuantum,
-- whose amplitude/ABL calculations are genuinely complex and
-- nontrivial but whose Time = Unit and evolveKet/evolveBra are
-- identity functions.
--
-- Therefore this source itself cannot distinguish two clock times
-- or generate a nonzero physical retarded time derivative. Physical
-- Kubo, propagation front and dimensionality require adding an
-- independently selected, nontrivial source dynamics, not renaming
-- the two-boundary condition into a spatial causal Lorentz cone.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Quantum.TSVF as Q
import DASHI.Quantum.TSVF2017OriginalComplexABLSelectedExact as Original

ConcreteTime : Set
ConcreteTime = Q.QuantumSurface.Time Original.finiteComplexQuantum

ConcreteKet : Set
ConcreteKet = Q.QuantumSurface.Ket Original.finiteComplexQuantum

ConcreteBra : Set
ConcreteBra = Q.QuantumSurface.Bra Original.finiteComplexQuantum

actualComplexTSVFTimeHasOnePoint :
  ∀ (t u : ConcreteTime) → t ≡ u
actualComplexTSVFTimeHasOnePoint tt tt = refl

actualOriginalComplexEvolutionPreservesEveryKet :
  ∀ (from to : ConcreteTime) (ket : ConcreteKet) →
  Q.QuantumSurface.evolveKet Original.finiteComplexQuantum
    from to ket ≡ ket
actualOriginalComplexEvolutionPreservesEveryKet tt tt ket = refl

actualOriginalComplexEvolutionPreservesEveryBra :
  ∀ (from to : ConcreteTime) (bra : ConcreteBra) →
  Q.QuantumSurface.evolveBra Original.finiteComplexQuantum
    from to bra ≡ bra
actualOriginalComplexEvolutionPreservesEveryBra tt tt bra = refl

-- A putative nonzero clock displacement between two *original*
-- finite complex selected times contradicts their actual Unit type.
actualOriginalComplexHasNoSeparatedClockReadings :
  ∀ (t u : ConcreteTime) →
  (t ≡ u → ⊥) → ⊥
actualOriginalComplexHasNoSeparatedClockReadings t u distinct =
  distinct (actualComplexTSVFTimeHasOnePoint t u)

-- This does not exclude physically richer TSVF models. It proves
-- that this original, already-proved complex amplitude/ABL instance
-- alone cannot discharge the OBS05/06/07/08/09 physical producer.
