{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyFiniteNoMeetRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Quantum.QuantumMereologyExact as QM

------------------------------------------------------------------------
-- FINITE STRUCTURAL REGRESSION
--
-- This proves only that the abstract TPSRefinementSpace interface does not
-- force a lattice/meet.  It is NOT the Pasqualini--Fortin theorem about the
-- physical space of Hilbert-space tensor-product structures.
------------------------------------------------------------------------

toyWorld : QM.BareQuantumWorld
toyWorld = record
  { QM.BareQuantumWorld.HilbertCarrier = ⊤
  ; QM.BareQuantumWorld.State = ⊤
  ; QM.BareQuantumWorld.Hamiltonian = ⊤
  ; QM.BareQuantumWorld.carrierState = λ _ → tt
  ; QM.BareQuantumWorld.evolve = λ _ _ → tt
  }

toyTPS : QM.TensorProductStructure toyWorld
toyTPS = record
  { QM.TensorProductStructure.Subsystem = ⊤
  ; QM.TensorProductStructure.FactorIndex = ⊤
  ; QM.TensorProductStructure.subsystemAt = λ _ → tt
  ; QM.TensorProductStructure.subsystemPartOfCarrier = λ _ → ⊤
  ; QM.TensorProductStructure.ReconstructsCarrier = ⊤
  ; QM.TensorProductStructure.reconstruction = tt
  ; QM.TensorProductStructure.Entangled = λ _ _ _ → ⊤
  ; QM.TensorProductStructure.Interacts = λ _ _ _ → ⊤
  }

data TPSTag : Set where
  leftTPS rightTPS : TPSTag

tagRefines : TPSTag → TPSTag → Set
tagRefines left right = left ≡ right

toyRefinementSpace : QM.TPSRefinementSpace toyWorld
toyRefinementSpace = record
  { QM.TPSRefinementSpace.TPS = TPSTag
  ; QM.TPSRefinementSpace.realizes = λ _ → toyTPS
  ; QM.TPSRefinementSpace.Refines = tagRefines
  }

leftNotRight : leftTPS ≡ rightTPS → ⊥
leftNotRight ()

toyRefinementSpaceHasNoCanonicalMeet :
  QM.CanonicalMeetAuthority toyRefinementSpace → ⊥
toyRefinementSpaceHasNoCanonicalMeet authority
  with QM.meet authority leftTPS rightTPS
... | leftTPS =
  leftNotRight
    (QM.meetRefinesRight authority leftTPS rightTPS)
... | rightTPS =
  leftNotRight
    (sym (QM.meetRefinesLeft authority leftTPS rightTPS))
