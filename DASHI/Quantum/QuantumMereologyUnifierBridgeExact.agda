{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyUnifierBridgeExact where

import DASHI.Unifier as U
import DASHI.Quantum.QuantumMereologyExact as QM

------------------------------------------------------------------------
-- Existing DASHI Hilbert skeleton -> bare quantum-mereology world.
--
-- The adapter deliberately supplies no TPS.  A Hilbert carrier plus dynamics
-- is exactly the upstream data whose subsystem decomposition remains open.
------------------------------------------------------------------------

fromHilbertSpace :
  (HS : U.HilbertSpace) →
  (Hamiltonian : Set) →
  (evolve :
    Hamiltonian →
    U.HilbertSpace.H HS →
    U.HilbertSpace.H HS) →
  QM.BareQuantumWorld
fromHilbertSpace HS Hamiltonian evolve = record
  { QM.BareQuantumWorld.HilbertCarrier = U.HilbertSpace.H HS
  ; QM.BareQuantumWorld.State = U.HilbertSpace.H HS
  ; QM.BareQuantumWorld.Hamiltonian = Hamiltonian
  ; QM.BareQuantumWorld.carrierState = λ state → state
  ; QM.BareQuantumWorld.evolve = evolve
  }
