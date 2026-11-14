module DASHI.Algebra.Quantum.Atomic369AFQMCSameEnergySourceExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic
import DASHI.Algebra.Quantum.DASHIStructuredStateCompression as Compression
import DASHI.Algebra.Quantum.ShadowTrainedAFQMCReuseExact as AF

------------------------------------------------------------------------
-- SAME SOURCE: the existing atomic interacting-energy stage is the
-- energy whose observation is compared to the shadow-trained trial.
--
-- The atomic generator owns orbital/many-electron/energy stages.
-- The AFQMC owner already proves finite-walker estimator bounds given
-- real fitting and stability witnesses. This module combines the two
-- ORIGINAL carriers. It does not manufacture Hamiltonian integrals,
-- an auxiliary-field measure, a phaseless propagator, or calibration.
--
-- Attribution: DASHI AtomicPeriodicTable369GenerativeExact source;
-- Provazza, Knitter et al. for the external shadow-training experiment;
-- AFQMC source witnesses remain separately accountable.
------------------------------------------------------------------------

module SameSource
  {M : Compression.CompressionModel}
  (S : AF.ShadowTrialInterface M)
  (E : AF.EnergyTransport S)
  (G : Atomic.AtomicGenerator) where

  record AtomicWalkerEnergySource : Set₁ where
    field
      atomicIndex : Atomic.AtomicIndex
      walkerManyElectron :
        AF.Walker S → Atomic.AtomicGenerator.ManyElectronState G
      energyObservation :
        Atomic.AtomicGenerator.InteractingEnergy G → Nat
      -- The *same* atomic generator and nuclear/electronic identity
      -- provide the ideal local-energy observation for every walker.
      idealIsAtomicEnergy :
        (d : AF.Measurements S) (w : AF.Walker S) →
        energyObservation
          (Atomic.AtomicGenerator.interactingEnergy G
            atomicIndex (walkerManyElectron w))
        ≡ AF.idealLocalEnergy E d w

  open AtomicWalkerEnergySource public

  atomicSourceEnergyBoundOnRun :
    (B : AtomicWalkerEnergySource) →
    (R : AF.FiniteWalkerRun S) →
    (d : AF.Measurements S) (n : Nat) →
    AF.energyDiscrepancy E
      (energyObservation B
        (Atomic.AtomicGenerator.interactingEnergy G
          (atomicIndex B) (walkerManyElectron B (AF.walk R n))))
      (AF.learnedLocalEnergy E d (AF.walk R n))
    ≤ AF.energyBudget E
  atomicSourceEnergyBoundOnRun B R d n
    rewrite idealIsAtomicEnergy B d (AF.walk R n) =
    AF.energyBoundOnRun E R d n

  -- Unlike a generic Hamiltonian-interface adapter, this theorem
  -- explicitly retains the selected atomic generator and its original
  -- AtomicIndex in the estimator statement. Empirical witnesses are
  -- still required to inhabit AtomicWalkerEnergySource and E.
