module DASHI.Physics.Chemistry.AtomicPeriodicTable369AFQMCSameSourceExact where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic
import DASHI.Physics.Chemistry.AtomicPeriodicTable369Nickel41ElectronAccountingExact as Nickel41
import DASHI.Physics.Chemistry.AtomicPeriodicTable369HartreeFockReuseExact as HartreeFock

------------------------------------------------------------------------
-- Same-source atomic interacting-energy transport.
-- Attribution: DASHI atomic owner; AFQMC algorithm reference
-- Provazza et al. arXiv:2611.08129 (2026); Zhao et al. arXiv:2506.22408.
--
-- A numerical FCIDUMP producer can discharge the equality only after
-- its orbital integrals, electron sector, units and geometry have been
-- identified with those of the selected AtomicGenerator.
-- This owner DOES NOT fill in missing molecular data or prove a model
-- is the published nickel reaction.
------------------------------------------------------------------------

record AtomicAFQMCInstance (G : Atomic.AtomicGenerator) : Set₁ where
  field
    atom : Atomic.AtomicIndex
    Walker : Set
    electronicState : Walker → Atomic.AtomicGenerator.ManyElectronState G
    walkerEnergy : Walker → Atomic.AtomicGenerator.InteractingEnergy G
    energyIsAtomic :
      ∀ walker →
      walkerEnergy walker ≡
      Atomic.AtomicGenerator.interactingEnergy G atom (electronicState walker)

open AtomicAFQMCInstance public

record AtomicAFQMCRun
    {G : Atomic.AtomicGenerator}
    (I : AtomicAFQMCInstance G) : Set where
  field
    walkerAt : Nat → Walker I

open AtomicAFQMCRun public

sameSourceEnergyAt :
  ∀ {G : Atomic.AtomicGenerator}
    {I : AtomicAFQMCInstance G} →
  (R : AtomicAFQMCRun I) →
  (n : Nat) →
  walkerEnergy I (walkerAt R n) ≡
  Atomic.AtomicGenerator.interactingEnergy G
    (atom I) (electronicState I (walkerAt R n))
sameSourceEnergyAt {I = I} R n =
  energyIsAtomic I (walkerAt R n)

-- Even a complete conditional same-source equality cannot construct
-- the missing chemical Hamiltonian, force bias, NQS or measurements.
data AtomicInterfaceImpliesNickelMeasurement : Set where

noMeasurementFromAtomicInterface :
  AtomicInterfaceImpliesNickelMeasurement → ⊥
noMeasurementFromAtomicInterface ()
