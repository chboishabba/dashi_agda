{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.DeviceDissipationMonotonicityBridgeExact where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Energy.Core as EC
import DASHI.Analysis.DissipationPathMonotonicity as DPM

------------------------------------------------------------------------
-- ACTUAL REPO ANALYSIS REUSE
--
-- DASHI.Analysis.DissipationPathMonotonicity already proves that any exact
-- balance F(before) = F(after) + D in an ordered additive energy space yields
-- one-step and finite-path energy descent.  Device solvers should therefore
-- supply a physical/numerical energy and exact balance rather than re-proving
-- monotonicity ad hoc.
------------------------------------------------------------------------

record DeviceDissipativeSolver
    {x e i : Level}
    {State : Set x}
    {Energy : Set e}
    (ES : EC.EnergySpace State Energy)
    (Input : Set i)
    : Set (lsuc (x ⊔ e ⊔ i)) where
  field
    transition : DPM.DissipativeTransition ES Input

open DeviceDissipativeSolver public

deviceMonotonicityCertificate :
  ∀ {x e i}
    {State : Set x}
    {Energy : Set e}
    {Input : Set i}
    {ES : EC.EnergySpace State Energy} →
  (solver : DeviceDissipativeSolver ES Input) →
  DPM.DissipationMonotonicityCertificate (transition solver)
deviceMonotonicityCertificate solver =
  DPM.certifyDissipationMonotonicity (transition solver)

------------------------------------------------------------------------
-- Finite bookkeeping fixture for a relaxation residual.  This is not claimed
-- to be electrostatic free energy; it only exhibits the exact balance shape the
-- generic theorem expects from a concrete physical solver.
------------------------------------------------------------------------

record RelaxationBalance : Set where
  constructor relaxationBalance
  field
    beforeEnergyCode : Nat
    afterEnergyCode  : Nat
    dissipatedCode   : Nat
    exactBalance     : afterEnergyCode + dissipatedCode ≡ beforeEnergyCode

open RelaxationBalance public

syntheticRelaxation : RelaxationBalance
syntheticRelaxation = relaxationBalance 100 70 30 refl

data DeviceEnergyResidual : Set where
  ElectrostaticFreeEnergy      : DeviceEnergyResidual
  CarrierEntropyContribution   : DeviceEnergyResidual
  RecombinationDissipation     : DeviceEnergyResidual
  ContactBoundaryWork          : DeviceEnergyResidual
  SolverStepEnergyIdentity     : DeviceEnergyResidual
  PhysicalNonnegativityProof   : DeviceEnergyResidual
  NonlinearConvergenceReceipt  : DeviceEnergyResidual

-- Firewall:
-- a decreasing numerical residual != a physically justified free-energy law.
