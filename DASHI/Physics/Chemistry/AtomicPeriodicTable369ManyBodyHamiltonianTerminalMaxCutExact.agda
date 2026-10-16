module DASHI.Physics.Chemistry.AtomicPeriodicTable369ManyBodyHamiltonianTerminalMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369C3FourierSpatialRestrictionExact as Fourier
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ExteriorC3RepresentationExact as Exterior
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ExteriorHodgeC3IntertwinerExact as Hodge
import DASHI.Physics.Chemistry.AtomicPeriodicTable369HamiltonianC3IntertwinerExact as H
import DASHI.Physics.Chemistry.AtomicPeriodicTable369CentralCoulombC3CompilerExact as Coulomb
import DASHI.Physics.Chemistry.AtomicPeriodicTable369P2CoulombExecutionExact as P2
import DASHI.Physics.Chemistry.AtomicPeriodicTable369SymmetryProjectionCompilerExact as Projection
import DASHI.Physics.Chemistry.AtomicPeriodicTable369HamiltonianCarrierAuditExact as Audit

------------------------------------------------------------------------
-- Machine-readable terminal cut after the first interaction-sensitive atomic
-- payment.  This is deliberately finer than the parent PR's earlier boundary.
------------------------------------------------------------------------

record Atomic369ManyBodyTerminalStatus : Set where
  constructor atomic369ManyBodyTerminalStatus
  field
    chargeSpatialC3FourierEquivalencePaid : Bool
    explicitWedge2Wedge3ActionPaid : Bool
    finiteHodgeWedge2IntertwinerPaid : Bool
    hydrogenicPTripletRestrictedHamiltonianPaid : Bool
    centralPotentialSymmetryCompilerPaid : Bool
    pairCoulombSymmetryCompilerPaid : Bool
    exactHydrogenicP2ProjectedCoulombMatrixPaid : Bool
    interactionSensitiveP2C3CommutationPaid : Bool
    sameObjectProjectionCompilerPaid : Bool
    surroundingHamiltonianCarrierAuditPaid : Bool

    completeComplexLinearFockAlgebraPaid : Bool
    sameObjectAnalyticSpatialC3HilbertActionPaid : Bool
    continuumKineticOperatorCovariancePaid : Bool
    fullContinuumCoulombHamiltonianCommutationPaid : Bool
    explicitEquivariantCIProjectionPaid : Bool
    actualAtomicGeneratorInteractingAttachmentPaid : Bool
    spinOrbitFineStructurePaid : Bool
    correlationBeyondSelectedP2SectorPaid : Bool
    empiricalSpectroscopyRecoveryPaid : Bool
    fullAtom369IdentityPaid : Bool

open Atomic369ManyBodyTerminalStatus public

canonicalAtomic369ManyBodyTerminalStatus : Atomic369ManyBodyTerminalStatus
canonicalAtomic369ManyBodyTerminalStatus =
  atomic369ManyBodyTerminalStatus
    true true true true true true true true true true
    false false false false false false false false false false

firstLiveLeaf : String
firstLiveLeaf =
  "same-object analytic spatial C3/Hilbert action plus kinetic covariance; then use the projection compiler to attach the full Coulomb Hamiltonian to an explicit selected CI carrier"

interactionNoLongerFirstLeaf : String
interactionNoLongerFirstLeaf =
  "electron-electron Coulomb interaction is already executed exactly on the selected common-spin hydrogenic 2p^2 antisymmetric sector: V_ee=(21/128) I_3"

fullAtomIdentityStillFalse :
  fullAtom369IdentityPaid canonicalAtomic369ManyBodyTerminalStatus ≡ false
fullAtomIdentityStillFalse = refl

empiricalRecoveryStillFalse :
  empiricalSpectroscopyRecoveryPaid canonicalAtomic369ManyBodyTerminalStatus ≡ false
empiricalRecoveryStillFalse = refl
