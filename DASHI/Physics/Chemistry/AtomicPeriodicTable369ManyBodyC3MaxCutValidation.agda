module DASHI.Physics.Chemistry.AtomicPeriodicTable369ManyBodyC3MaxCutValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369C3FourierSpatialRestrictionExact as Fourier
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ExteriorC3RepresentationExact as Exterior
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ExteriorHodgeC3IntertwinerExact as Hodge
import DASHI.Physics.Chemistry.AtomicPeriodicTable369HamiltonianC3IntertwinerExact as Hamiltonian
import DASHI.Physics.Chemistry.AtomicPeriodicTable369HamiltonianCarrierAuditExact as Audit
import DASHI.Physics.Chemistry.AtomicPeriodicTable369CentralCoulombC3CompilerExact as Coulomb
import DASHI.Physics.Chemistry.AtomicPeriodicTable369P2CoulombExecutionExact as P2
import DASHI.Physics.Chemistry.AtomicPeriodicTable369SymmetryProjectionCompilerExact as Projection

------------------------------------------------------------------------
-- Fourier / representation-equivalence regression.
------------------------------------------------------------------------

fourierSameRepresentationPaid :
  Fourier.C3FourierSpatialRestrictionBoundary.sameRepresentationUpToFourierBasisPaid
    Fourier.canonicalC3FourierSpatialRestrictionBoundary
  ≡ true
fourierSameRepresentationPaid = refl

fourierSameMatrixRejected :
  Fourier.C3FourierSpatialRestrictionBoundary.sameMatrixInMagneticBasis
    Fourier.canonicalC3FourierSpatialRestrictionBoundary
  ≡ false
fourierSameMatrixRejected = refl

------------------------------------------------------------------------
-- Exterior-power regression.
------------------------------------------------------------------------

wedge2OrderThreeRegression :
  Exterior.wedge2PositiveStep
    (Exterior.wedge2PositiveStep
      (Exterior.wedge2PositiveStep Exterior.canonicalWedge2NegZero))
  ≡ Exterior.canonicalWedge2NegZero
wedge2OrderThreeRegression = Exterior.canonicalWedge2Orbit

wedge3ClosedDeterminantInvariant :
  Exterior.wedge3PositiveStep Exterior.wedgeNegZeroPos
  ≡ Exterior.wedgeNegZeroPos
wedge3ClosedDeterminantInvariant = refl

------------------------------------------------------------------------
-- Finite Hodge-style wedge2 <-> one-particle representation regression.
------------------------------------------------------------------------

hodgeWedge2IntertwinerPaid :
  Hodge.ExteriorHodgeC3Boundary.wedge2ToOneParticleC3IntertwinerPaid
    Hodge.canonicalExteriorHodgeC3Boundary
  ≡ true
hodgeWedge2IntertwinerPaid = refl

continuousSiblingNotImportedAsAuthority :
  Hodge.ExteriorHodgeC3Boundary.sibling1164ContinuousHodgeUsedAsTheoremAuthority
    Hodge.canonicalExteriorHodgeC3Boundary
  ≡ false
continuousSiblingNotImportedAsAuthority = refl

------------------------------------------------------------------------
-- Restricted Hamiltonian regression.
------------------------------------------------------------------------

restrictedHamiltonianPaid :
  Hamiltonian.HamiltonianC3Boundary.hydrogenicPTripletChargeCommutationPaid
    Hamiltonian.canonicalHamiltonianC3Boundary
  ≡ true
restrictedHamiltonianPaid = refl

interactingHamiltonianStillOpen :
  Hamiltonian.HamiltonianC3Boundary.actualAtomicGeneratorInteractingAttachmentInhabited
    Hamiltonian.canonicalHamiltonianC3Boundary
  ≡ false
interactingHamiltonianStillOpen = refl

------------------------------------------------------------------------
-- Central/pair-potential compiler regression.
------------------------------------------------------------------------

centralPotentialCompilerPaid :
  Coulomb.CentralCoulombC3Boundary.radiusPreservingActionImpliesCentralPotentialInvariant
    Coulomb.canonicalCentralCoulombC3Boundary
  ≡ true
centralPotentialCompilerPaid = refl

pairPotentialCompilerPaid :
  Coulomb.CentralCoulombC3Boundary.separationPreservingActionImpliesPairPotentialInvariant
    Coulomb.canonicalCentralCoulombC3Boundary
  ≡ true
pairPotentialCompilerPaid = refl

finiteChargeNotSpatialByDefinition :
  Coulomb.CentralCoulombC3Boundary.finiteChargeTransportIsSpatialRotationByDefinition
    Coulomb.canonicalCentralCoulombC3Boundary
  ≡ false
finiteChargeNotSpatialByDefinition = refl

------------------------------------------------------------------------
-- Exact hydrogenic p^2 Coulomb projection regression.
------------------------------------------------------------------------

p2InteractionSensitiveCommutationPaid :
  P2.P2CoulombExecutionBoundary.interactionSensitiveC3CommutationPaid
    P2.canonicalP2CoulombExecutionBoundary
  ≡ true
p2InteractionSensitiveCommutationPaid = refl

p2FullAtomIdentityRejected :
  P2.P2CoulombExecutionBoundary.fullAtom369IdentityPaid
    P2.canonicalP2CoulombExecutionBoundary
  ≡ false
p2FullAtomIdentityRejected = refl

p2MatrixInvariantRegression :
  P2.coulombMatrixElement
    (P2.p2C3Step P2.p2NegZero)
    (P2.p2C3Step P2.p2NegZero)
  ≡ P2.coulombMatrixElement P2.p2NegZero P2.p2NegZero
p2MatrixInvariantRegression = refl

------------------------------------------------------------------------
-- Projection compiler firewall regression.
------------------------------------------------------------------------

arbitraryTruncationRejected :
  Projection.SymmetryProjectionBoundary.arbitraryTruncationInheritsSymmetryAutomatically
    Projection.canonicalSymmetryProjectionBoundary
  ≡ false
arbitraryTruncationRejected = refl

sameObjectProjectionRequired :
  Projection.SymmetryProjectionBoundary.sameObjectSelectedHamiltonianEqualityRequired
    Projection.canonicalSymmetryProjectionBoundary
  ≡ true
sameObjectProjectionRequired = refl

------------------------------------------------------------------------
-- Surrounding-Hamiltonian same-carrier firewall.
------------------------------------------------------------------------

surroundingHamiltoniansExist :
  Audit.HamiltonianCarrierAuditBoundary.surroundingHamiltoniansExist
    Audit.canonicalHamiltonianCarrierAuditBoundary
  ≡ true
surroundingHamiltoniansExist = refl

surroundingNamesDoNotCreateSameCarrier :
  Audit.HamiltonianCarrierAuditBoundary.surroundingHamiltonianNameImpliesSameCarrier
    Audit.canonicalHamiltonianCarrierAuditBoundary
  ≡ false
surroundingNamesDoNotCreateSameCarrier = refl
