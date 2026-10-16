module DASHI.Physics.Chemistry.AtomicPeriodicTable369ManyBodyC3MaxCutValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369C3FourierSpatialRestrictionExact as Fourier
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ExteriorC3RepresentationExact as Exterior
import DASHI.Physics.Chemistry.AtomicPeriodicTable369HamiltonianC3IntertwinerExact as Hamiltonian
import DASHI.Physics.Chemistry.AtomicPeriodicTable369HamiltonianCarrierAuditExact as Audit
import DASHI.Physics.Chemistry.AtomicPeriodicTable369CentralCoulombC3CompilerExact as Coulomb

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
