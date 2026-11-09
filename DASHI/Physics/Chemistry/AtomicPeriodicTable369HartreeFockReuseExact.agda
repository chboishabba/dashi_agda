module DASHI.Physics.Chemistry.AtomicPeriodicTable369HartreeFockReuseExact where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AtomicPeriodicTable369HeliumHartreeConvergenceExact as He
import DASHI.Physics.Chemistry.AtomicPeriodicTable369Nickel41ElectronAccountingExact as Ni

------------------------------------------------------------------------
-- EXISTING source ownership is reused, NOT reconstructed.
--
-- Helium radial producer is already executed and its limit independently
-- compared to the published closed-shell Hartree-Fock energy. The existing
-- evidence explicitly identifies it as RHF-equivalent only for the one-
-- spatial-orbital two-electron helium model. Nothing in this module creates
-- nickel STO-3G Gaussian integrals, a molecular RHF root, or AFQMC data.
------------------------------------------------------------------------

heliumRHFClassConvergenceWasAlreadyPaid :
  He.HeliumHartreeConvergenceReceipt.monotoneTowardPublishedHFLimit
    He.canonicalHeliumHartreeConvergenceReceipt ≡ true
  ×
  He.HeliumHartreeConvergenceReceipt.overallPassed
    He.canonicalHeliumHartreeConvergenceReceipt ≡ true
heliumRHFClassConvergenceWasAlreadyPaid = refl , refl

heliumCorrelationBeyondRHFRemainsOpen :
  He.HeliumHartreeConvergenceBoundary.electronCorrelationPaid
    He.canonicalHeliumHartreeConvergenceBoundary ≡ false
heliumCorrelationBeyondRHFRemainsOpen = refl

heliumMultiOrbitalStateTrackingRemainsOpen :
  He.HeliumHartreeConvergenceBoundary.genericMultiOrbitalStateTrackingPaid
    He.canonicalHeliumHartreeConvergenceBoundary ≡ false
heliumMultiOrbitalStateTrackingRemainsOpen = refl

-- The nickel source (neutral molecular hypothesis, not original QPU evidence)
-- contains 80 paired inactive orbitals plus 4 active alpha and 4 beta
-- electrons. Those numbers cannot be inferred from a one-orbital HF object.
nickelHasEightyHypotheticalCorePairs :
  Ni.selectedCorePairsIfNeutral ≡ 80
nickelHasEightyHypotheticalCorePairs = refl

record MolecularRHFAdmission : Set₁ where
  field
    SourceGeometry : Set
    MolecularOrbitals : Set
    ElectronicIntegrals : Set

    originalGeometry : SourceGeometry
    chosenOrbitalFrame : MolecularOrbitals
    derivedIntegrals : ElectronicIntegrals

    geometryIsNickel41Source : SourceGeometry → Set
    orbitalsMatchSelectedGeometry :
      SourceGeometry → MolecularOrbitals → Set
    integralsMatchSelectedOrbitals :
      MolecularOrbitals → ElectronicIntegrals → Set

    originalGeometryAdmitted :
      geometryIsNickel41Source originalGeometry
    originalFrameAdmitted :
      orbitalsMatchSelectedGeometry originalGeometry chosenOrbitalFrame
    originalIntegralIdentityAdmitted :
      integralsMatchSelectedOrbitals chosenOrbitalFrame derivedIntegrals

-- A correctly admitted source chain retains the original orbital/integral
-- identity; neither a radial HF convergence receipt nor a 3/6/9
-- representation supplies these physical admissions.
molecularRHFNeedsMatchingOrbitalFrame :
  (A : MolecularRHFAdmission) →
  MolecularRHFAdmission.orbitalsMatchSelectedGeometry A
    (MolecularRHFAdmission.originalGeometry A)
    (MolecularRHFAdmission.chosenOrbitalFrame A)
molecularRHFNeedsMatchingOrbitalFrame A =
  MolecularRHFAdmission.originalFrameAdmitted A

molecularRHFNeedsMatchingIntegralFrame :
  (A : MolecularRHFAdmission) →
  MolecularRHFAdmission.integralsMatchSelectedOrbitals A
    (MolecularRHFAdmission.chosenOrbitalFrame A)
    (MolecularRHFAdmission.derivedIntegrals A)
molecularRHFNeedsMatchingIntegralFrame A =
  MolecularRHFAdmission.originalIntegralIdentityAdmitted A
