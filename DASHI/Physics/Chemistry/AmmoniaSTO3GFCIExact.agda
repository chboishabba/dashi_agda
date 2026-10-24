module DASHI.Physics.Chemistry.AmmoniaSTO3GFCIExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- DECLARED-MODEL NUMERICAL HAMILTONIAN PAYMENT
--
-- This is deliberately model-chemistry scoped: STO-3G at the fixed equilibrium
-- geometry used by Yoffe et al.  The reported FCI eigenvalue pays numerical
-- diagonalization for that finite Hamiltonian, not the exact continuum NH3
-- molecule and not the literal eigenvector coefficients in this repository.
------------------------------------------------------------------------

yoffeEtAlVQSCI : Source.AttributedSource
yoffeEtAlVQSCI =
  Source.mkDOISource
    "Daniel Yoffe; Noga Entin; Amir Natan; Adi Makmal"
    "A qubit-efficient variational selected configuration-interaction method"
    "Quantum Science and Technology 10 (2025) 015020; published online 2024"
    "2024"
    "10.1088/2058-9565/ad7d32"
    "https://doi.org/10.1088/2058-9565/ad7d32"
    Source.academicArticleSource
    "primary authority for the declared NH3 STO-3G electronic-structure benchmark: 10 electrons, 16 spin-orbitals, HF energy -55.4554 Ha and classically diagonalized FCI energy -55.5245 Ha; not authority for an exact continuum molecular Hamiltonian"
    Source.publicAttribution

record NH3STO3GFCIReceipt : Set where
  constructor nh3STO3GFCIReceipt
  field
    molecule : String
    basis : String
    electrons : Nat
    spinOrbitals : Nat
    energySign : String
    hfEnergyTenThousandthHartree : Nat
    fciEnergyTenThousandthHartree : Nat
    source : Source.AttributedSource
    hfMethod : String
    fciMethod : String
    geometryScope : String

open NH3STO3GFCIReceipt public

canonicalNH3STO3GFCIReceipt : NH3STO3GFCIReceipt
canonicalNH3STO3GFCIReceipt =
  nh3STO3GFCIReceipt
    "NH3"
    "STO-3G"
    10
    16
    "both stored magnitudes are negative Hartree energies"
    554554
    555245
    yoffeEtAlVQSCI
    "restricted Hartree-Fock benchmark"
    "classical full configuration-interaction matrix diagonalization using Psi4-generated molecular data"
    "fixed equilibrium geometry used by the cited study"

correlationEnergyMagnitudeTenThousandthHartree : Nat
correlationEnergyMagnitudeTenThousandthHartree = 691

record STO3GFCIBoundary : Set where
  constructor sto3GFCIBoundary
  field
    sourceBackedFiniteHamiltonianModelPaid : Bool
    sourceBackedFiniteHamiltonianModelPaidIsTrue :
      sourceBackedFiniteHamiltonianModelPaid ≡ true
    sourceBackedFCIDiagonalizationPaid : Bool
    sourceBackedFCIDiagonalizationPaidIsTrue :
      sourceBackedFCIDiagonalizationPaid ≡ true
    sourceBackedHFEnergyPaid : Bool
    sourceBackedHFEnergyPaidIsTrue : sourceBackedHFEnergyPaid ≡ true
    literalFCIMatrixImported : Bool
    literalFCIMatrixImportedIsFalse : literalFCIMatrixImported ≡ false
    literalFCIEigenvectorCoefficientsImported : Bool
    literalFCIEigenvectorCoefficientsImportedIsFalse :
      literalFCIEigenvectorCoefficientsImported ≡ false
    sto3gFCIEqualsExactPhysicalGroundState : Bool
    sto3gFCIEqualsExactPhysicalGroundStateIsFalse :
      sto3gFCIEqualsExactPhysicalGroundState ≡ false
    sourceEigenvalueCreatesDASHIProofOfEigenvector : Bool
    sourceEigenvalueCreatesDASHIProofOfEigenvectorIsFalse :
      sourceEigenvalueCreatesDASHIProofOfEigenvector ≡ false

open STO3GFCIBoundary public

canonicalSTO3GFCIBoundary : STO3GFCIBoundary
canonicalSTO3GFCIBoundary =
  sto3GFCIBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
