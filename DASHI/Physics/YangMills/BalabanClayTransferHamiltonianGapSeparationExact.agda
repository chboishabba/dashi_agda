module DASHI.Physics.YangMills.BalabanClayTransferHamiltonianGapSeparationExact where

------------------------------------------------------------------------
-- SOURCE AUDIT
--
-- Mir Faizal and Arshid Shabir,
-- "Reflection-positive renormalization and the persistence of the mass gap
-- in lattice SU(N) Yang-Mills: Part (2)", International Journal of Geometric
-- Methods in Modern Physics 23 (2026).
-- DOI: 10.1142/S0219887826501136.
--
-- A dimensionless transfer contraction 1-lambda_2 and the Hamiltonian energy
-- -a^{-1} log(lambda_2) are different quantities.  They may be related only
-- through an explicit spacing-dependent conversion theorem.  This module
-- makes accidental reuse impossible at the type level and proves the exact
-- transport once the conversion bridge is supplied.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

record TransferHamiltonianGapData
    (Scale Eigenvalue TransferGap HamiltonianGap : Set) : Set₁ where
  field
    transferGapFromEigenvalue : Eigenvalue → TransferGap
    hamiltonianGapFromScaleAndEigenvalue :
      Scale → Eigenvalue → HamiltonianGap

    PositiveTransferGap : TransferGap → Set
    PositiveHamiltonianGap : HamiltonianGap → Set

    transferToHamiltonianPositivity : ∀ scale eigenvalue →
      PositiveTransferGap (transferGapFromEigenvalue eigenvalue) →
      PositiveHamiltonianGap
        (hamiltonianGapFromScaleAndEigenvalue scale eigenvalue)

open TransferHamiltonianGapData public

positiveTransferGapRequiresExplicitPhysicalConversion :
  ∀ {Scale Eigenvalue TransferGap HamiltonianGap}
    (dataSet : TransferHamiltonianGapData
      Scale Eigenvalue TransferGap HamiltonianGap)
    scale eigenvalue →
  PositiveTransferGap dataSet
    (transferGapFromEigenvalue dataSet eigenvalue) →
  PositiveHamiltonianGap dataSet
    (hamiltonianGapFromScaleAndEigenvalue dataSet scale eigenvalue)
positiveTransferGapRequiresExplicitPhysicalConversion
    dataSet scale eigenvalue transferPositive =
  transferToHamiltonianPositivity dataSet scale eigenvalue transferPositive

record UniformPhysicalGapConversion
    (Cutoff Eigenvalue TransferGap HamiltonianGap : Set) : Set₁ where
  field
    scale : Cutoff → Cutoff
    eigenvalue : Cutoff → Eigenvalue
    dataSet :
      TransferHamiltonianGapData Cutoff Eigenvalue TransferGap HamiltonianGap
    transferPositiveAtEveryCutoff : ∀ cutoff →
      PositiveTransferGap dataSet
        (transferGapFromEigenvalue dataSet (eigenvalue cutoff))

open UniformPhysicalGapConversion public

hamiltonianGapPositiveAtEveryCutoff :
  ∀ {Cutoff Eigenvalue TransferGap HamiltonianGap}
    (conversion : UniformPhysicalGapConversion
      Cutoff Eigenvalue TransferGap HamiltonianGap)
    cutoff →
  PositiveHamiltonianGap (dataSet conversion)
    (hamiltonianGapFromScaleAndEigenvalue (dataSet conversion)
      (scale conversion cutoff) (eigenvalue conversion cutoff))
hamiltonianGapPositiveAtEveryCutoff conversion cutoff =
  positiveTransferGapRequiresExplicitPhysicalConversion
    (dataSet conversion)
    (scale conversion cutoff)
    (eigenvalue conversion cutoff)
    (transferPositiveAtEveryCutoff conversion cutoff)

transferHamiltonianGapTypeSeparationLevel : ProofLevel
transferHamiltonianGapTypeSeparationLevel = machineChecked

physicalGapConversionInputsLevel : ProofLevel
physicalGapConversionInputsLevel = conditional
