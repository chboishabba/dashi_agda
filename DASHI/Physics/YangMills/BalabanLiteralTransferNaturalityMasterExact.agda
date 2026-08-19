module DASHI.Physics.YangMills.BalabanLiteralTransferNaturalityMasterExact where

------------------------------------------------------------------------
-- ROUND64 MASTER THEOREM 4: LITERAL OS-COMPATIBLE TRANSFER NATURALITY
--
-- PRIMARY SOURCES
--
-- Martin Lüscher,
-- "Construction of a Selfadjoint, Strictly Positive Transfer Matrix for
-- Euclidean Lattice Gauge Theories", Communications in Mathematical Physics
-- 54 (1977), 283--292. DOI: 10.1007/BF01614090.
--
-- Konrad Osterwalder and Erhard Seiler,
-- "Gauge Field Theories on a Lattice", Annals of Physics 110 (1978),
-- 440--471. DOI: 10.1016/0003-4916(78)90039-8.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- DASHI CONTRIBUTION
--
-- Round63 exposed kernel naturality and temporal trace/integration naturality
-- as two physical leaves.  They are a useful sufficient decomposition, but the
-- theorem consumed by the spectral/RG continuation is the ONE physical square
--
--   B (T_coarse f) = T_fine (B f).
--
-- This file makes the full TransferIntertwiner the master producer and proves
-- that the existing two-square KernelTraceNaturality package constructs it.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanWilsonTransferIntertwinerExact as Transfer
import DASHI.Physics.YangMills.BalabanTransferKernelTraceNaturalityExact as KernelTrace

record LiteralOSCompatibleTransferNaturality
    (Fine Coarse : Set) : Set₁ where
  field
    physicalIntertwiner : Transfer.TransferIntertwiner Fine Coarse

open LiteralOSCompatibleTransferNaturality public

literalIntertwiningEquation :
  ∀ {Fine Coarse}
    (master : LiteralOSCompatibleTransferNaturality Fine Coarse)
    coarse →
  Transfer.liftObservable (physicalIntertwiner master)
    (Transfer.coarseTransfer (physicalIntertwiner master) coarse)
  ≡ Transfer.fineTransfer (physicalIntertwiner master)
      (Transfer.liftObservable (physicalIntertwiner master) coarse)
literalIntertwiningEquation master =
  Transfer.intertwines (physicalIntertwiner master)

masterFromKernelTraceNaturality :
  ∀ {Fine Coarse FineKernel CoarseKernel} →
  KernelTrace.TransferKernelTraceNaturality
    Fine Coarse FineKernel CoarseKernel →
  LiteralOSCompatibleTransferNaturality Fine Coarse
masterFromKernelTraceNaturality naturality = record
  { physicalIntertwiner =
      KernelTrace.kernelTraceNaturalityImpliesTransferIntertwiner naturality
  }

literalTransferMasterCompilerLevel : ProofLevel
literalTransferMasterCompilerLevel = machineChecked

-- Remaining physical theorem: instantiate this master on the literal Bałaban
-- block transformation and Wilson/Lüscher transfer carriers.  Kernel and trace
-- naturality remain one available proof decomposition, not two endgame leaves.
physicalLiteralOSCompatibleTransferNaturalityLevel : ProofLevel
physicalLiteralOSCompatibleTransferNaturalityLevel = conditional
