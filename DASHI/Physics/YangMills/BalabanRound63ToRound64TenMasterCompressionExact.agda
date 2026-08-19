module DASHI.Physics.YangMills.BalabanRound63ToRound64TenMasterCompressionExact where

------------------------------------------------------------------------
-- ROUND63 -> ROUND64 FRONTIER COMPRESSION
--
-- This is the executable backwards-facing proof of the reclassification.
-- Round63 had thirteen SU(2)-shaped physical leaves.  Round64 does NOT claim
-- those thirteen witnesses magically prove the literal Clay problem.  Instead
-- it records the exact functions required to compress implementation-shaped
-- leaves into stronger master propositions, and requires the two Clay-facing
-- obligations that Round63 omitted entirely:
--
--   M7  local operators / OPE / stress tensor / T00=H,
--   M10 every compact simple gauge group.
--
-- Given those compression functions and the two new witnesses, the old
-- physical witness package constructs the ten-master witness package exactly.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2ClayBackwardsCompilerExact as Old
import DASHI.Physics.YangMills.YangMillsClayTenMasterBackwardsCompilerExact as New

record Round63ToTenMasterCompression
    (oldTypes : Old.SU2PhysicalProducerTypes)
    (newTypes : New.TenMasterProducerTypes) : Set₁ where
  field
    -- A1+A2 -> M1: prove the signed whole residual rather than forcing a split.
    compressG2 :
      Old.G2CorrelatedDegreeOneBound oldTypes →
      Old.G2RawHigherDegreeBound oldTypes →
      New.SignedSelectedRegionG2Absorption newTypes

    -- B1 -> M2.
    compressOneLoop :
      Old.LiteralOneLoopCoefficientPositive oldTypes →
      New.LiteralWilsonGhostHaarOneLoopCoefficient newTypes

    -- C1 -> M3.
    compressRG :
      Old.PhysicalQuarticRemainderUniform oldTypes →
      New.UniformNonlinearOneStepRGStability newTypes

    -- D1+D2 -> M4: literal full transfer intertwiner.
    compressTransfer :
      Old.LiteralWilsonKernelNaturality oldTypes →
      Old.LiteralTemporalTraceNaturality oldTypes →
      New.LiteralOSCompatibleTransferNaturality newTypes

    -- E1+E2 -> M5: one common physical-unit floor.
    compressGap :
      Old.TerminalPhysicalWilsonTransferGap oldTypes →
      Old.CutoffUniformPhysicalFeshbachLossBudget oldTypes →
      New.CutoffUniformPhysicalTransferGap newTypes

    -- F1+F2+F3 -> M6: one sufficiently strong convergence theorem.
    compressContinuum :
      Old.PhysicalRenormalizedSchwingerScaleIncrementUniform oldTypes →
      Old.RenormalizedYangMillsSchwingerTightness oldTypes →
      Old.YangMillsContinuumOSUniqueLimit oldTypes →
      New.StrongContinuumSchwingerConvergence newTypes

    -- G1 -> M8; G2 -> M9.
    compressNonGaussian :
      Old.PhysicalContinuumFourthCumulantLowerBound oldTypes →
      New.SameLimitFourthCumulantLowerBound newTypes

    compressClustering :
      Old.PhysicalUniformExponentialClustering oldTypes →
      New.SameLimitPhysicalExponentialClustering newTypes

    -- Genuine omissions from Round63, not compressions.
    localOperatorOPEStressTensor :
      New.ContinuumLocalOperatorOPEStressTensor newTypes

    compactSimpleGroupUniformization :
      New.CompactSimpleGroupUniformization newTypes

open Round63ToTenMasterCompression public

round63WitnessesPlusLiteralMissingObligationsGiveTenMasters :
  ∀ {oldTypes newTypes} →
  Round63ToTenMasterCompression oldTypes newTypes →
  Old.SU2PhysicalProducers oldTypes →
  New.TenMasterProducers newTypes
round63WitnessesPlusLiteralMissingObligationsGiveTenMasters compression old = record
  { New.TenMasterProducers.signedSelectedRegionG2Absorption =
      compressG2 compression
        (Old.g2CorrelatedDegreeOneBound old)
        (Old.g2RawHigherDegreeBound old)
  ; New.TenMasterProducers.literalWilsonGhostHaarOneLoopCoefficient =
      compressOneLoop compression
        (Old.literalOneLoopCoefficientPositive old)
  ; New.TenMasterProducers.uniformNonlinearOneStepRGStability =
      compressRG compression
        (Old.physicalQuarticRemainderUniform old)
  ; New.TenMasterProducers.literalOSCompatibleTransferNaturality =
      compressTransfer compression
        (Old.literalWilsonKernelNaturality old)
        (Old.literalTemporalTraceNaturality old)
  ; New.TenMasterProducers.cutoffUniformPhysicalTransferGap =
      compressGap compression
        (Old.terminalPhysicalWilsonTransferGap old)
        (Old.cutoffUniformPhysicalFeshbachLossBudget old)
  ; New.TenMasterProducers.strongContinuumSchwingerConvergence =
      compressContinuum compression
        (Old.physicalRenormalizedSchwingerScaleIncrementUniform old)
        (Old.renormalizedYangMillsSchwingerTightness old)
        (Old.yangMillsContinuumOSUniqueLimit old)
  ; New.TenMasterProducers.continuumLocalOperatorOPEStressTensor =
      localOperatorOPEStressTensor compression
  ; New.TenMasterProducers.sameLimitFourthCumulantLowerBound =
      compressNonGaussian compression
        (Old.physicalContinuumFourthCumulantLowerBound old)
  ; New.TenMasterProducers.sameLimitPhysicalExponentialClustering =
      compressClustering compression
        (Old.physicalUniformExponentialClustering old)
  ; New.TenMasterProducers.compactSimpleGroupUniformization =
      compactSimpleGroupUniformization compression
  }

round63ToTenMasterCompressionCompilerLevel : ProofLevel
round63ToTenMasterCompressionCompilerLevel = machineChecked

-- The compression record is intentionally not given a canonical inhabitant:
-- constructing each function on the literal carriers is the mathematical work.
-- In particular, M7 and M10 cannot be manufactured from the old SU(2) fields.
round64LiteralCompressionInstantiationLevel : ProofLevel
round64LiteralCompressionInstantiationLevel = conditional
