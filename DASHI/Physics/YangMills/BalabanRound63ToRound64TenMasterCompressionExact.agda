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
    compressG2 :
      Old.G2CorrelatedDegreeOneBound oldTypes →
      Old.G2RawHigherDegreeBound oldTypes →
      New.SignedSelectedRegionG2Absorption newTypes

    compressOneLoop :
      Old.LiteralOneLoopCoefficientPositive oldTypes →
      New.LiteralWilsonGhostHaarOneLoopCoefficient newTypes

    compressRG :
      Old.PhysicalQuarticRemainderUniform oldTypes →
      New.UniformNonlinearOneStepRGStability newTypes

    compressTransfer :
      Old.LiteralWilsonKernelNaturality oldTypes →
      Old.LiteralTemporalTraceNaturality oldTypes →
      New.LiteralOSCompatibleTransferNaturality newTypes

    compressGap :
      Old.TerminalPhysicalWilsonTransferGap oldTypes →
      Old.CutoffUniformPhysicalFeshbachLossBudget oldTypes →
      New.CutoffUniformPhysicalTransferGap newTypes

    compressContinuum :
      Old.PhysicalRenormalizedSchwingerScaleIncrementUniform oldTypes →
      Old.RenormalizedYangMillsSchwingerTightness oldTypes →
      Old.YangMillsContinuumOSUniqueLimit oldTypes →
      New.StrongContinuumSchwingerConvergence newTypes

    compressNonGaussian :
      Old.PhysicalContinuumFourthCumulantLowerBound oldTypes →
      New.SameLimitFourthCumulantLowerBound newTypes

    compressClustering :
      Old.PhysicalUniformExponentialClustering oldTypes →
      New.SameLimitPhysicalExponentialClustering newTypes

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
  { signedSelectedRegionG2Absorption =
      compressG2 compression
        (Old.g2CorrelatedDegreeOneBound old)
        (Old.g2RawHigherDegreeBound old)
  ; literalWilsonGhostHaarOneLoopCoefficient =
      compressOneLoop compression
        (Old.literalOneLoopCoefficientPositive old)
  ; uniformNonlinearOneStepRGStability =
      compressRG compression
        (Old.physicalQuarticRemainderUniform old)
  ; literalOSCompatibleTransferNaturality =
      compressTransfer compression
        (Old.literalWilsonKernelNaturality old)
        (Old.literalTemporalTraceNaturality old)
  ; cutoffUniformPhysicalTransferGap =
      compressGap compression
        (Old.terminalPhysicalWilsonTransferGap old)
        (Old.cutoffUniformPhysicalFeshbachLossBudget old)
  ; strongContinuumSchwingerConvergence =
      compressContinuum compression
        (Old.physicalRenormalizedSchwingerScaleIncrementUniform old)
        (Old.renormalizedYangMillsSchwingerTightness old)
        (Old.yangMillsContinuumOSUniqueLimit old)
  ; continuumLocalOperatorOPEStressTensor =
      localOperatorOPEStressTensor compression
  ; sameLimitFourthCumulantLowerBound =
      compressNonGaussian compression
        (Old.physicalContinuumFourthCumulantLowerBound old)
  ; sameLimitPhysicalExponentialClustering =
      compressClustering compression
        (Old.physicalUniformExponentialClustering old)
  ; compactSimpleGroupUniformization =
      compactSimpleGroupUniformization compression
  }

round63ToTenMasterCompressionCompilerLevel : ProofLevel
round63ToTenMasterCompressionCompilerLevel = machineChecked

round64LiteralCompressionInstantiationLevel : ProofLevel
round64LiteralCompressionInstantiationLevel = conditional
