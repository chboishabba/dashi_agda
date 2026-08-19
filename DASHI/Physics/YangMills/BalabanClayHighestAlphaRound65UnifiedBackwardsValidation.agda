module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound65UnifiedBackwardsValidation where

------------------------------------------------------------------------
-- ROUND65 FOCUSED ROOT
--
-- Seven programmes are the honest current backwards cutset.  Four packages are
-- possible only if one unified polymer/Schwinger theorem closes continuum
-- existence + local/composite fields + interaction survival + physical
-- clustering on the same family.  Generic 4D UV RG stability is already
-- source-owned by Bałaban CMP119/CMP122; signed G2 is reduced to five exact
-- degree blocks; beta_0 follows from the literal singular scalar coefficient;
-- and compact-simple promotion is reduced to one group-parametric continuation
-- theorem over the existing quantitative Lie package.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClaySevenProgrammeBackwardsCompilerExact as Seven
import DASHI.Physics.YangMills.YangMillsClayFourPackageBackwardsCompilerExact as Four
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact as Unified
import DASHI.Physics.YangMills.BalabanPublishedUVStabilityNonlinearRGCoreExact as UV
import DASHI.Physics.YangMills.BalabanSelectedRegionFiveBlockSignedG2Exact as G2
import DASHI.Physics.YangMills.BalabanSU2OneLoopInfraredCoefficientFromLiteralScalarExact as OneLoop
import DASHI.Physics.YangMills.BalabanLiteralTransferNaturalityMasterExact as Transfer
import DASHI.Physics.YangMills.BalabanCutoffUniformPhysicalTransferGapMasterExact as Gap
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.YangMillsCompactSimpleParametricPromotionReductionExact as Groups

round65HonestProgrammeCountExact : Seven.sevenProgrammeCount ≡ 7
round65HonestProgrammeCountExact = Seven.sevenProgrammeCountExact

round65ConditionalFourPackageCountExact : Four.fourPackageCount ≡ 4
round65ConditionalFourPackageCountExact = Four.fourPackageCountExact

round65BackwardsCompilerLevel : ProofLevel
round65BackwardsCompilerLevel = machineChecked

round65UnifiedProjectionTheoremsLevel : ProofLevel
round65UnifiedProjectionTheoremsLevel = Unified.unifiedNormProjectionClosureLevel

round65PublishedUVCoreLevel : ProofLevel
round65PublishedUVCoreLevel = UV.publishedFourDimensionalNonlinearRGCoreLevel

round65FiveBlockG2CompilerLevel : ProofLevel
round65FiveBlockG2CompilerLevel = G2.fiveBlockSignedG2CompilerLevel

round65LiteralBetaCoefficientCompilerLevel : ProofLevel
round65LiteralBetaCoefficientCompilerLevel =
  OneLoop.literalScalarReductionToUniversalBetaCoefficientLevel

round65CompactSimpleClassificationPromotionLevel : ProofLevel
round65CompactSimpleClassificationPromotionLevel =
  Groups.compactSimpleClassificationToParametricFamilyLevel

-- Remaining physical research seams.
round65PhysicalFiveBlockG2Level : ProofLevel
round65PhysicalFiveBlockG2Level = G2.physicalFiveBlockSignedG2Level

round65LiteralWilsonGhostHaarScalarReductionLevel : ProofLevel
round65LiteralWilsonGhostHaarScalarReductionLevel =
  OneLoop.literalWilsonGhostHaarWardScalarReductionLevel

round65LiteralRegularMatchingRemainderLevel : ProofLevel
round65LiteralRegularMatchingRemainderLevel =
  OneLoop.literalFourOrbitRegularMatchingRemainderLevel

round65LiteralPhysicalStateToPublishedRGCarrierLevel : ProofLevel
round65LiteralPhysicalStateToPublishedRGCarrierLevel =
  UV.literalPhysicalStateToPublishedRGCarrierLevel

round65UnifiedPhysicalPolymerNormLevel : ProofLevel
round65UnifiedPhysicalPolymerNormLevel =
  Unified.physicalYMUnifiedPolymerNormProducerLevel

round65LiteralTransferLevel : ProofLevel
round65LiteralTransferLevel = Transfer.physicalLiteralOSCompatibleTransferNaturalityLevel

round65CutoffUniformPhysicalGapLevel : ProofLevel
round65CutoffUniformPhysicalGapLevel = Gap.physicalCutoffUniformTransferGapLevel

round65LocalOPEStressLevel : ProofLevel
round65LocalOPEStressLevel = Local.physicalContinuumLocalOperatorOPEStressTensorLevel

round65CompactSimpleParametricContinuationLevel : ProofLevel
round65CompactSimpleParametricContinuationLevel =
  Groups.compactSimpleParametricYMContinuationLevel

-- Fourth-cumulant -> non-Gaussian and OS clustering -> Hamiltonian gap remain
-- downstream theorem closures and are not reintroduced as algebraic producers.
round65FourthCumulantToNonGaussianLevel : ProofLevel
round65FourthCumulantToNonGaussianLevel = machineChecked

round65OSClusteringToHamiltonianGapLevel : ProofLevel
round65OSClusteringToHamiltonianGapLevel = machineChecked

-- Seven is authoritative today. Four becomes authoritative only after an
-- actual physical UnifiedContinuumRGCompletion is constructed.
round65SevenProgrammePhysicalInstantiationLevel : ProofLevel
round65SevenProgrammePhysicalInstantiationLevel = conditional

round65FourPackageCollapseLevel : ProofLevel
round65FourPackageCollapseLevel = Four.fourPackagePhysicalCollapseLevel
