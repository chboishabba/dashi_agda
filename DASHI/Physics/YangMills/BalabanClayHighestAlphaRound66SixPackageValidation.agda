module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound66SixPackageValidation where

------------------------------------------------------------------------
-- ROUND66 FOCUSED ROOT
--
-- Round66 starts from the six-package / eleven-leaf diagnostic and removes
-- consequences that are not genuinely new Yang--Mills analysis.
--
--   diagnostic leaves:          11
--   genuinely physical leaves:  10
--   theorem packages:             6
--
-- The reduction 11 -> 10 is transfer-gap -> observable clustering: once the
-- literal centered observable is on the SAME transfer Hilbert carrier and the
-- common vacuum-orthogonal semigroup decay is identified, Cauchy--Schwarz gives
-- the connected-correlation bound.
--
-- Further high-alpha reductions in this root:
--
-- * a common mass floor is derived from terminalFloor - lossCeiling;
-- * d=4 small-polymer extraction is finite (<=8 blocks) with four exact Taylor
--   channels, while the large-polymer branch has an explicit 1/32 target;
-- * Step-V/KP 1/2 + 1/32 = 17/32 leaves 15/32 contraction headroom;
-- * the recurrence K_(n+1)<=17/32 K_n+E 2^-n has exact all-depth convolution
--   32 ((17/32)^n-(1/2)^n), so iteration is no longer physical input;
-- * composite-operator all-depth RG transport follows from one-step protection;
-- * the literal one-loop evaluator is definitionally the object folded into
--   the four joint hypercubic orbit sums.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClaySixPackageElevenLeafBackwardsCompilerExact as Eleven
import DASHI.Physics.YangMills.YangMillsClaySixPackageTenPhysicalLeafBackwardsCompilerExact as Ten
import DASHI.Physics.YangMills.BalabanTransferGapToObservableClusteringExact as GapCluster
import DASHI.Physics.YangMills.BalabanUniformTerminalMinusLossGapExact as GapBudget
import DASHI.Physics.YangMills.BalabanCorrectedSmallPolymerExtractionContractionExact as Extract
import DASHI.Physics.YangMills.BalabanSmallPolymerTaylorNormalizationExact as Taylor
import DASHI.Physics.YangMills.BalabanUnifiedPolymerStepVContractionBudgetExact as StepBudget
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondIterationExact as Iteration
import DASHI.Physics.YangMills.BalabanCompositeOperatorRGParallelTransportExact as Composite
import DASHI.Physics.YangMills.BalabanLiteralOneLoopFourOrbitSameObjectExact as OneLoop
import DASHI.Physics.YangMills.BalabanSelectedRegionFiveBlockSignedG2Exact as G2
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact as Unified
import DASHI.Physics.YangMills.YangMillsCompactSimpleParametricPromotionReductionExact as Groups

round66DiagnosticElevenLeafCountExact : Eleven.elevenLeafCount ≡ 11
round66DiagnosticElevenLeafCountExact = Eleven.elevenLeafCountExact

round66PhysicalTenLeafCountExact : Ten.tenPhysicalLeafCount ≡ 10
round66PhysicalTenLeafCountExact = Ten.tenPhysicalLeafCountExact

round66SixPackageCountExact : Ten.sixPackageCount ≡ 6
round66SixPackageCountExact = Ten.sixPackageCountExact

round66TransferGapToClusteringCompilerLevel : ProofLevel
round66TransferGapToClusteringCompilerLevel =
  GapCluster.transferGapToObservableClusteringCompilerLevel

round66TerminalMinusLossGapCompilerLevel : ProofLevel
round66TerminalMinusLossGapCompilerLevel =
  GapBudget.terminalMinusLossGapCompilerLevel

round66SmallLargeExtractionCompilerLevel : ProofLevel
round66SmallLargeExtractionCompilerLevel =
  Extract.correctedSmallLargeExtractionCompilerLevel

round66TaylorNormalizationLevel : ProofLevel
round66TaylorNormalizationLevel =
  Taylor.smallPolymerFourChannelExtractionAlgebraLevel

round66StepVContractionBudgetLevel : ProofLevel
round66StepVContractionBudgetLevel =
  StepBudget.stepVContractionBudgetArithmeticLevel

round66AllDepthIterationLevel : ProofLevel
round66AllDepthIterationLevel =
  Iteration.seventeenThirtySecondIterationAlgebraLevel

round66CompositeParallelTransportLevel : ProofLevel
round66CompositeParallelTransportLevel =
  Composite.protectedCompositeAllDepthTransportLevel

round66LiteralOneLoopOrbitFoldLevel : ProofLevel
round66LiteralOneLoopOrbitFoldLevel =
  OneLoop.literalOneLoopSameObjectOrbitFoldLevel

round66FiveBlockG2CompilerLevel : ProofLevel
round66FiveBlockG2CompilerLevel = G2.fiveBlockSignedG2CompilerLevel

round66UnifiedProjectionClosureLevel : ProofLevel
round66UnifiedProjectionClosureLevel = Unified.unifiedNormProjectionClosureLevel

round66CompactSimpleParametricReductionLevel : ProofLevel
round66CompactSimpleParametricReductionLevel =
  Groups.compactSimpleClassificationToParametricFamilyLevel

------------------------------------------------------------------------
-- Live physical analysis after all Round66 theorem/algebraic reductions.
------------------------------------------------------------------------

round66PhysicalFiveBlockG2Level : ProofLevel
round66PhysicalFiveBlockG2Level = G2.physicalFiveBlockSignedG2Level

round66LiteralWardScalarLevel : ProofLevel
round66LiteralWardScalarLevel = OneLoop.literalWardScalarEvaluatorConstructionLevel

round66FourOrbitRegularRemainderLevel : ProofLevel
round66FourOrbitRegularRemainderLevel = OneLoop.literalFourJointOrbitEnclosureLevel

round66LiteralTransferObservableCarrierLevel : ProofLevel
round66LiteralTransferObservableCarrierLevel =
  GapCluster.literalObservableTransferRepresentationLevel

round66TerminalFloorLevel : ProofLevel
round66TerminalFloorLevel = GapBudget.physicalUniformTerminalFloorLevel

round66TotalLossCeilingLevel : ProofLevel
round66TotalLossCeilingLevel = GapBudget.physicalUniformTotalLossCeilingLevel

round66SmallPolymerPhysicalExtractionLevel : ProofLevel
round66SmallPolymerPhysicalExtractionLevel = Extract.physicalYMSmallPolymerExtractionLevel

round66LargePolymerPhysicalContractionLevel : ProofLevel
round66LargePolymerPhysicalContractionLevel = Extract.physicalYMLargePolymerContractionLevel

round66UnifiedPhysicalStepVBudgetLevel : ProofLevel
round66UnifiedPhysicalStepVBudgetLevel =
  StepBudget.physicalUnifiedStepVContractionBudgetLevel

round66UnifiedPhysicalOneStepRecurrenceLevel : ProofLevel
round66UnifiedPhysicalOneStepRecurrenceLevel =
  Iteration.physicalUnifiedOneStepRecurrenceLevel

round66CompositeMixingLevel : ProofLevel
round66CompositeMixingLevel = Composite.physicalYMCompositeMixingLevel

round66StressWardProtectionLevel : ProofLevel
round66StressWardProtectionLevel = Composite.physicalYMStressWardProtectionLevel

round66PhysicalSixPackageCompletionLevel : ProofLevel
round66PhysicalSixPackageCompletionLevel = conditional
