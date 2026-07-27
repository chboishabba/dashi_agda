module DASHI.Physics.YangMills.BalabanClayLiteralFrontierCompletionLedger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT3LiteralPhysicalCoercivityProducerExact as T3
import DASHI.Physics.YangMills.BalabanClayT2LiteralWilsonSixFactorProducerExact as T2Activity
import DASHI.Physics.YangMills.BalabanClayT2LiteralEightWayCliqueExact as T2Clique
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as T5
import DASHI.Physics.YangMills.BalabanClayBranchHeadReceiptSurface as Receipt

------------------------------------------------------------------------
-- Locally derived finite/reduction theorems.
------------------------------------------------------------------------

literalReferenceHodgeProducerLevel : ProofLevel
literalReferenceHodgeProducerLevel = T3.literalReferenceHodgeProducerLevel

literalPatchTransferProducerLevel : ProofLevel
literalPatchTransferProducerLevel = T3.literalPatchTransferProducerLevel

fiveTermRelativeHessianCombinationLevel : ProofLevel
fiveTermRelativeHessianCombinationLevel = T3.fiveTermRelativeHessianCombinationLevel

literalBadTraversalActionReductionLevel : ProofLevel
literalBadTraversalActionReductionLevel = T2Activity.literalBadTraversalWitnessProducerLevel

literalSixFactorCombinationLevel : ProofLevel
literalSixFactorCombinationLevel = T2Activity.literalSixFactorCombinationLevel

literalEightWayCliqueGeometryLevel : ProofLevel
literalEightWayCliqueGeometryLevel = T2Clique.literalEightWayCliqueGeometryLevel

localizedPlaquetteProjectionReductionLevel : ProofLevel
localizedPlaquetteProjectionReductionLevel = T4.localizedPlaquetteProjectorLevel

finiteGramEntrywiseToQuadraticConvergenceLevel : ProofLevel
finiteGramEntrywiseToQuadraticConvergenceLevel =
  T5.finiteGramEntrywiseToQuadraticConvergenceLevel

------------------------------------------------------------------------
-- Literal analytic/model-identification leaves.  These remain conditional
-- until an inhabitant of the corresponding explicit data record is supplied.
------------------------------------------------------------------------

literalFiveComponentEstimateInputsLevel : ProofLevel
literalFiveComponentEstimateInputsLevel = T3.literalFiveComponentEstimateInputsLevel

literalWilsonSixFactorAnalyticInputsLevel : ProofLevel
literalWilsonSixFactorAnalyticInputsLevel =
  T2Activity.literalSixComponentAnalyticInputsLevel

physicalPolymerExtensionIdentificationLevel : ProofLevel
physicalPolymerExtensionIdentificationLevel =
  T2Clique.physicalPolymerExtensionIdentificationLevel

literalVacuumPolarizationIntegralInputsLevel : ProofLevel
literalVacuumPolarizationIntegralInputsLevel =
  T4.literalVacuumPolarizationIntegralInputsLevel

physicalExpectationConvergenceInputsLevel : ProofLevel
physicalExpectationConvergenceInputsLevel =
  T5.physicalExpectationConvergenceInputsLevel

cleanAgda29BranchHeadReceiptLevel : ProofLevel
cleanAgda29BranchHeadReceiptLevel = Receipt.cleanAgda29BranchHeadReceiptLevel
