{-# OPTIONS --safe #-}
module DASHI.Unified.YMCMP119ResidualWeldTOEExact where

------------------------------------------------------------------------
-- YANG-MILLS CMP119 LITERAL RESIDUAL-WELD TOE NORMALIZATION
--
-- O. Objective.
-- Route the strongest existing CMP119 E/R/B/V residual-weld audit into the
-- DASHI TOE graph.
--
-- R. Reuse.
-- BalabanCMP119LiteralResidualWeldMaxCut20261002Exact is the canonical owner.
-- It already reuses the regular-E, R-operation, boundary, vacuum, and
-- periodic-polymer reflection owners.
--
-- C. Construction.
-- Export aliases only.
-- Keep theorem-bearing donors separate from conditional same-object leaves.
--
-- S. Scope.
-- Do not infer a physical component support dictionary.
-- Do not infer a crossing-kernel RP theorem.
-- Do not identify a finite shell tail with the source residual without the
-- explicit source/evaluator weld.
--
-- L. Lineage.
-- Bałaban source attribution remains in the imported owners.
-- DASHI owns this import edge only.
-- No ESD or digital-ESD implementation surface is edited.
--
-- P. Postcondition.
-- TOE consumers can see exactly which E/R/B/V reflection and dyadic donors are
-- available and exactly which source dictionaries remain conditional.
--
-- G. Governance.
-- Reuse first.
-- Keep ProofLevel values unchanged.
-- Fail closed on continuum and Clay promotion in the canonical R559 owner.
--
-- F. Verification.
-- Preflight and Agda must accept this module and the TOE root.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)

import DASHI.Physics.YangMills.BalabanCMP119LiteralResidualWeldMaxCut20261002Exact as Weld
import DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Exact as YMTOE

------------------------------------------------------------------------
-- Existing theorem-bearing donors.
------------------------------------------------------------------------

toeResidualWeldCompilerLevel : ProofLevel
toeResidualWeldCompilerLevel =
  Weld.literalResidualWeldCompilerLevel

toeRegularELocalizedCompositeDonorLevel : ProofLevel
toeRegularELocalizedCompositeDonorLevel =
  Weld.regularELocalizedCompositeDonorLevel

toeROperationDyadicShellDonorLevel : ProofLevel
toeROperationDyadicShellDonorLevel =
  Weld.rOperationDyadicShellDonorLevel

toeVacuumConstantCarrierDonorLevel : ProofLevel
toeVacuumConstantCarrierDonorLevel =
  Weld.vacuumConstantCarrierDonorLevel

toeReflectionPolymerGeometryDonorLevel : ProofLevel
toeReflectionPolymerGeometryDonorLevel =
  Weld.reflectionPolymerGeometryDonorLevel

toeRegularEReflectionSupportClassifierLevel : ProofLevel
toeRegularEReflectionSupportClassifierLevel =
  Weld.regularEReflectionSupportDonorLevel

toeBoundaryReflectionSupportClassifierLevel : ProofLevel
toeBoundaryReflectionSupportClassifierLevel =
  Weld.boundaryReflectionSupportDonorLevel

toeROperationReflectionSupportClassifierLevel : ProofLevel
toeROperationReflectionSupportClassifierLevel =
  Weld.rOperationReflectionSupportDonorLevel

------------------------------------------------------------------------
-- Exact source/same-object leaves.
------------------------------------------------------------------------

toeCommonActionEvaluatorAdditiveSemanticsLevel : ProofLevel
toeCommonActionEvaluatorAdditiveSemanticsLevel =
  Weld.commonActionEvaluatorAdditiveSemanticsLevel

toeRegularESelectedCarrierInstantiationLevel : ProofLevel
toeRegularESelectedCarrierInstantiationLevel =
  Weld.regularESelectedCarrierInstantiationLevel

toeRegularEComponentPeriodicSupportDictionaryLevel : ProofLevel
toeRegularEComponentPeriodicSupportDictionaryLevel =
  Weld.regularEComponentToPeriodicPolymerSupportLevel

toeRegularEOneSidedActivityReflectionLevel : ProofLevel
toeRegularEOneSidedActivityReflectionLevel =
  Weld.ESupport.cmp119RegularEOneSidedActivityReflectionLevel

toeRegularECrossingKernelRPLevel : ProofLevel
toeRegularECrossingKernelRPLevel =
  Weld.ESupport.cmp119RegularECrossingKernelRPLevel

toeROperationPublishedPolymerDictionaryLevel : ProofLevel
toeROperationPublishedPolymerDictionaryLevel =
  Weld.rOperationPublishedPolymerDictionaryLevel

toeROperationWeightSplitAndRootedEntropyLevel : ProofLevel
toeROperationWeightSplitAndRootedEntropyLevel =
  Weld.rOperationWeightSplitAndRootedEntropyLevel

toeBoundaryPublishedPolymerDictionaryLevel : ProofLevel
toeBoundaryPublishedPolymerDictionaryLevel =
  Weld.boundaryPublishedPolymerDictionaryLevel

toeBoundaryLocalizedTermsToSelectedShellsLevel : ProofLevel
toeBoundaryLocalizedTermsToSelectedShellsLevel =
  Weld.boundaryLocalizedTermsToSelectedShellsLevel

toeVacuumEvaluatorIsSourceConstantLevel : ProofLevel
toeVacuumEvaluatorIsSourceConstantLevel =
  Weld.vacuumEvaluatorIsSourceConstantLevel

toeCommonERBPeriodicSupportToSelectedShellCarrierLevel : ProofLevel
toeCommonERBPeriodicSupportToSelectedShellCarrierLevel =
  Weld.commonERBPeriodicSupportToSelectedShellCarrierLevel

toeFullResidualEqualsSelectedFiniteShellTailLevel : ProofLevel
toeFullResidualEqualsSelectedFiniteShellTailLevel =
  Weld.fullResidualEqualsSelectedFiniteShellTailLevel

------------------------------------------------------------------------
-- Terminal fail-closed reuse.
------------------------------------------------------------------------

toeResidualWeldDoesNotPromoteContinuum :
  YMTOE.toeFlat4DContinuumTransferProvedHere
    ≡ Agda.Builtin.Bool.false
toeResidualWeldDoesNotPromoteContinuum =
  YMTOE.toeFlat4DContinuumTransferProvedHereIsFalse

toeResidualWeldDoesNotPromoteClay :
  YMTOE.toeClayYangMillsPromoted
    ≡ Agda.Builtin.Bool.false
toeResidualWeldDoesNotPromoteClay =
  YMTOE.toeClayYangMillsPromotedIsFalse
