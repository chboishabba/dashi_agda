module DASHI.Analysis.RiemannG2PoleQuotientFinalCutReconciliationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientCurrentCutExact as Pole
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as R8889
import DASHI.Analysis.RiemannG2QuarterPeriodPoleQuotientFinalCompilerExact as Final
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as ProducerAllowance
import DASHI.Analysis.RiemannG2PoleQuotientChannelAllowanceExact as Allowance
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotleG2dScalarDeterminantSumTargetExact as Det

------------------------------------------------------------------------
-- FINAL-CARRIER RECONCILIATION
--
-- The determinant-taper G2d lane and the universal pole-quotient lane contain
-- similar reflection-paired cosine kernels, but the repository explicitly does
-- NOT identify their tapers. Hence determinant signed cancellation remains a
-- useful scalarization/diagnostic theorem and cannot silently pay final H_off.
--
-- The authoritative final high-ordinate consumer is already owned:
--
--   cluster = offOrdinate + Gamma
--   offOrdinate <= B_off
--   Gamma <= B_Gamma
--   B_off + B_Gamma < M_cluster.
--
-- Bare local upper-bound targets are too weak: arbitrarily oversized budgets
-- can satisfy local upper theorems while missing the final strict window.
-- The producer-facing leaf is therefore concrete even before same-object
-- transport: a downstream-assigned allowance lives in the producer's scalar
-- carrier, and the analytic proof must establish
--
--   B_off <= A_off       or       B_Gamma <= A_Gamma.
--
-- After same-object transport, the final consumer proves
--
--   A_off + A_Gamma < M_cluster,
--
-- and the generic allowance compiler derives the strict combined budget. No
-- subtraction/division/midpoint structure is required.
------------------------------------------------------------------------

data FinalHighOrdinateLeaf : Set where
  universalPoleQuotientSignedOff : FinalHighOrdinateLeaf
  sameTaperGammaPrecision : FinalHighOrdinateLeaf
  ownedClusterMarginAttachment : FinalHighOrdinateLeaf
  determinantSignedDiagnostic : FinalHighOrdinateLeaf
  rebuildFinalContradictionCompiler : FinalHighOrdinateLeaf


data FinalLeafState : Set where
  live : FinalLeafState
  downstream : FinalLeafState
  diagnostic : FinalLeafState
  pruned : FinalLeafState

finalLeafState : FinalHighOrdinateLeaf -> FinalLeafState
finalLeafState universalPoleQuotientSignedOff = live
finalLeafState sameTaperGammaPrecision = live
finalLeafState ownedClusterMarginAttachment = downstream
finalLeafState determinantSignedDiagnostic = diagnostic
finalLeafState rebuildFinalContradictionCompiler = pruned

universalPoleQuotientOffIsLive :
  finalLeafState universalPoleQuotientSignedOff ≡ live
universalPoleQuotientOffIsLive = refl

gammaPrecisionIsLive :
  finalLeafState sameTaperGammaPrecision ≡ live
gammaPrecisionIsLive = refl

clusterAttachmentIsDownstream :
  finalLeafState ownedClusterMarginAttachment ≡ downstream
clusterAttachmentIsDownstream = refl

determinantPaymentIsDiagnostic :
  finalLeafState determinantSignedDiagnostic ≡ diagnostic
determinantPaymentIsDiagnostic = refl

finalCompilerRebuildIsPruned :
  finalLeafState rebuildFinalContradictionCompiler ≡ pruned
finalCompilerRebuildIsPruned = refl

------------------------------------------------------------------------
-- Exact producer-facing final leaf types.
------------------------------------------------------------------------

LiteralFinalSignedOffPayment : Set₁
LiteralFinalSignedOffPayment = ProducerAllowance.PoleQuotientOffAllowancePayment

LiteralFinalGammaPayment : Set₁
LiteralFinalGammaPayment = ProducerAllowance.PoleQuotientGammaAllowancePayment

FinalCommonCarrierAllowancePayment :
  (surface : Split.OrderedAdditiveComplementSurface) -> Set₁
FinalCommonCarrierAllowancePayment = Allowance.PoleQuotientChannelAllowance

------------------------------------------------------------------------
-- Existing-owner pins.
------------------------------------------------------------------------

finalPoleQuotientDoesNotAcceptDeterminantTaperWithoutTransport :
  Pole.rankTwoDeterminantQTransportedToPoleQuotientCarrier
    Pole.canonicalPoleQuotientCurrentCut ≡ false
finalPoleQuotientDoesNotAcceptDeterminantTaperWithoutTransport = refl

finalPoleQuotientSignedOffStillOpen :
  Pole.poleQuotientSignedOffOrdinateBoundClosed
    Pole.canonicalPoleQuotientCurrentCut ≡ false
finalPoleQuotientSignedOffStillOpen = refl

finalPoleQuotientGammaStillOpen :
  Pole.gammaResidualBudgetClosed Pole.canonicalPoleQuotientCurrentCut ≡ false
finalPoleQuotientGammaStillOpen = refl

clusterMarginMathematicsAlreadyOwned :
  R8889.quantitativeClusterMarginOwned
    R8889.canonicalCheckedLeanPoleQuotientReturn8889 ≡ true
clusterMarginMathematicsAlreadyOwned = refl

clusterMarginNeedsNoFreshDerivation :
  R8889.PoleQuotientProducerReconciliationBoundary.clusterMathematicsNeedsFreshDerivation
    R8889.canonicalPoleQuotientProducerReconciliationBoundary ≡ false
clusterMarginNeedsNoFreshDerivation = refl

finalComplementCompilerAlreadyOwned :
  Final.QuarterPeriodPoleQuotientBoundary.existingSplitComplementCompilerIsReusable
    Final.canonicalQuarterPeriodPoleQuotientBoundary ≡ true
finalComplementCompilerAlreadyOwned = refl

determinantSignedLeafStillMathematicallyOpen :
  Det.signedScalarDeterminantSumBoundClosed
    Det.canonicalG2dScalarDeterminantSumTarget ≡ false
determinantSignedLeafStillMathematicallyOpen = refl

producerAllowanceTargetIsConcrete :
  ProducerAllowance.ProducerAllowanceTargetBoundary.offLeafIsBudgetBelowAssignedAllowance
    ProducerAllowance.canonicalProducerAllowanceTargetBoundary ≡ true
producerAllowanceTargetIsConcrete = refl

gammaAllowanceTargetIsConcrete :
  ProducerAllowance.ProducerAllowanceTargetBoundary.gammaLeafIsBudgetBelowAssignedAllowance
    ProducerAllowance.canonicalProducerAllowanceTargetBoundary ≡ true
gammaAllowanceTargetIsConcrete = refl

allowanceCompilerUsesNoHalfMarginDivision :
  Allowance.PoleQuotientChannelAllowanceBoundary.halfMarginDivisionRequired
    Allowance.canonicalPoleQuotientChannelAllowanceBoundary ≡ false
allowanceCompilerUsesNoHalfMarginDivision = refl

allowanceCompilerProducesStrictCombinedBudget :
  Allowance.PoleQuotientChannelAllowanceBoundary.separateProducerBoundsCompileToStrictCombinedBudget
    Allowance.canonicalPoleQuotientChannelAllowanceBoundary ≡ true
allowanceCompilerProducesStrictCombinedBudget = refl

record PoleQuotientFinalCutBoundary : Set where
  constructor pole-quotient-final-cut-boundary
  field
    determinantLaneIsFinalPoleQuotientCarrier : Bool
    determinantLaneIsFinalPoleQuotientCarrierIsFalse :
      determinantLaneIsFinalPoleQuotientCarrier ≡ false

    determinantDirectPaymentAutomaticallyPaysFinalOffSocket : Bool
    determinantDirectPaymentAutomaticallyPaysFinalOffSocketIsFalse :
      determinantDirectPaymentAutomaticallyPaysFinalOffSocket ≡ false

    bareOffTargetInhabitanceAloneIsConsumerSufficient : Bool
    bareOffTargetInhabitanceAloneIsConsumerSufficientIsFalse :
      bareOffTargetInhabitanceAloneIsConsumerSufficient ≡ false

    bareGammaTargetInhabitanceAloneIsConsumerSufficient : Bool
    bareGammaTargetInhabitanceAloneIsConsumerSufficientIsFalse :
      bareGammaTargetInhabitanceAloneIsConsumerSufficient ≡ false

    producerMayChooseItsOwnAllowance : Bool
    producerMayChooseItsOwnAllowanceIsFalse :
      producerMayChooseItsOwnAllowance ≡ false

    producerFacingAllowanceTargetsAreConcrete : Bool
    producerFacingAllowanceTargetsAreConcreteIsTrue :
      producerFacingAllowanceTargetsAreConcrete ≡ true

    finalCommonCarrierHasConcreteAllowanceCompiler : Bool
    finalCommonCarrierHasConcreteAllowanceCompilerIsTrue :
      finalCommonCarrierHasConcreteAllowanceCompiler ≡ true

    finalAllowanceCompilerRequiresHalfMarginDivision : Bool
    finalAllowanceCompilerRequiresHalfMarginDivisionIsFalse :
      finalAllowanceCompilerRequiresHalfMarginDivision ≡ false

    literalUniversalPoleQuotientSignedOffIsForwardLeaf : Bool
    literalUniversalPoleQuotientSignedOffIsForwardLeafIsTrue :
      literalUniversalPoleQuotientSignedOffIsForwardLeaf ≡ true

    sameTaperGammaPrecisionIsForwardLeaf : Bool
    sameTaperGammaPrecisionIsForwardLeafIsTrue :
      sameTaperGammaPrecisionIsForwardLeaf ≡ true

    freshClusterMarginAnalysisRequired : Bool
    freshClusterMarginAnalysisRequiredIsFalse :
      freshClusterMarginAnalysisRequired ≡ false

    finalContradictionCompilerNeedsRebuilding : Bool
    finalContradictionCompilerNeedsRebuildingIsFalse :
      finalContradictionCompilerNeedsRebuilding ≡ false

    representationAdaptersArePrimaryNewHarmonicResearch : Bool
    representationAdaptersArePrimaryNewHarmonicResearchIsFalse :
      representationAdaptersArePrimaryNewHarmonicResearch ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalPoleQuotientFinalCutBoundary : PoleQuotientFinalCutBoundary
canonicalPoleQuotientFinalCutBoundary =
  pole-quotient-final-cut-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "Treat the repository as closed-world for infrastructure, but preserve exact carrier ownership and consumer strength. The determinant q lane is diagnostic/scalarization and is not definitionally the final universal pole-quotient taper. Bare off/Gamma target inhabitance is insufficient. The producer-facing leaves now carry downstream-assigned allowances in their own scalar carriers and must prove B_off <= A_off or B_Gamma <= A_Gamma. After same-object transport, the final consumer proves A_off + A_Gamma < M_cluster; the ordered-additive allowance compiler yields the strict combined budget without division or midpoint structure, and the allowance-aware same-object assembly feeds the existing contradiction compiler. The two live analytic leaves remain the literal universal-pole-quotient signed off estimate and same-taper Gamma precision. Cluster mathematics is already owned; RH is not derived."
