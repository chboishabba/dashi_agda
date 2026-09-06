module DASHI.Analysis.RiemannG2PoleQuotientFinalCutReconciliationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientCurrentCutExact as Pole
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as R8889
import DASHI.Analysis.RiemannG2QuarterPeriodPoleQuotientFinalCompilerExact as Final
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotleG2dScalarDeterminantSumTargetExact as Det
import DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact as Direct

------------------------------------------------------------------------
-- FINAL-CARRIER RECONCILIATION
--
-- The determinant-taper G2d lane and the universal pole-quotient lane contain
-- very similar reflection-paired cosine kernels, but the repository explicitly
-- does NOT identify their tapers.  Therefore a DirectSignedConsumerPayment on
-- the rank-two determinant problem is useful scalarization/diagnostic work; it
-- is not automatically the final pole-quotient H_off payment.
--
-- The authoritative final high-ordinate consumer is already owned elsewhere:
--
--   cluster = offOrdinate + Gamma
--   offOrdinate <= B_off
--   Gamma <= B_Gamma
--   B_off + B_Gamma < M_cluster
--
-- and the existing compiler turns those inputs into contradiction.  The 8889
-- return additionally says the quantitative cluster-margin MATHEMATICS is
-- already owned, leaving only same-object attachment.  Hence, under the user's
-- repo-complete search discipline, the two genuinely analytic leaves are:
--
--   1. literal universal-pole-quotient signed off-ordinate bound;
--   2. same-taper Gamma precision repair.
--
-- Representation/attachment work is downstream infrastructure, not a competing
-- harmonic-analysis research programme.
------------------------------------------------------------------------

data FinalHighOrdinateLeaf : Set where
  universalPoleQuotientSignedOff
  sameTaperGammaPrecision
  ownedClusterMarginAttachment
  determinantSignedDiagnostic
  rebuildFinalContradictionCompiler
  : FinalHighOrdinateLeaf

data FinalLeafState : Set where
  live downstream diagnostic pruned : FinalLeafState

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

-- This proposition is intentionally only a type alias for the final off leaf.
-- It prevents future schedulers from inventing a weaker surrogate target.
LiteralFinalSignedOffPayment : Set₁
LiteralFinalSignedOffPayment = Off.PoleQuotientOffOrdinateBudgetTarget

record PoleQuotientFinalCutBoundary : Set where
  constructor pole-quotient-final-cut-boundary
  field
    determinantLaneIsFinalPoleQuotientCarrier : Bool
    determinantLaneIsFinalPoleQuotientCarrierIsFalse :
      determinantLaneIsFinalPoleQuotientCarrier ≡ false

    determinantDirectPaymentAutomaticallyPaysFinalOffSocket : Bool
    determinantDirectPaymentAutomaticallyPaysFinalOffSocketIsFalse :
      determinantDirectPaymentAutomaticallyPaysFinalOffSocket ≡ false

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
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "Treat the repository as closed-world for infrastructure, but preserve exact carrier ownership. The rank-two determinant q lane is diagnostic/scalarization and is not definitionally the universal pole-quotient taper. The final high-ordinate mathematical cut therefore has two analytic leaves: inhabit PoleQuotientOffOrdinateBudgetTarget on the exact universal pole-quotient reflection-cosine carrier, and repair the same-taper Gamma budget to the already-owned sharp window. The 8889 quantitative cluster margin is owned mathematics requiring only same-object attachment, and the final split-complement contradiction compiler is already closed. RH is not derived."
