module DASHI.Analysis.RiemannG2PoleQuotientFinalCutReconciliationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientCurrentCutExact as Pole
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as R8889
import DASHI.Analysis.RiemannG2QuarterPeriodPoleQuotientFinalCompilerExact as Final
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
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
-- The existing compiler turns those inputs into contradiction. The 8889 return
-- additionally says the quantitative cluster-margin mathematics is already
-- owned, leaving only same-object attachment. Under closed-world repo search,
-- the genuinely analytic leaves are therefore:
--
--   1. literal universal-pole-quotient signed off-ordinate bound;
--   2. same-taper Gamma precision repair.
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

-- Canonical type of the surviving signed analytic leaf. This aliases the
-- existing target; it does not create a weaker surrogate.
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
