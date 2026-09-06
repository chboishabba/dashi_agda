module DASHI.Analysis.RiemannG2PoleQuotientFinalCutReconciliationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientCurrentCutExact as Pole
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as R8889
import DASHI.Analysis.RiemannG2QuarterPeriodPoleQuotientFinalCompilerExact as Final
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
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
-- A bare local upper-bound target is still too weak to count as the analytic
-- payment: an arbitrary oversized budget can satisfy a local upper theorem and
-- be useless to the strict final window. Therefore this owner strengthens the
-- final leaves with proof-bearing consumer-adequacy receipts while retaining the
-- historical target APIs unchanged.
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
-- CONSUMER-SUFFICIENT FINAL LEAVES
--
-- Each target already carries its local upper theorem. These wrappers add the
-- exact facts a final-use producer must prove rather than merely name as Sets.
------------------------------------------------------------------------

record ConsumerSufficientPoleQuotientOffProducer : Set₁ where
  field
    target : Off.PoleQuotientOffOrdinateBudgetTarget

    crossingCutoffFeedsThisExactOffProducer : Set
    crossingCutoffFeedsThisExactOffProducerReceipt :
      crossingCutoffFeedsThisExactOffProducer

    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    sameLiteralPoleQuotientTaperAsFinalConsumerReceipt :
      sameLiteralPoleQuotientTaperAsFinalConsumer

    FitsSharpClusterAccuracyWindow :
      Off.PoleQuotientOffOrdinateBudgetTarget -> Set
    fitsSharpClusterAccuracyWindow : FitsSharpClusterAccuracyWindow target

    producerReference : String

open ConsumerSufficientPoleQuotientOffProducer public

record ConsumerSufficientPoleQuotientGammaProducer : Set₁ where
  field
    target : Gamma.PoleQuotientGammaBudgetTarget

    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    sameLiteralPoleQuotientTaperAsFinalConsumerReceipt :
      sameLiteralPoleQuotientTaperAsFinalConsumer

    FitsSharpClusterAccuracyWindow :
      Gamma.PoleQuotientGammaBudgetTarget -> Set
    fitsSharpClusterAccuracyWindow : FitsSharpClusterAccuracyWindow target

    producerReference : String

open ConsumerSufficientPoleQuotientGammaProducer public

-- Canonical surviving signed analytic payment. This is deliberately stronger
-- than merely inhabiting PoleQuotientOffOrdinateBudgetTarget.
LiteralFinalSignedOffPayment : Set₁
LiteralFinalSignedOffPayment = ConsumerSufficientPoleQuotientOffProducer

LiteralFinalGammaPayment : Set₁
LiteralFinalGammaPayment = ConsumerSufficientPoleQuotientGammaProducer

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

    finalOffLeafCarriesSharpWindowAdequacyReceipt : Bool
    finalOffLeafCarriesSharpWindowAdequacyReceiptIsTrue :
      finalOffLeafCarriesSharpWindowAdequacyReceipt ≡ true

    finalGammaLeafCarriesSharpWindowAdequacyReceipt : Bool
    finalGammaLeafCarriesSharpWindowAdequacyReceiptIsTrue :
      finalGammaLeafCarriesSharpWindowAdequacyReceipt ≡ true

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
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "Treat the repository as closed-world for infrastructure, but preserve exact carrier ownership and consumer strength. The determinant q lane is diagnostic/scalarization and is not definitionally the final universal pole-quotient taper. Bare off/Gamma target inhabitance is also insufficient because an arbitrary oversized budget need not fit the strict final window. The two live analytic leaves are proof-bearing consumer-sufficient producers: the exact universal pole-quotient reflection-cosine off bound with crossing/same-taper/sharp-window receipts, and the same-taper Gamma bound with a sharp-window receipt. The 8889 quantitative cluster margin is owned mathematics requiring only same-object attachment, and the final split-complement contradiction compiler is already closed. RH is not derived."
