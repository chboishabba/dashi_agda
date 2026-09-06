module DASHI.Analysis.RiemannG2PoleQuotientFinalCutReconciliationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientCurrentCutExact as Pole
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as R8889
import DASHI.Analysis.RiemannG2QuarterPeriodPoleQuotientFinalCompilerExact as Final
import DASHI.Analysis.RiemannG2PoleQuotientChannelAllowanceExact as Allowance
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
-- A bare local upper-bound target is too weak to count as the analytic payment:
-- an arbitrary oversized budget can satisfy a local upper theorem and be useless
-- to the strict final window. Likewise the producer must not be allowed to
-- choose its own meaning of "sharp enough". Consumer adequacy is therefore an
-- EXTERNAL predicate supplied by the downstream final consumer, and the producer
-- must inhabit that fixed predicate.
--
-- The repo already owns a more concrete allowance pattern in the Riemann lane.
-- `RiemannG2PoleQuotientChannelAllowanceExact` lifts that pattern to the final
-- off/Gamma split:
--
--   B_off <= A_off
--   B_Gamma <= A_Gamma
--   A_off + A_Gamma < M_cluster
--
-- compiles to B_off + B_Gamma < M_cluster. No midpoint/division structure is
-- required on the deliberately weak ordered-additive final carrier.
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
-- `OffAdequate` / `GammaAdequate` are parameters, not fields. Thus the final
-- consumer fixes the acceptance predicate and a producer cannot make its own
-- budget vacuously adequate by choosing a permissive relation.
--
-- On the final common ordered scalar carrier the canonical concrete adequacy
-- shape is the allowance ledger above. The abstract parameters remain here only
-- because off/Gamma target records still carry independent scalar types before
-- same-object transport.
------------------------------------------------------------------------

record ConsumerSufficientPoleQuotientOffProducer
    (OffAdequate : Off.PoleQuotientOffOrdinateBudgetTarget -> Set) : Set₁ where
  field
    target : Off.PoleQuotientOffOrdinateBudgetTarget

    crossingCutoffFeedsThisExactOffProducer : Set
    crossingCutoffFeedsThisExactOffProducerReceipt :
      crossingCutoffFeedsThisExactOffProducer

    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    sameLiteralPoleQuotientTaperAsFinalConsumerReceipt :
      sameLiteralPoleQuotientTaperAsFinalConsumer

    fitsSharpClusterAccuracyWindow : OffAdequate target

    producerReference : String

open ConsumerSufficientPoleQuotientOffProducer public

record ConsumerSufficientPoleQuotientGammaProducer
    (GammaAdequate : Gamma.PoleQuotientGammaBudgetTarget -> Set) : Set₁ where
  field
    target : Gamma.PoleQuotientGammaBudgetTarget

    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    sameLiteralPoleQuotientTaperAsFinalConsumerReceipt :
      sameLiteralPoleQuotientTaperAsFinalConsumer

    fitsSharpClusterAccuracyWindow : GammaAdequate target

    producerReference : String

open ConsumerSufficientPoleQuotientGammaProducer public

LiteralFinalSignedOffPayment :
  (OffAdequate : Off.PoleQuotientOffOrdinateBudgetTarget -> Set) -> Set₁
LiteralFinalSignedOffPayment = ConsumerSufficientPoleQuotientOffProducer

LiteralFinalGammaPayment :
  (GammaAdequate : Gamma.PoleQuotientGammaBudgetTarget -> Set) -> Set₁
LiteralFinalGammaPayment = ConsumerSufficientPoleQuotientGammaProducer

FinalCommonCarrierAllowancePayment :
  (surface :
    DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact.OrderedAdditiveComplementSurface)
  -> Set₁
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

    producerMayChooseItsOwnSharpWindowPredicate : Bool
    producerMayChooseItsOwnSharpWindowPredicateIsFalse :
      producerMayChooseItsOwnSharpWindowPredicate ≡ false

    finalCommonCarrierHasConcreteAllowanceCompiler : Bool
    finalCommonCarrierHasConcreteAllowanceCompilerIsTrue :
      finalCommonCarrierHasConcreteAllowanceCompiler ≡ true

    finalAllowanceCompilerRequiresHalfMarginDivision : Bool
    finalAllowanceCompilerRequiresHalfMarginDivisionIsFalse :
      finalAllowanceCompilerRequiresHalfMarginDivision ≡ false

    finalOffLeafCarriesConsumerDefinedAdequacyReceipt : Bool
    finalOffLeafCarriesConsumerDefinedAdequacyReceiptIsTrue :
      finalOffLeafCarriesConsumerDefinedAdequacyReceipt ≡ true

    finalGammaLeafCarriesConsumerDefinedAdequacyReceipt : Bool
    finalGammaLeafCarriesConsumerDefinedAdequacyReceiptIsTrue :
      finalGammaLeafCarriesConsumerDefinedAdequacyReceipt ≡ true

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
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "Treat the repository as closed-world for infrastructure, but preserve exact carrier ownership and consumer strength. The determinant q lane is diagnostic/scalarization and is not definitionally the final universal pole-quotient taper. Bare off/Gamma target inhabitance is insufficient because an arbitrary oversized budget need not fit the strict final window, and a producer may not define its own notion of adequacy. On the final common carrier, adequacy is now concrete: the consumer assigns off/Gamma allowances, each actual producer budget must lie below its assigned allowance, and the allowance sum must lie strictly below the quantitative cluster margin. The generic ordered-additive compiler then yields the strict combined budget without division or midpoint structure. The two live analytic leaves remain the literal universal-pole-quotient signed off estimate and same-taper Gamma precision; cluster mathematics and final contradiction algebra are already owned. RH is not derived."
