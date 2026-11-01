module DASHI.Analysis.RiemannG2FiniteNearIndexedLiteralKernelCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearEvaluationBidiExact as Eval
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Final
import DASHI.Analysis.RiemannG2WindowFreeFiniteNearFinalModelCompilerExact as WindowFree

------------------------------------------------------------------------
-- FINITE-EVALUATION-INDEXED LITERAL KERNEL
--
-- Do not ask for a separate equality
--
--   signedNearValue = literalFiniteNearValue.
--
-- Instead define the literal finite value to be the transported signed value of
-- the carrier-neutral FiniteNearProducer.  The actual representation theorem is
-- then exactly
--
--   signedNearValue = finiteNearSum cellResponse.
--
-- One external same-object equality remains:
--
--   signedNearValue = final nearResponseAt(chosen J).
------------------------------------------------------------------------

cast : {A B : Set} -> A ≡ B -> A -> B
cast refl x = x

record FiniteNearIndexedLiteralKernel
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (finite : Eval.FiniteNearProducer) : Set₁ where
  private
    Scalar = NearFar.Scalar S
    evaluation = Eval.FiniteNearProducer.evaluation finite
  field
    evaluationScalarIdentity :
      Eval.SignedFiniteNearEvaluationSurface.Scalar evaluation ≡ Scalar

    ZeroIndex : Set
    nearIndex : ZeroIndex -> Set
    multiplicity : ZeroIndex -> Scalar
    horizontalDisplacement : ZeroIndex -> Scalar

    ordinate : ZeroIndex -> Scalar
    target : Scalar
    subtract : Scalar -> Scalar -> Scalar
    targetRelativeGap : ZeroIndex -> Scalar
    targetRelativeGapIsOrdinateMinusTarget :
      (sigma : ZeroIndex) ->
      targetRelativeGap sigma ≡ subtract (ordinate sigma) target

    four : Scalar
    mul : Scalar -> Scalar -> Scalar
    cosh cos : Scalar -> Scalar
    poleTaperValue : Scalar -> Scalar
    integrate : (Scalar -> Scalar) -> Scalar
    finiteNearSum : (ZeroIndex -> Scalar) -> Scalar

    cellResponse : ZeroIndex -> Scalar
    cellResponseIsLiteralReflectionPair :
      (sigma : ZeroIndex) ->
      cellResponse sigma
      ≡ integrate
          (λ u ->
            mul
              (mul
                (mul four (poleTaperValue u))
                (mul
                  (multiplicity sigma)
                  (cosh (mul (horizontalDisplacement sigma) u))))
              (cos (mul (targetRelativeGap sigma) u)))

    signedEvaluationIsLiteralFiniteSum :
      cast evaluationScalarIdentity
        (Eval.SignedFiniteNearEvaluationSurface.signedNearValue evaluation)
      ≡ finiteNearSum cellResponse

    exactNearIndexIsCheckedNearOffFinset : Set
    exactNearIndexIsCheckedNearOffFinsetReceipt :
      exactNearIndexIsCheckedNearOffFinset

    exactMultiplicityIsZetaMultiplicity : Set
    exactMultiplicityIsZetaMultiplicityReceipt :
      exactMultiplicityIsZetaMultiplicity

    exactHorizontalDisplacementIsOffLineRealPart : Set
    exactHorizontalDisplacementIsOffLineRealPartReceipt :
      exactHorizontalDisplacementIsOffLineRealPart

    exactPoleTaperIsFinalUniversalPoleQuotientTaper : Set
    exactPoleTaperIsFinalUniversalPoleQuotientTaperReceipt :
      exactPoleTaperIsFinalUniversalPoleQuotientTaper

    reflectionPairAlreadyCancelsOddHeightChannel : Set
    reflectionPairAlreadyCancelsOddHeightChannelReceipt :
      reflectionPairAlreadyCancelsOddHeightChannel

    kernelReference : String

open FiniteNearIndexedLiteralKernel public

compiledWindowFreeKernel :
  forall {S finite} ->
  FiniteNearIndexedLiteralKernel S finite ->
  WindowFree.FinalPoleNearLiteralKernel S
compiledWindowFreeKernel {finite = finite} kernel = record
  { WindowFree.ZeroIndex = ZeroIndex kernel
  ; WindowFree.nearIndex = nearIndex kernel
  ; WindowFree.multiplicity = multiplicity kernel
  ; WindowFree.horizontalDisplacement = horizontalDisplacement kernel
  ; WindowFree.ordinate = ordinate kernel
  ; WindowFree.target = target kernel
  ; WindowFree.subtract = subtract kernel
  ; WindowFree.targetRelativeGap = targetRelativeGap kernel
  ; WindowFree.targetRelativeGapIsOrdinateMinusTarget =
      targetRelativeGapIsOrdinateMinusTarget kernel
  ; WindowFree.four = four kernel
  ; WindowFree.mul = mul kernel
  ; WindowFree.cosh = cosh kernel
  ; WindowFree.cos = cos kernel
  ; WindowFree.poleTaperValue = poleTaperValue kernel
  ; WindowFree.integrate = integrate kernel
  ; WindowFree.finiteNearSum = finiteNearSum kernel
  ; WindowFree.cellResponse = cellResponse kernel
  ; WindowFree.cellResponseIsLiteralReflectionPair =
      cellResponseIsLiteralReflectionPair kernel
  ; WindowFree.literalFiniteNearValue =
      cast (evaluationScalarIdentity kernel)
        (Eval.SignedFiniteNearEvaluationSurface.signedNearValue
          (Eval.FiniteNearProducer.evaluation finite))
  ; WindowFree.literalFiniteNearValueIsSum =
      signedEvaluationIsLiteralFiniteSum kernel
  ; WindowFree.exactNearIndexIsCheckedNearOffFinset =
      exactNearIndexIsCheckedNearOffFinset kernel
  ; WindowFree.exactNearIndexIsCheckedNearOffFinsetReceipt =
      exactNearIndexIsCheckedNearOffFinsetReceipt kernel
  ; WindowFree.exactMultiplicityIsZetaMultiplicity =
      exactMultiplicityIsZetaMultiplicity kernel
  ; WindowFree.exactMultiplicityIsZetaMultiplicityReceipt =
      exactMultiplicityIsZetaMultiplicityReceipt kernel
  ; WindowFree.exactHorizontalDisplacementIsOffLineRealPart =
      exactHorizontalDisplacementIsOffLineRealPart kernel
  ; WindowFree.exactHorizontalDisplacementIsOffLineRealPartReceipt =
      exactHorizontalDisplacementIsOffLineRealPartReceipt kernel
  ; WindowFree.exactPoleTaperIsFinalUniversalPoleQuotientTaper =
      exactPoleTaperIsFinalUniversalPoleQuotientTaper kernel
  ; WindowFree.exactPoleTaperIsFinalUniversalPoleQuotientTaperReceipt =
      exactPoleTaperIsFinalUniversalPoleQuotientTaperReceipt kernel
  ; WindowFree.reflectionPairAlreadyCancelsOddHeightChannel =
      reflectionPairAlreadyCancelsOddHeightChannel kernel
  ; WindowFree.reflectionPairAlreadyCancelsOddHeightChannelReceipt =
      reflectionPairAlreadyCancelsOddHeightChannelReceipt kernel
  ; WindowFree.kernelReference = kernelReference kernel
  }

record IndexedFiniteNearFinalAttachment
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport)
    (finite : Eval.FiniteNearProducer)
    (kernel : FiniteNearIndexedLiteralKernel S finite) : Set₁ where
  private
    evaluation = Eval.FiniteNearProducer.evaluation finite
  field
    signedEvaluationIsFinalNearResponse :
      cast (evaluationScalarIdentity kernel)
        (Eval.SignedFiniteNearEvaluationSurface.signedNearValue evaluation)
      ≡ Transport.nearResponseAt transport (Direct.chosenCutoff offInput)

    attachmentReference : String

open IndexedFiniteNearFinalAttachment public

compileIndexedFinalLiteralModel :
  forall {S transport} ->
  (offInput : Direct.DirectLiteralOffTargetInput S transport) ->
  (finite : Eval.FiniteNearProducer) ->
  (kernel : FiniteNearIndexedLiteralKernel S finite) ->
  IndexedFiniteNearFinalAttachment offInput finite kernel ->
  Final.FinalPoleNearLiteralModel offInput
compileIndexedFinalLiteralModel offInput finite kernel attachment =
  WindowFree.compileWindowFreeFinalLiteralModel
    offInput
    (compiledWindowFreeKernel kernel)
    finite
    record
      { WindowFree.evaluationScalarIdentity = evaluationScalarIdentity kernel
      ; WindowFree.signedEvaluationIsLiteralFiniteNear = refl
      ; WindowFree.signedEvaluationIsFinalNearResponse =
          signedEvaluationIsFinalNearResponse attachment
      ; WindowFree.attachmentReference = attachmentReference attachment
      }

record FiniteNearIndexedLiteralKernelBoundary : Set where
  constructor finite-near-indexed-literal-kernel-boundary
  field
    separateSignedValueEqualsLiteralValueWeldRequired : Bool
    separateSignedValueEqualsLiteralValueWeldRequiredIsFalse :
      separateSignedValueEqualsLiteralValueWeldRequired ≡ false

    signedEvaluationToLiteralSumTheoremStillRequired : Bool
    signedEvaluationToLiteralSumTheoremStillRequiredIsTrue :
      signedEvaluationToLiteralSumTheoremStillRequired ≡ true

    signedEvaluationToFinalNearWeldStillRequired : Bool
    signedEvaluationToFinalNearWeldStillRequiredIsTrue :
      signedEvaluationToFinalNearWeldStillRequired ≡ true

    explicitWindowRequired : Bool
    explicitWindowRequiredIsFalse : explicitWindowRequired ≡ false

    determinantConsumerRequired : Bool
    determinantConsumerRequiredIsFalse : determinantConsumerRequired ≡ false

    finalLiteralModelCompilesAfterKernelAndOneExternalWeld : Bool
    finalLiteralModelCompilesAfterKernelAndOneExternalWeldIsTrue :
      finalLiteralModelCompilesAfterKernelAndOneExternalWeld ≡ true

    analyticPhaseInequalityPaidHere : Bool
    analyticPhaseInequalityPaidHereIsFalse : analyticPhaseInequalityPaidHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    shortestDirectRepresentationPath : String

canonicalFiniteNearIndexedLiteralKernelBoundary :
  FiniteNearIndexedLiteralKernelBoundary
canonicalFiniteNearIndexedLiteralKernelBoundary =
  finite-near-indexed-literal-kernel-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl
    "Index the literal kernel by the carrier-neutral FiniteNearProducer and define literalFiniteNearValue to be its transported signedNearValue. The representation theorem is then signedNearValue = finiteNearSum(cellResponse), plus one external same-object weld signedNearValue = final nearResponseAt(chosen J). Those compile the existing FinalPoleNearLiteralModel. No selected Weil window or determinant consumer is required; the post-crossing strict ClusterResponse inequality remains separate and unproved."
