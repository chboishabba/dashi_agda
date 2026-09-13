module DASHI.Analysis.RiemannG2FinalNearIndexedLiteralModelCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearEvaluationBidiExact as Eval
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Final
import DASHI.Analysis.RiemannG2FiniteNearIndexedLiteralKernelCompilerExact as Indexed
import DASHI.Analysis.RiemannG2FinalNearIndexedFiniteProducerExact as FinalFinite

------------------------------------------------------------------------
-- FINAL-NEAR-INDEXED LITERAL MODEL COMPILER
--
-- On the preferred direct route, choose the carrier-neutral finite evaluator to
-- evaluate final nearResponseAt(chosen J) definitionally.  Then the literal
-- representation debt reduces to one proof-relevant theorem:
--
--   nearResponseAt(chosen J) = finiteNearSum(cellResponse).
--
-- No separate signed-value/literal-value weld and no signed-value/final-near
-- weld remain.  The actual post-crossing strict ClusterResponse inequality is
-- still a separate analytic theorem.
------------------------------------------------------------------------

record FinalNearIndexedLiteralKernel
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport)
    (finiteInput : FinalFinite.FinalNearIndexedFiniteInput offInput) : Set₁ where
  private
    Scalar = NearFar.Scalar S
    finalNear = Transport.nearResponseAt transport (Direct.chosenCutoff offInput)
  field
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

    finalNearResponseIsLiteralFiniteSum :
      finalNear ≡ finiteNearSum cellResponse

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

open FinalNearIndexedLiteralKernel public

compiledGenericFiniteProducer :
  forall {S transport offInput} ->
  (finiteInput : FinalFinite.FinalNearIndexedFiniteInput
    {S = S} {transport = transport} offInput) ->
  Eval.FiniteNearProducer
compiledGenericFiniteProducer {offInput = offInput} finiteInput =
  FinalFinite.compileFinalNearIndexedFiniteProducer offInput finiteInput

compiledIndexedKernel :
  forall {S transport} ->
  (offInput : Direct.DirectLiteralOffTargetInput S transport) ->
  (finiteInput : FinalFinite.FinalNearIndexedFiniteInput offInput) ->
  FinalNearIndexedLiteralKernel offInput finiteInput ->
  Indexed.FiniteNearIndexedLiteralKernel S
    (FinalFinite.compileFinalNearIndexedFiniteProducer offInput finiteInput)
compiledIndexedKernel offInput finiteInput kernel = record
  { Indexed.evaluationScalarIdentity = refl
  ; Indexed.ZeroIndex = ZeroIndex kernel
  ; Indexed.nearIndex = nearIndex kernel
  ; Indexed.multiplicity = multiplicity kernel
  ; Indexed.horizontalDisplacement = horizontalDisplacement kernel
  ; Indexed.ordinate = ordinate kernel
  ; Indexed.target = target kernel
  ; Indexed.subtract = subtract kernel
  ; Indexed.targetRelativeGap = targetRelativeGap kernel
  ; Indexed.targetRelativeGapIsOrdinateMinusTarget =
      targetRelativeGapIsOrdinateMinusTarget kernel
  ; Indexed.four = four kernel
  ; Indexed.mul = mul kernel
  ; Indexed.cosh = cosh kernel
  ; Indexed.cos = cos kernel
  ; Indexed.poleTaperValue = poleTaperValue kernel
  ; Indexed.integrate = integrate kernel
  ; Indexed.finiteNearSum = finiteNearSum kernel
  ; Indexed.cellResponse = cellResponse kernel
  ; Indexed.cellResponseIsLiteralReflectionPair =
      cellResponseIsLiteralReflectionPair kernel
  ; Indexed.signedEvaluationIsLiteralFiniteSum =
      finalNearResponseIsLiteralFiniteSum kernel
  ; Indexed.exactNearIndexIsCheckedNearOffFinset =
      exactNearIndexIsCheckedNearOffFinset kernel
  ; Indexed.exactNearIndexIsCheckedNearOffFinsetReceipt =
      exactNearIndexIsCheckedNearOffFinsetReceipt kernel
  ; Indexed.exactMultiplicityIsZetaMultiplicity =
      exactMultiplicityIsZetaMultiplicity kernel
  ; Indexed.exactMultiplicityIsZetaMultiplicityReceipt =
      exactMultiplicityIsZetaMultiplicityReceipt kernel
  ; Indexed.exactHorizontalDisplacementIsOffLineRealPart =
      exactHorizontalDisplacementIsOffLineRealPart kernel
  ; Indexed.exactHorizontalDisplacementIsOffLineRealPartReceipt =
      exactHorizontalDisplacementIsOffLineRealPartReceipt kernel
  ; Indexed.exactPoleTaperIsFinalUniversalPoleQuotientTaper =
      exactPoleTaperIsFinalUniversalPoleQuotientTaper kernel
  ; Indexed.exactPoleTaperIsFinalUniversalPoleQuotientTaperReceipt =
      exactPoleTaperIsFinalUniversalPoleQuotientTaperReceipt kernel
  ; Indexed.reflectionPairAlreadyCancelsOddHeightChannel =
      reflectionPairAlreadyCancelsOddHeightChannel kernel
  ; Indexed.reflectionPairAlreadyCancelsOddHeightChannelReceipt =
      reflectionPairAlreadyCancelsOddHeightChannelReceipt kernel
  ; Indexed.kernelReference = kernelReference kernel
  }

compileFinalNearIndexedLiteralModel :
  forall {S transport} ->
  (offInput : Direct.DirectLiteralOffTargetInput S transport) ->
  (finiteInput : FinalFinite.FinalNearIndexedFiniteInput offInput) ->
  (kernel : FinalNearIndexedLiteralKernel offInput finiteInput) ->
  Final.FinalPoleNearLiteralModel offInput
compileFinalNearIndexedLiteralModel offInput finiteInput kernel =
  Indexed.compileIndexedFinalLiteralModel
    offInput
    finite
    indexedKernel
    record
      { Indexed.signedEvaluationIsFinalNearResponse = refl
      ; Indexed.attachmentReference = kernelReference kernel
      }
  where
  finite : Eval.FiniteNearProducer
  finite = FinalFinite.compileFinalNearIndexedFiniteProducer offInput finiteInput

  indexedKernel : Indexed.FiniteNearIndexedLiteralKernel _ finite
  indexedKernel = compiledIndexedKernel offInput finiteInput kernel

record FinalNearIndexedLiteralModelBoundary : Set where
  constructor final-near-indexed-literal-model-boundary
  field
    separateSignedValueToLiteralValueWeldRequired : Bool
    separateSignedValueToLiteralValueWeldRequiredIsFalse :
      separateSignedValueToLiteralValueWeldRequired ≡ false

    separateSignedValueToFinalNearWeldRequired : Bool
    separateSignedValueToFinalNearWeldRequiredIsFalse :
      separateSignedValueToFinalNearWeldRequired ≡ false

    finalNearToLiteralFiniteSumIsSingleScalarRepresentationTheorem : Bool
    finalNearToLiteralFiniteSumIsSingleScalarRepresentationTheoremIsTrue :
      finalNearToLiteralFiniteSumIsSingleScalarRepresentationTheorem ≡ true

    explicitWindowRequired : Bool
    explicitWindowRequiredIsFalse : explicitWindowRequired ≡ false

    determinantConsumerRequired : Bool
    determinantConsumerRequiredIsFalse : determinantConsumerRequired ≡ false

    existingFinalLiteralModelIsCompilerOutput : Bool
    existingFinalLiteralModelIsCompilerOutputIsTrue :
      existingFinalLiteralModelIsCompilerOutput ≡ true

    analyticClusterResponseInequalityPaidHere : Bool
    analyticClusterResponseInequalityPaidHereIsFalse :
      analyticClusterResponseInequalityPaidHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    shortestDirectRepresentationPath : String

canonicalFinalNearIndexedLiteralModelBoundary :
  FinalNearIndexedLiteralModelBoundary
canonicalFinalNearIndexedLiteralModelBoundary =
  final-near-indexed-literal-model-boundary
    false refl
    false refl
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl
    "Index the carrier-neutral finite evaluator on final nearResponseAt(chosen J), realize the literal universal-pole-quotient kernel, and prove the single scalar representation theorem nearResponseAt(J)=finiteNearSum(cellResponse). Then the generic FiniteNearProducer, both former same-object welds, and the existing FinalPoleNearLiteralModel are compiler output. The post-crossing literalNear+far+Gamma<ClusterResponse theorem remains separate and unproved."
