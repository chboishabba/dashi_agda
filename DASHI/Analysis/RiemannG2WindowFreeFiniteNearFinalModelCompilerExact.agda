module DASHI.Analysis.RiemannG2WindowFreeFiniteNearFinalModelCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearEvaluationBidiExact as Eval
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Final

------------------------------------------------------------------------
-- WINDOW-FREE FINAL-NEAR MODEL COMPILER
--
-- Introspection separates two debts that were previously fused inside
-- FinalPoleNearLiteralModel:
--
--   (K) realize the literal target-centred reflection-paired finite kernel;
--   (W) identify one carrier-neutral FiniteNearProducer evaluation both with
--       that literal finite value and with final nearResponseAt(chosen J).
--
-- Neither debt requires ActualSelectedPoleNearProducer or a Weil target window.
-- The explicit-window route remains an optional stronger route.
------------------------------------------------------------------------

cast : {A B : Set} -> A ≡ B -> A -> B
cast refl x = x

sym : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl yz = yz

------------------------------------------------------------------------
-- Literal phase-visible kernel, without the final-scalar same-object weld.
------------------------------------------------------------------------

record FinalPoleNearLiteralKernel
    (S : NearFar.OrderedAdditiveNearFarSurface) : Set₁ where
  private
    Scalar = NearFar.Scalar S
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

    literalFiniteNearValue : Scalar
    literalFiniteNearValueIsSum :
      literalFiniteNearValue ≡ finiteNearSum cellResponse

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

open FinalPoleNearLiteralKernel public

------------------------------------------------------------------------
-- Carrier-neutral signed evaluation -> literal kernel + final scalar weld.
--
-- This is deliberately window-free.  It exposes the exact remaining same-object
-- obligations rather than smuggling in the selected explicit-formula producer.
------------------------------------------------------------------------

record WindowFreeFiniteNearFinalAttachment
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport)
    (kernel : FinalPoleNearLiteralKernel S)
    (finite : Eval.FiniteNearProducer) : Set₁ where
  private
    evaluation = Eval.FiniteNearProducer.evaluation finite
  field
    evaluationScalarIdentity :
      Eval.SignedFiniteNearEvaluationSurface.Scalar evaluation
      ≡ NearFar.Scalar S

    signedEvaluationIsLiteralFiniteNear :
      cast evaluationScalarIdentity
        (Eval.SignedFiniteNearEvaluationSurface.signedNearValue evaluation)
      ≡ literalFiniteNearValue kernel

    signedEvaluationIsFinalNearResponse :
      cast evaluationScalarIdentity
        (Eval.SignedFiniteNearEvaluationSurface.signedNearValue evaluation)
      ≡ Transport.nearResponseAt transport (Direct.chosenCutoff offInput)

    attachmentReference : String

open WindowFreeFiniteNearFinalAttachment public

------------------------------------------------------------------------
-- Mechanical compilation to the existing final observer model.
------------------------------------------------------------------------

compileWindowFreeFinalLiteralModel :
  forall {S transport} ->
  (offInput : Direct.DirectLiteralOffTargetInput S transport) ->
  (kernel : FinalPoleNearLiteralKernel S) ->
  (finite : Eval.FiniteNearProducer) ->
  WindowFreeFiniteNearFinalAttachment offInput kernel finite ->
  Final.FinalPoleNearLiteralModel offInput
compileWindowFreeFinalLiteralModel offInput kernel finite attachment = record
  { Final.ZeroIndex = ZeroIndex kernel
  ; Final.nearIndex = nearIndex kernel
  ; Final.multiplicity = multiplicity kernel
  ; Final.horizontalDisplacement = horizontalDisplacement kernel
  ; Final.ordinate = ordinate kernel
  ; Final.target = target kernel
  ; Final.subtract = subtract kernel
  ; Final.targetRelativeGap = targetRelativeGap kernel
  ; Final.targetRelativeGapIsOrdinateMinusTarget =
      targetRelativeGapIsOrdinateMinusTarget kernel
  ; Final.four = four kernel
  ; Final.mul = mul kernel
  ; Final.cosh = cosh kernel
  ; Final.cos = cos kernel
  ; Final.poleTaperValue = poleTaperValue kernel
  ; Final.integrate = integrate kernel
  ; Final.finiteNearSum = finiteNearSum kernel
  ; Final.cellResponse = cellResponse kernel
  ; Final.cellResponseIsLiteralReflectionPair =
      cellResponseIsLiteralReflectionPair kernel
  ; Final.literalFiniteNearValue = literalFiniteNearValue kernel
  ; Final.literalFiniteNearValueIsSum = literalFiniteNearValueIsSum kernel
  ; Final.finalNearResponseIsLiteralFiniteNear =
      trans
        (sym (signedEvaluationIsFinalNearResponse attachment))
        (signedEvaluationIsLiteralFiniteNear attachment)
  ; Final.exactNearIndexIsCheckedNearOffFinset =
      exactNearIndexIsCheckedNearOffFinset kernel
  ; Final.exactNearIndexIsCheckedNearOffFinsetReceipt =
      exactNearIndexIsCheckedNearOffFinsetReceipt kernel
  ; Final.exactMultiplicityIsZetaMultiplicity =
      exactMultiplicityIsZetaMultiplicity kernel
  ; Final.exactMultiplicityIsZetaMultiplicityReceipt =
      exactMultiplicityIsZetaMultiplicityReceipt kernel
  ; Final.exactHorizontalDisplacementIsOffLineRealPart =
      exactHorizontalDisplacementIsOffLineRealPart kernel
  ; Final.exactHorizontalDisplacementIsOffLineRealPartReceipt =
      exactHorizontalDisplacementIsOffLineRealPartReceipt kernel
  ; Final.exactPoleTaperIsFinalUniversalPoleQuotientTaper =
      exactPoleTaperIsFinalUniversalPoleQuotientTaper kernel
  ; Final.exactPoleTaperIsFinalUniversalPoleQuotientTaperReceipt =
      exactPoleTaperIsFinalUniversalPoleQuotientTaperReceipt kernel
  ; Final.reflectionPairAlreadyCancelsOddHeightChannel =
      reflectionPairAlreadyCancelsOddHeightChannel kernel
  ; Final.reflectionPairAlreadyCancelsOddHeightChannelReceipt =
      reflectionPairAlreadyCancelsOddHeightChannelReceipt kernel
  ; Final.modelReference = attachmentReference attachment
  }

------------------------------------------------------------------------
-- Boundary / scheduler facts.
------------------------------------------------------------------------

record WindowFreeFiniteNearFinalBoundary : Set where
  constructor window-free-finite-near-final-boundary
  field
    explicitTargetWindowRequiredForDirectSameObjectWeld : Bool
    explicitTargetWindowRequiredForDirectSameObjectWeldIsFalse :
      explicitTargetWindowRequiredForDirectSameObjectWeld ≡ false

    determinantDirectConsumerRequired : Bool
    determinantDirectConsumerRequiredIsFalse :
      determinantDirectConsumerRequired ≡ false

    literalKernelAndFinalScalarWeldAreDistinctDebts : Bool
    literalKernelAndFinalScalarWeldAreDistinctDebtsIsTrue :
      literalKernelAndFinalScalarWeldAreDistinctDebts ≡ true

    carrierNeutralFiniteProducerAloneBuildsLiteralKernel : Bool
    carrierNeutralFiniteProducerAloneBuildsLiteralKernelIsFalse :
      carrierNeutralFiniteProducerAloneBuildsLiteralKernel ≡ false

    carrierNeutralFiniteProducerAloneIdentifiesFinalNearScalar : Bool
    carrierNeutralFiniteProducerAloneIdentifiesFinalNearScalarIsFalse :
      carrierNeutralFiniteProducerAloneIdentifiesFinalNearScalar ≡ false

    kernelPlusTwoSameObjectEqualitiesCompileFinalLiteralModel : Bool
    kernelPlusTwoSameObjectEqualitiesCompileFinalLiteralModelIsTrue :
      kernelPlusTwoSameObjectEqualitiesCompileFinalLiteralModel ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    nextDirectRepresentationTarget : String

canonicalWindowFreeFiniteNearFinalBoundary :
  WindowFreeFiniteNearFinalBoundary
canonicalWindowFreeFiniteNearFinalBoundary =
  window-free-finite-near-final-boundary
    false refl
    false refl
    true refl
    false refl
    false refl
    true refl
    false refl
    "Recover a literal universal-pole-quotient kernel realization and a window-free same-object attachment for one carrier-neutral FiniteNearProducer: its signedNearValue must be identified both with that literal finite sum and with final nearResponseAt(chosen J). These are representation/same-object debts, not the post-crossing signed inequality. Once supplied, the existing FinalPoleNearLiteralModel is compiler output; no ActualSelectedPoleNearProducer or determinant-q payment is required."
