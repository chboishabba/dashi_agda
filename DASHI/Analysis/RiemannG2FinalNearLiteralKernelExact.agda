module DASHI.Analysis.RiemannG2FinalNearLiteralKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Final
import DASHI.Analysis.RiemannG2ProofRelevantTargetTranslationModulationExact as Phase
import DASHI.Analysis.RiemannAristotleFiniteNearSchurKernelCovarianceTargetExact as Reflection

record FinalNearLiteralKernel
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport) : Set₁ where
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
    finalNearResponseIsLiteralFiniteSum :
      Transport.nearResponseAt transport (Direct.chosenCutoff offInput)
      ≡ finiteNearSum cellResponse
    exactNearIndexIsCheckedNearOffFinset : Set
    exactNearIndexIsCheckedNearOffFinsetReceipt : exactNearIndexIsCheckedNearOffFinset
    exactMultiplicityIsZetaMultiplicity : Set
    exactMultiplicityIsZetaMultiplicityReceipt : exactMultiplicityIsZetaMultiplicity
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

open FinalNearLiteralKernel public

record FinalNearCheckedScalarAttachment
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport) : Set where
  field
    attachmentCheckedNearScalar : NearFar.Scalar S
    finalNearResponseIsAttachmentCheckedScalar :
      Transport.nearResponseAt transport (Direct.chosenCutoff offInput)
      ≡ attachmentCheckedNearScalar

open FinalNearCheckedScalarAttachment public

record CheckedScalarLiteralFoldIdentification
    {S : NearFar.OrderedAdditiveNearFarSurface}
    (checkedNearScalar literalFiniteNearValue : NearFar.Scalar S) : Set where
  field
    identifiedCheckedScalarIsLiteralFiniteNearValue :
      checkedNearScalar ≡ literalFiniteNearValue

open CheckedScalarLiteralFoldIdentification public

------------------------------------------------------------------------
-- Least-privilege refinement of R1b.
--
-- The retained Lean source separately names the reflection-paired scalar formula,
-- while the final Agda consumer needs the finite fold of literal cells.  Keep
-- those identities distinct so source recovery can pay either edge without
-- manufacturing the other:
--
--   checked scalar = literal reflection-pair scalar = finite cell fold.
------------------------------------------------------------------------

record CheckedScalarLiteralReflectionPairIdentification
    {S : NearFar.OrderedAdditiveNearFarSurface}
    (checkedNearScalar literalReflectionPairScalar : NearFar.Scalar S) : Set where
  field
    identifiedCheckedScalarIsLiteralReflectionPairScalar :
      checkedNearScalar ≡ literalReflectionPairScalar

open CheckedScalarLiteralReflectionPairIdentification public

record LiteralReflectionPairFiniteFoldIdentification
    {S : NearFar.OrderedAdditiveNearFarSurface}
    (literalReflectionPairScalar literalFiniteNearValue : NearFar.Scalar S) : Set where
  field
    identifiedLiteralReflectionPairScalarIsFiniteFold :
      literalReflectionPairScalar ≡ literalFiniteNearValue

open LiteralReflectionPairFiniteFoldIdentification public

compileCheckedScalarLiteralFoldIdentificationFromReflectionPairSplit :
  forall {S} ->
  {checkedNearScalar literalReflectionPairScalar literalFiniteNearValue : NearFar.Scalar S} ->
  CheckedScalarLiteralReflectionPairIdentification
    checkedNearScalar literalReflectionPairScalar ->
  LiteralReflectionPairFiniteFoldIdentification
    literalReflectionPairScalar literalFiniteNearValue ->
  CheckedScalarLiteralFoldIdentification checkedNearScalar literalFiniteNearValue
compileCheckedScalarLiteralFoldIdentificationFromReflectionPairSplit
    checkedToReflection reflectionToFold = record
  { identifiedCheckedScalarIsLiteralFiniteNearValue =
      trans
        (identifiedCheckedScalarIsLiteralReflectionPairScalar checkedToReflection)
        (identifiedLiteralReflectionPairScalarIsFiniteFold reflectionToFold)
  }

record FinalNearCheckedScalarBridge
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport)
    (literalFiniteNearValue : NearFar.Scalar S) : Set where
  field
    checkedNearScalar : NearFar.Scalar S
    finalNearResponseIsCheckedNearScalar :
      Transport.nearResponseAt transport (Direct.chosenCutoff offInput)
      ≡ checkedNearScalar
    checkedNearScalarIsLiteralFiniteNearValue :
      checkedNearScalar ≡ literalFiniteNearValue

open FinalNearCheckedScalarBridge public

compileFinalNearCheckedScalarBridge :
  forall {S transport} ->
  (offInput : Direct.DirectLiteralOffTargetInput S transport) ->
  {literalFiniteNearValue : NearFar.Scalar S} ->
  (attachment : FinalNearCheckedScalarAttachment offInput) ->
  CheckedScalarLiteralFoldIdentification
    (attachmentCheckedNearScalar attachment)
    literalFiniteNearValue ->
  FinalNearCheckedScalarBridge offInput literalFiniteNearValue
compileFinalNearCheckedScalarBridge offInput attachment identification = record
  { checkedNearScalar = attachmentCheckedNearScalar attachment
  ; finalNearResponseIsCheckedNearScalar =
      finalNearResponseIsAttachmentCheckedScalar attachment
  ; checkedNearScalarIsLiteralFiniteNearValue =
      identifiedCheckedScalarIsLiteralFiniteNearValue identification
  }

compileFinalNearRepresentationEquality :
  forall {S transport} ->
  (offInput : Direct.DirectLiteralOffTargetInput S transport) ->
  {literalFiniteNearValue : NearFar.Scalar S} ->
  FinalNearCheckedScalarBridge offInput literalFiniteNearValue ->
  Transport.nearResponseAt transport (Direct.chosenCutoff offInput)
  ≡ literalFiniteNearValue
compileFinalNearRepresentationEquality offInput bridge =
  trans
    (finalNearResponseIsCheckedNearScalar bridge)
    (checkedNearScalarIsLiteralFiniteNearValue bridge)

compileFinalNearRepresentationEqualityFromSplit :
  forall {S transport} ->
  (offInput : Direct.DirectLiteralOffTargetInput S transport) ->
  {literalFiniteNearValue : NearFar.Scalar S} ->
  (attachment : FinalNearCheckedScalarAttachment offInput) ->
  CheckedScalarLiteralFoldIdentification
    (attachmentCheckedNearScalar attachment)
    literalFiniteNearValue ->
  Transport.nearResponseAt transport (Direct.chosenCutoff offInput)
  ≡ literalFiniteNearValue
compileFinalNearRepresentationEqualityFromSplit offInput attachment identification =
  compileFinalNearRepresentationEquality offInput
    (compileFinalNearCheckedScalarBridge offInput attachment identification)

genericTargetGapCosineCompilerClosedReceipt :
  Phase.ProofRelevantTranslationModulationBoundary.targetGapCosineCompilerClosed
    Phase.canonicalProofRelevantTranslationModulationBoundary ≡ true
genericTargetGapCosineCompilerClosedReceipt = refl

reflectionPairLiteralFormulaSourceOwnedReceipt :
  Reflection.FiniteNearSchurKernelCovarianceTarget.rawPairKernelFormulaOwnedInLean
    Reflection.canonicalFiniteNearSchurKernelCovarianceTarget ≡ true
reflectionPairLiteralFormulaSourceOwnedReceipt = refl

compileFinalPoleNearLiteralModel :
  forall {S transport} ->
  (offInput : Direct.DirectLiteralOffTargetInput S transport) ->
  FinalNearLiteralKernel offInput ->
  Final.FinalPoleNearLiteralModel offInput
compileFinalPoleNearLiteralModel offInput kernel = record
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
  ; Final.literalFiniteNearValue = finiteNearSum kernel (cellResponse kernel)
  ; Final.literalFiniteNearValueIsSum = refl
  ; Final.finalNearResponseIsLiteralFiniteNear =
      finalNearResponseIsLiteralFiniteSum kernel
  ; Final.exactNearIndexIsCheckedNearOffFinset = exactNearIndexIsCheckedNearOffFinset kernel
  ; Final.exactNearIndexIsCheckedNearOffFinsetReceipt = exactNearIndexIsCheckedNearOffFinsetReceipt kernel
  ; Final.exactMultiplicityIsZetaMultiplicity = exactMultiplicityIsZetaMultiplicity kernel
  ; Final.exactMultiplicityIsZetaMultiplicityReceipt = exactMultiplicityIsZetaMultiplicityReceipt kernel
  ; Final.exactHorizontalDisplacementIsOffLineRealPart = exactHorizontalDisplacementIsOffLineRealPart kernel
  ; Final.exactHorizontalDisplacementIsOffLineRealPartReceipt = exactHorizontalDisplacementIsOffLineRealPartReceipt kernel
  ; Final.exactPoleTaperIsFinalUniversalPoleQuotientTaper = exactPoleTaperIsFinalUniversalPoleQuotientTaper kernel
  ; Final.exactPoleTaperIsFinalUniversalPoleQuotientTaperReceipt = exactPoleTaperIsFinalUniversalPoleQuotientTaperReceipt kernel
  ; Final.reflectionPairAlreadyCancelsOddHeightChannel = reflectionPairAlreadyCancelsOddHeightChannel kernel
  ; Final.reflectionPairAlreadyCancelsOddHeightChannelReceipt = reflectionPairAlreadyCancelsOddHeightChannelReceipt kernel
  ; Final.modelReference = kernelReference kernel
  }

record FinalNearLiteralKernelBoundary : Set where
  constructor final-near-literal-kernel-boundary
  field
    evaluatorRequiredToStateLiteralKernel : Bool
    evaluatorRequiredToStateLiteralKernelIsFalse : evaluatorRequiredToStateLiteralKernel ≡ false
    oneFinalNearToLiteralSumEqualityRequired : Bool
    oneFinalNearToLiteralSumEqualityRequiredIsTrue : oneFinalNearToLiteralSumEqualityRequired ≡ true
    existingFinalObserverModelIsCompilerOutput : Bool
    existingFinalObserverModelIsCompilerOutputIsTrue : existingFinalObserverModelIsCompilerOutput ≡ true
    selectedWeilWindowRequired : Bool
    selectedWeilWindowRequiredIsFalse : selectedWeilWindowRequired ≡ false
    determinantConsumerRequired : Bool
    determinantConsumerRequiredIsFalse : determinantConsumerRequired ≡ false
    genericTargetGapCosineLawClosed : Bool
    genericTargetGapCosineLawClosedIsTrue : genericTargetGapCosineLawClosed ≡ true
    reflectionPairLiteralFormulaSourceOwned : Bool
    reflectionPairLiteralFormulaSourceOwnedIsTrue : reflectionPairLiteralFormulaSourceOwned ≡ true
    actualUniversalPoleQuotientPhaseRealizationInhabited : Bool
    actualUniversalPoleQuotientPhaseRealizationInhabitedIsFalse : actualUniversalPoleQuotientPhaseRealizationInhabited ≡ false
    checkedNearScalarBridgeInhabited : Bool
    checkedNearScalarBridgeInhabitedIsFalse : checkedNearScalarBridgeInhabited ≡ false
    r1aCheckedScalarAttachmentInhabited : Bool
    r1aCheckedScalarAttachmentInhabitedIsFalse : r1aCheckedScalarAttachmentInhabited ≡ false
    r1bLiteralFoldIdentificationInhabited : Bool
    r1bLiteralFoldIdentificationInhabitedIsFalse : r1bLiteralFoldIdentificationInhabited ≡ false
    r1b1CheckedScalarReflectionPairIdentificationInhabited : Bool
    r1b1CheckedScalarReflectionPairIdentificationInhabitedIsFalse :
      r1b1CheckedScalarReflectionPairIdentificationInhabited ≡ false
    r1b2ReflectionPairFiniteFoldIdentificationInhabited : Bool
    r1b2ReflectionPairFiniteFoldIdentificationInhabitedIsFalse :
      r1b2ReflectionPairFiniteFoldIdentificationInhabited ≡ false
    statusReceiptPaysR1Equality : Bool
    statusReceiptPaysR1EqualityIsFalse : statusReceiptPaysR1Equality ≡ false
    analyticClusterMarginPaidHere : Bool
    analyticClusterMarginPaidHereIsFalse : analyticClusterMarginPaidHere ≡ false
    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false
    highestAlphaReading : String

canonicalFinalNearLiteralKernelBoundary : FinalNearLiteralKernelBoundary
canonicalFinalNearLiteralKernelBoundary =
  final-near-literal-kernel-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "R1 is evaluator-independent. R1a attaches final nearResponseAt(chosen J) to one checked/imported finite-near scalar. R1b is now factored further: R1b1 identifies that checked scalar with the literal reflection-pair scalar on the final universal pole-quotient carrier; R1b2 identifies the SAME reflection-pair scalar with the literal finite cell fold. The retained Lean reflection-pair theorem is source ownership only in the current return, so it does not inhabit R1b1; generic phase algebra does not inhabit the final pole-quotient carrier either. R1b compiles from R1b1+R1b2, and final R1 compiles from R1a+R1b. Certificates remain downstream; no strict ClusterResponse inequality or RH is proved here."
