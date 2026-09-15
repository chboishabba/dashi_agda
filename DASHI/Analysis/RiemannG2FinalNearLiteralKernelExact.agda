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

------------------------------------------------------------------------
-- EVALUATOR-INDEPENDENT FINAL LITERAL NEAR KERNEL
--
-- Representation owns the literal finite kernel and the one decisive equality
--
--   nearResponseAt(chosen J) = finiteNearSum(cellResponse).
--
-- No numerical/symbolic evaluator is an input.  A proof-carrying evaluator may
-- consume this representation downstream.  This avoids the ownership cycle
-- kernel -> evaluator -> certificate -> kernel.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- CROSS-PROVER REPRESENTATION FACTORIZATION
--
-- The checked Lean return and the final literal kernel currently meet at one
-- representation equality.  For acquisition and transport work it is useful to
-- expose the least same-object factorization of that equality without changing
-- the final consumer:
--
--   final nearResponseAt(chosen J)
--      = checked/imported finite-near scalar
--      = literal finite cell fold.
--
-- Neither equality is manufactured here.  The first is the cross-prover
-- same-carrier transport; the second is the literal-summand/fold identification.
-- Once both are supplied, the final R1 equality is compiler output by transitivity.
------------------------------------------------------------------------

record FinalNearCheckedScalarAttachment
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport) : Set where
  field
    checkedNearScalar : NearFar.Scalar S
    finalNearResponseIsCheckedNearScalar :
      Transport.nearResponseAt transport (Direct.chosenCutoff offInput)
      ≡ checkedNearScalar

open FinalNearCheckedScalarAttachment public

record CheckedScalarLiteralFoldIdentification
    {S : NearFar.OrderedAdditiveNearFarSurface}
    (checkedNearScalar literalFiniteNearValue : NearFar.Scalar S) : Set where
  field
    checkedNearScalarIsLiteralFiniteNearValue :
      checkedNearScalar ≡ literalFiniteNearValue

open CheckedScalarLiteralFoldIdentification public

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
    (FinalNearCheckedScalarAttachment.checkedNearScalar attachment)
    literalFiniteNearValue ->
  FinalNearCheckedScalarBridge offInput literalFiniteNearValue
compileFinalNearCheckedScalarBridge offInput attachment identification = record
  { FinalNearCheckedScalarBridge.checkedNearScalar =
      FinalNearCheckedScalarAttachment.checkedNearScalar attachment
  ; FinalNearCheckedScalarBridge.finalNearResponseIsCheckedNearScalar =
      FinalNearCheckedScalarAttachment.finalNearResponseIsCheckedNearScalar attachment
  ; FinalNearCheckedScalarBridge.checkedNearScalarIsLiteralFiniteNearValue =
      CheckedScalarLiteralFoldIdentification.checkedNearScalarIsLiteralFiniteNearValue
        identification
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
    (FinalNearCheckedScalarBridge.finalNearResponseIsCheckedNearScalar bridge)
    (FinalNearCheckedScalarBridge.checkedNearScalarIsLiteralFiniteNearValue bridge)

compileFinalNearRepresentationEqualityFromSplit :
  forall {S transport} ->
  (offInput : Direct.DirectLiteralOffTargetInput S transport) ->
  {literalFiniteNearValue : NearFar.Scalar S} ->
  (attachment : FinalNearCheckedScalarAttachment offInput) ->
  CheckedScalarLiteralFoldIdentification
    (FinalNearCheckedScalarAttachment.checkedNearScalar attachment)
    literalFiniteNearValue ->
  Transport.nearResponseAt transport (Direct.chosenCutoff offInput)
  ≡ literalFiniteNearValue
compileFinalNearRepresentationEqualityFromSplit offInput attachment identification =
  compileFinalNearRepresentationEquality offInput
    (compileFinalNearCheckedScalarBridge offInput attachment identification)

------------------------------------------------------------------------
-- R1 SOURCE/TRANSPORT AUDIT
--
-- Repo archaeology separates three facts that must not be collapsed:
--
--   1. generic target-gap / even-projection algebra is proof-bearing in Agda;
--   2. a Lean source owner names the literal reflection-pair 4*g*cosh*cos
--      formula on the zeta carrier;
--   3. neither fact instantiates the actual universal pole-quotient phase
--      carrier or transports the checked finite-near scalar into this Agda
--      final carrier.
--
-- R1a and R1b are now separately inhabitable theorem obligations:
--
--   R1a  final nearResponseAt(chosen J) = checked/imported scalar
--   R1b  checked/imported scalar = literal finite cell fold
--
-- The booleans below are deliberately fail-closed acquisition status.  They do
-- not replace either theorem-bearing obligation.
------------------------------------------------------------------------

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
  ; Final.modelReference = kernelReference kernel
  }

record FinalNearLiteralKernelBoundary : Set where
  constructor final-near-literal-kernel-boundary
  field
    evaluatorRequiredToStateLiteralKernel : Bool
    evaluatorRequiredToStateLiteralKernelIsFalse :
      evaluatorRequiredToStateLiteralKernel ≡ false

    oneFinalNearToLiteralSumEqualityRequired : Bool
    oneFinalNearToLiteralSumEqualityRequiredIsTrue :
      oneFinalNearToLiteralSumEqualityRequired ≡ true

    existingFinalObserverModelIsCompilerOutput : Bool
    existingFinalObserverModelIsCompilerOutputIsTrue :
      existingFinalObserverModelIsCompilerOutput ≡ true

    selectedWeilWindowRequired : Bool
    selectedWeilWindowRequiredIsFalse : selectedWeilWindowRequired ≡ false

    determinantConsumerRequired : Bool
    determinantConsumerRequiredIsFalse : determinantConsumerRequired ≡ false

    genericTargetGapCosineLawClosed : Bool
    genericTargetGapCosineLawClosedIsTrue :
      genericTargetGapCosineLawClosed ≡ true

    reflectionPairLiteralFormulaSourceOwned : Bool
    reflectionPairLiteralFormulaSourceOwnedIsTrue :
      reflectionPairLiteralFormulaSourceOwned ≡ true

    actualUniversalPoleQuotientPhaseRealizationInhabited : Bool
    actualUniversalPoleQuotientPhaseRealizationInhabitedIsFalse :
      actualUniversalPoleQuotientPhaseRealizationInhabited ≡ false

    checkedNearScalarBridgeInhabited : Bool
    checkedNearScalarBridgeInhabitedIsFalse :
      checkedNearScalarBridgeInhabited ≡ false

    statusReceiptPaysR1Equality : Bool
    statusReceiptPaysR1EqualityIsFalse :
      statusReceiptPaysR1Equality ≡ false

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
    "Representation is evaluator-independent. Generic target-gap/even-projection cosine algebra is already proof-bearing in Agda, and a Lean source owner names the literal reflection-pair 4*g*cosh*cos formula. Neither fact supplies the actual universal pole-quotient phase realization or the theorem-bearing checked-near-scalar transport. R1 may be acquired directly or as two independent theorem-bearing payments: R1a attaches final nearResponseAt(chosen J) to one checked/imported near scalar; R1b identifies that SAME checked scalar with the literal finite cell fold. The bundled bridge and final R1 equality are compiler output from R1a+R1b. Status Booleans and opaque same-carrier receipts pay neither equality. Numerical/symbolic certificates remain downstream, no selected Weil window or determinant consumer is required, and no strict ClusterResponse inequality or RH is proved here."
