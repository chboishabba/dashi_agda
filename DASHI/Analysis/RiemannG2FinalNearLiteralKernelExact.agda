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
    false refl
    false refl
    "Representation is evaluator-independent. The final R1 equality may be acquired directly or factored through one checked/imported near scalar: first identify final nearResponseAt(chosen J) with that scalar, then identify the same scalar with the literal finite cell fold. The bridge composes those same-object equalities only; it does not manufacture either one. Numerical/symbolic certificates remain downstream, no selected Weil window or determinant consumer is required, and no strict ClusterResponse inequality or RH is proved here."
