module DASHI.Core.TwoChannelAllowanceCompositionExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- GENERIC TWO-CHANNEL ALLOWANCE COMPOSITION
--
-- Many DASHI consumers split one terminal quantity into two independently
-- bounded channels.  The proof shape does not belong to any one physical or
-- analytic domain:
--
--   x <= X
--   y <= Y
--   --------
--   x + y <= X + Y
--
-- and, more specifically, an intermediate allowance may reserve room for the
-- second channel:
--
--   X <= X
--   Y <= epsilon
--   X + epsilon <= A
--   -----------------
--   X + Y <= A.
--
-- The surface is intentionally weaker than a preorder.  Reflexivity is NOT a
-- global field.  Applications that need X <= X must pay that concrete receipt.
------------------------------------------------------------------------

record OrderedAdditiveTwoChannelSurface : Set₁ where
  constructor ordered-additive-two-channel-surface
  field
    Scalar : Set
    _<=_ : Scalar -> Scalar -> Set
    add : Scalar -> Scalar -> Scalar

    <=-trans :
      forall {a b c} -> _<=_ a b -> _<=_ b c -> _<=_ a c

    addMonotone :
      forall {a a' b b'} ->
      _<=_ a a' ->
      _<=_ b b' ->
      _<=_ (add a b) (add a' b')

open OrderedAdditiveTwoChannelSurface public

record TwoChannelEnvelope
    (S : OrderedAdditiveTwoChannelSurface) : Set where
  constructor two-channel-envelope
  field
    firstValue secondValue : Scalar S
    firstEnvelope secondEnvelope : Scalar S

    firstBound : _<=_ S firstValue firstEnvelope
    secondBound : _<=_ S secondValue secondEnvelope

open TwoChannelEnvelope public

combinedEnvelopeBound :
  (S : OrderedAdditiveTwoChannelSurface) ->
  (d : TwoChannelEnvelope S) ->
  _<=_ S
    (add S (firstValue d) (secondValue d))
    (add S (firstEnvelope d) (secondEnvelope d))
combinedEnvelopeBound S d =
  addMonotone S (firstBound d) (secondBound d)

record IntermediateAllowanceFit
    (S : OrderedAdditiveTwoChannelSurface)
    (firstEnvelope secondEnvelope assigned : Scalar S) : Set where
  constructor intermediate-allowance-fit
  field
    intermediateAllowance : Scalar S

    firstEnvelopeSelfOrder :
      _<=_ S firstEnvelope firstEnvelope

    secondEnvelopeBelowIntermediate :
      _<=_ S secondEnvelope intermediateAllowance

    firstPlusIntermediateBelowAssigned :
      _<=_ S
        (add S firstEnvelope intermediateAllowance)
        assigned

open IntermediateAllowanceFit public

combinedEnvelopeBelowAssigned :
  (S : OrderedAdditiveTwoChannelSurface) ->
  (firstEnvelope secondEnvelope assigned : Scalar S) ->
  IntermediateAllowanceFit S firstEnvelope secondEnvelope assigned ->
  _<=_ S
    (add S firstEnvelope secondEnvelope)
    assigned
combinedEnvelopeBelowAssigned S firstEnvelope secondEnvelope assigned fit =
  <=-trans S
    (addMonotone S
      (firstEnvelopeSelfOrder fit)
      (secondEnvelopeBelowIntermediate fit))
    (firstPlusIntermediateBelowAssigned fit)

------------------------------------------------------------------------
-- Boundary: this owner performs only order/addition composition.  It never
-- chooses an allowance, proves channel estimates, or manufactures reflexivity.
------------------------------------------------------------------------

record TwoChannelAllowanceBoundary : Set where
  constructor two-channel-allowance-boundary
  field
    channelwiseBoundsCompose : Bool
    channelwiseBoundsComposeIsTrue : channelwiseBoundsCompose ≡ true

    intermediateAllowanceCompositionOwned : Bool
    intermediateAllowanceCompositionOwnedIsTrue :
      intermediateAllowanceCompositionOwned ≡ true

    globalReflexivityRequired : Bool
    globalReflexivityRequiredIsFalse : globalReflexivityRequired ≡ false

    compilerChoosesIntermediateAllowance : Bool
    compilerChoosesIntermediateAllowanceIsFalse :
      compilerChoosesIntermediateAllowance ≡ false

    compilerCreatesChannelEstimate : Bool
    compilerCreatesChannelEstimateIsFalse :
      compilerCreatesChannelEstimate ≡ false

canonicalTwoChannelAllowanceBoundary : TwoChannelAllowanceBoundary
canonicalTwoChannelAllowanceBoundary =
  two-channel-allowance-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
