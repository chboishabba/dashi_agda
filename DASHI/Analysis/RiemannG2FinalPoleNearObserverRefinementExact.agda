module DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact as Historical

------------------------------------------------------------------------
-- INTROSPECTIVE REFINEMENT OF THE FINAL POLE-NEAR OBSERVER
--
-- The current direct one-leaf consumer sees only the scalar
--
--   nearResponseAt J.
--
-- That is sufficient as an endpoint type, but it hides exactly the coordinate
-- needed by every surviving cancellation route: target-relative phase on the
-- literal finite near-zero family.  The checked cutoff return records
-- `sameFiniteNearCarrier` only as an opaque Set receipt, so it cannot by itself
-- expose the literal summands to an Agda harmonic-analysis consumer.
--
-- This owner adds the smallest refinement that separates the two states the
-- final consumer cares about.  It does NOT require a Weil target-window test,
-- a second explicit-formula decomposition, or a determinant-q consumer.  It
-- simply identifies the FINAL near scalar with a literal finite aggregation
-- whose reflection-paired cells expose multiplicity, horizontal displacement
-- and target-relative gap.
------------------------------------------------------------------------

record FinalPoleNearLiteralModel
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport) : Set₁ where
  private
    Scalar = NearFar.Scalar S
  field
    ZeroIndex : Set

    -- Literal coordinates of the finite near family.
    nearIndex : ZeroIndex -> Set
    multiplicity : ZeroIndex -> Scalar
    horizontalDisplacement : ZeroIndex -> Scalar
    targetRelativeGap : ZeroIndex -> Scalar

    -- Only the operations used by the reflection-paired target-centred kernel
    -- are exposed.  No unrelated analytic structure is required here.
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

    -- This is the decisive observer refinement: the scalar consumed by the
    -- canonical one-leaf Off target is exactly the literal phase-visible sum.
    finalNearResponseIsLiteralFiniteNear :
      Transport.nearResponseAt transport (Direct.chosenCutoff offInput)
      ≡ literalFiniteNearValue

    exactNearIndexIsCheckedNearOffFinset : Set
    exactNearIndexIsCheckedNearOffFinsetReceipt :
      exactNearIndexIsCheckedNearOffFinset

    exactMultiplicityIsZetaMultiplicity : Set
    exactMultiplicityIsZetaMultiplicityReceipt :
      exactMultiplicityIsZetaMultiplicity

    exactGapIsOrdinateMinusTarget : Set
    exactGapIsOrdinateMinusTargetReceipt :
      exactGapIsOrdinateMinusTarget

    exactHorizontalDisplacementIsOffLineRealPart : Set
    exactHorizontalDisplacementIsOffLineRealPartReceipt :
      exactHorizontalDisplacementIsOffLineRealPart

    exactPoleTaperIsFinalUniversalPoleQuotientTaper : Set
    exactPoleTaperIsFinalUniversalPoleQuotientTaperReceipt :
      exactPoleTaperIsFinalUniversalPoleQuotientTaper

    reflectionPairAlreadyCancelsOddHeightChannel : Set
    reflectionPairAlreadyCancelsOddHeightChannelReceipt :
      reflectionPairAlreadyCancelsOddHeightChannel

    modelReference : String

open FinalPoleNearLiteralModel public

------------------------------------------------------------------------
-- The literal model is an observer refinement, not an analytic payment.
------------------------------------------------------------------------

data LiteralNearModelPaysJointMargin : Set where

data CoarseCountEnvelopePaysJointMargin : Set where

literalNearModelDoesNotPayJointMargin :
  LiteralNearModelPaysJointMargin -> ⊥
literalNearModelDoesNotPayJointMargin ()

coarseCountEnvelopeDoesNotPayJointMargin :
  CoarseCountEnvelopePaysJointMargin -> ⊥
coarseCountEnvelopeDoesNotPayJointMargin ()

------------------------------------------------------------------------
-- Existing collision witness reused directly.
--
-- The historical owner already proves that two cells can have the same
-- multiplicity and absolute envelope while their signed contributions have
-- opposite sign.  Reuse the collision itself here; do not duplicate its
-- rational arithmetic in the final-carrier observer module.
------------------------------------------------------------------------

coarseObserverCollisionAlreadyOwned :
  Historical.sameCoarseObservation
    Historical.positivePhaseCell
    Historical.negativePhaseCell
coarseObserverCollisionAlreadyOwned = Historical.sameCountAndEnvelope

------------------------------------------------------------------------
-- Search classification.
------------------------------------------------------------------------

data FinalNearObservationCoordinate : Set where
  scalarNearResponseOnly : FinalNearObservationCoordinate
  countAndAbsoluteEnvelope : FinalNearObservationCoordinate
  literalTargetRelativePhase : FinalNearObservationCoordinate
  fullWeilTargetWindow : FinalNearObservationCoordinate
  jointComplementPayment : FinalNearObservationCoordinate


data CoordinateState : Set where
  inadequateObserver : CoordinateState
  requiredRefinement : CoordinateState
  optionalStrongerRefinement : CoordinateState
  analyticPayment : CoordinateState

coordinateState : FinalNearObservationCoordinate -> CoordinateState
coordinateState scalarNearResponseOnly = inadequateObserver
coordinateState countAndAbsoluteEnvelope = inadequateObserver
coordinateState literalTargetRelativePhase = requiredRefinement
coordinateState fullWeilTargetWindow = optionalStrongerRefinement
coordinateState jointComplementPayment = analyticPayment

record FinalPoleNearObserverRefinementBoundary : Set where
  constructor final-pole-near-observer-refinement-boundary
  field
    finalNearScalarAloneExposesCancellationCoordinates : Bool
    finalNearScalarAloneExposesCancellationCoordinatesIsFalse :
      finalNearScalarAloneExposesCancellationCoordinates ≡ false

    countAndAbsoluteEnvelopeSufficientForSignedResponse : Bool
    countAndAbsoluteEnvelopeSufficientForSignedResponseIsFalse :
      countAndAbsoluteEnvelopeSufficientForSignedResponse ≡ false

    targetRelativePhaseIsFirstMissingCoordinate : Bool
    targetRelativePhaseIsFirstMissingCoordinateIsTrue :
      targetRelativePhaseIsFirstMissingCoordinate ≡ true

    finalNearResponseNeedsProofRelevantLiteralIdentification : Bool
    finalNearResponseNeedsProofRelevantLiteralIdentificationIsTrue :
      finalNearResponseNeedsProofRelevantLiteralIdentification ≡ true

    fullWeilTargetWindowIsPrimitiveRequirementOfOneLeafConsumer : Bool
    fullWeilTargetWindowIsPrimitiveRequirementOfOneLeafConsumerIsFalse :
      fullWeilTargetWindowIsPrimitiveRequirementOfOneLeafConsumer ≡ false

    literalModelAutomaticallyPaysJointMargin : Bool
    literalModelAutomaticallyPaysJointMarginIsFalse :
      literalModelAutomaticallyPaysJointMargin ≡ false

    existingCoarseCollisionWitnessReused : Bool
    existingCoarseCollisionWitnessReusedIsTrue :
      existingCoarseCollisionWitnessReused ≡ true

    literalFinalModelInhabitedHere : Bool
    literalFinalModelInhabitedHereIsFalse :
      literalFinalModelInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalFinalPoleNearObserverRefinementBoundary :
  FinalPoleNearObserverRefinementBoundary
canonicalFinalPoleNearObserverRefinementBoundary =
  final-pole-near-observer-refinement-boundary
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl
    "The introspective collision is now localized inside the one-leaf high theorem. The final transport exposes nearResponseAt(J) only as a scalar, while count/envelope data provably identify cells with opposite signed contributions. The first missing observation coordinate is therefore a proof-relevant same-object model exposing the literal target-relative phase, multiplicity, near family and reflection-paired kernel whose finite sum equals that exact final nearResponseAt(J). A full Weil target-window object is stronger than the primitive one-leaf consumer requires. Supplying this literal model enables phase-sensitive analysis but does not itself prove the joint complement margin or RH."
