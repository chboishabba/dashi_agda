module DASHI.Analysis.RiemannG2CommonC3DeterminantCovarianceCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.ThreeChannelC3EquivarianceGateExact as C3
import DASHI.Core.ConsumerRelativeSymmetryRelevanceExact as Symmetry
import DASHI.Analysis.RiemannAristotleG2eDeterminantTaperKernelExact as G2e
import DASHI.Analysis.RiemannG2DeterminantConsumerQuotient369Exact as Quotient
import DASHI.Analysis.RiemannAristotleTwoZeroThreeTaperReturnExact as ThreeTaper

------------------------------------------------------------------------
-- COMMON-C3 DETERMINANT COVARIANCE COMPILER
--
-- The finite 369 regression showed the correct algebraic symmetry shape:
-- rotate the two nuisance rows and the target/taper row together.  This module
-- packages the exact generic implication needed by RH without assuming that the
-- literal three-window construction already carries such an action.
------------------------------------------------------------------------

record CommonC3DeterminantGeometry : Set₁ where
  field
    Cell Scalar : Set
    action : C3.OrderThreeAction Cell
    determinant3 : Cell -> Cell -> Cell -> Scalar
    determinantCovariant :
      (a b c : Cell) ->
      determinant3
        (C3.rotate action a)
        (C3.rotate action b)
        (C3.rotate action c)
      ≡ determinant3 a b c

open CommonC3DeterminantGeometry public

record LiteralDeterminantOrbit (G : CommonC3DeterminantGeometry) : Set where
  field
    nuisanceOne nuisanceTwo : Cell G
    taperPoint : Cell G

open LiteralDeterminantOrbit public

q :
  (G : CommonC3DeterminantGeometry) ->
  LiteralDeterminantOrbit G ->
  Scalar G
q G orbit =
  determinant3 G
    (nuisanceOne orbit)
    (nuisanceTwo orbit)
    (taperPoint orbit)

rotateOrbit :
  (G : CommonC3DeterminantGeometry) ->
  LiteralDeterminantOrbit G ->
  LiteralDeterminantOrbit G
rotateOrbit G orbit = record
  { nuisanceOne = C3.rotate (action G) (nuisanceOne orbit)
  ; nuisanceTwo = C3.rotate (action G) (nuisanceTwo orbit)
  ; taperPoint = C3.rotate (action G) (taperPoint orbit)
  }

commonC3PreservesQ :
  (G : CommonC3DeterminantGeometry) ->
  (orbit : LiteralDeterminantOrbit G) ->
  q G (rotateOrbit G orbit) ≡ q G orbit
commonC3PreservesQ G orbit =
  determinantCovariant G
    (nuisanceOne orbit)
    (nuisanceTwo orbit)
    (taperPoint orbit)

------------------------------------------------------------------------
-- Once the literal G2e determinant observer is known to be preserved, the
-- fixed reflection-kernel consumer is invariant automatically.  This consumes
-- the canonical 369 consumer-relative symmetry theorem rather than rebuilding
-- it in the RH lane.
------------------------------------------------------------------------

g2eQPreservingActionMakesKernelConsumerInvariant :
  (A : G2e.DeterminantTaperAlgebra) ->
  (kernel : G2e.Scalar A) ->
  (act : G2e.Cell A -> G2e.Cell A) ->
  Symmetry.PreservesObserver (Quotient.determinantObserver A) act ->
  Symmetry.ConsumerInvariantUnder (Quotient.fixedKernelConsumer A kernel) act
g2eQPreservingActionMakesKernelConsumerInvariant A kernel act preserves =
  Symmetry.sufficientObserverPreservationImpliesConsumerInvariance
    (Quotient.determinantResponseSufficientForFixedKernel A kernel)
    preserves

threeOrbitConsumerEquality :
  ∀ {State Outcome : Set}
    (consumer : State -> Outcome) ->
    (act : State -> State) ->
  Symmetry.ConsumerInvariantUnder consumer act ->
  (x : State) ->
  (consumer (act x) ≡ consumer x)
  × (consumer (act (act x)) ≡ consumer x)
threeOrbitConsumerEquality consumer act invariant x =
  invariant x , trans (invariant (act x)) (invariant x)

------------------------------------------------------------------------
-- Literal attachment boundary.
--
-- The user-directed assumption for this tranche is that ordinary machinery is
-- already present elsewhere in the repository.  Therefore this owner does not
-- rebuild taper construction, Schur elimination, determinant algebra, or C3
-- action infrastructure.  The only remaining attachment is same-object:
-- identify the actual nuisance rows and actual constructed taper point with one
-- common order-three action and discharge determinant covariance on those exact
-- objects.
------------------------------------------------------------------------

record LiteralRiemannCommonC3Attachment : Set₁ where
  field
    literalCommonC3Geometry : CommonC3DeterminantGeometry
    literalOrbit : LiteralDeterminantOrbit literalCommonC3Geometry
    sameObjectNuisanceOne : Set
    sameObjectNuisanceTwo : Set
    sameObjectConstructedTaper : Set
    sameObjectG2eDeterminantResponse : Set

open LiteralRiemannCommonC3Attachment public

constructedThreeTaperMachineryAlreadyOwned : Bool
constructedThreeTaperMachineryAlreadyOwned =
  ThreeTaper.constructedPositiveTaperTriple
    ThreeTaper.canonicalTwoZeroThreeTaperReturn

exactSelectedNuisanceEliminationAlreadyOwned : Bool
exactSelectedNuisanceEliminationAlreadyOwned =
  ThreeTaper.twoSelectedNuisancesEliminatedExactly
    ThreeTaper.canonicalTwoZeroThreeTaperReturn

literalSameObjectCommonC3AttachmentRecovered : Bool
literalSameObjectCommonC3AttachmentRecovered = false

literalSameObjectCommonC3AttachmentRecoveredIsFalse :
  literalSameObjectCommonC3AttachmentRecovered ≡ false
literalSameObjectCommonC3AttachmentRecoveredIsFalse = refl

record CommonC3DeterminantCompilerBoundary : Set where
  constructor commonC3DeterminantCompilerBoundary
  field
    commonRotationPreservesDeterminantQ : Bool
    commonRotationPreservesDeterminantQIsTrue :
      commonRotationPreservesDeterminantQ ≡ true
    qPreservationForcesFixedKernelConsumerInvariance : Bool
    qPreservationForcesFixedKernelConsumerInvarianceIsTrue :
      qPreservationForcesFixedKernelConsumerInvariance ≡ true
    invariantThreeOrbitAutomaticallyProducesCancellation : Bool
    invariantThreeOrbitAutomaticallyProducesCancellationIsFalse :
      invariantThreeOrbitAutomaticallyProducesCancellation ≡ false
    ordinaryThreeTaperAndSchurMachineryNeedsRebuildingHere : Bool
    ordinaryThreeTaperAndSchurMachineryNeedsRebuildingHereIsFalse :
      ordinaryThreeTaperAndSchurMachineryNeedsRebuildingHere ≡ false
    literalSameObjectAttachmentStillRequired : Bool
    literalSameObjectAttachmentStillRequiredIsTrue :
      literalSameObjectAttachmentStillRequired ≡ true
    highestAlphaReading : String

canonicalCommonC3DeterminantCompilerBoundary : CommonC3DeterminantCompilerBoundary
canonicalCommonC3DeterminantCompilerBoundary =
  commonC3DeterminantCompilerBoundary
    true refl
    true refl
    false refl
    false refl
    true refl
    "All generic C3/determinant machinery is now treated as existing infrastructure. The only RH payment is the literal same-object attachment of the actual two nuisance rows and constructed taper response to one common order-three action. If that action merely preserves q, the fixed-kernel consumer is invariant on the entire orbit and no cancellation follows from symmetry alone; a useful symmetry route must add a nontrivial scalar q/phase theorem."
