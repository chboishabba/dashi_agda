module DASHI.Physics.GR.SignedGSourceDynamicsBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed
import DASHI.Physics.GR.GravitationalPredictionAttributionBidiExact as Attr
import DASHI.Physics.GR.GravitationalPredictionObservationBidiExact as Pred

------------------------------------------------------------------------
-- SOURCE MODEL != SOURCE SOLUTION
--
-- A +/-G comparison may hold the source-model law fixed while requiring a
-- different source trajectory/state solved under each coupling sign.  The
-- prediction record's sourceModelCarrier is therefore not sufficient to stand
-- in for the sign-conditioned source solution.
------------------------------------------------------------------------

record SignedGSourceSolution
    (prediction : Attr.AttributedGravitationalPrediction)
    (sign : Signed.CouplingSign) : Set₁ where
  constructor signed-g-source-solution
  field
    sourceModelCarrier : String
    sourceModelMatchesPrediction :
      sourceModelCarrier
        ≡ Pred.sourceModelCarrier (Attr.prediction prediction)

    sourceSolutionCarrier : String
    sourceSolutionRevision : String
    couplingSign : Signed.CouplingSign
    couplingSignMatches : couplingSign ≡ sign

    SourceDynamicsDerivation : Set
    sourceDynamicsDerivation : SourceDynamicsDerivation

open SignedGSourceSolution public

record SignedGSourceDynamicsPair
    (positivePrediction negativePrediction : Attr.AttributedGravitationalPrediction)
    : Set₁ where
  constructor signed-g-source-dynamics-pair
  field
    positiveSourceSolution :
      SignedGSourceSolution positivePrediction Signed.positiveCoupling
    negativeSourceSolution :
      SignedGSourceSolution negativePrediction Signed.negativeCoupling

    sameSourceModelLaw :
      sourceModelCarrier positiveSourceSolution
        ≡ sourceModelCarrier negativeSourceSolution

    PositiveNegativeSolutionIdentityDecision : Set
    solutionIdentityDecision : PositiveNegativeSolutionIdentityDecision

open SignedGSourceDynamicsPair public

------------------------------------------------------------------------
-- Introspective fixture: same source-model label can require different solved
-- source-state decisions under different coupling signs.
------------------------------------------------------------------------

data SourceModelFixture : Set where
  positiveGModelFixture negativeGModelFixture : SourceModelFixture

data CoarseSourceModel : Set where
  sameSourceModel : CoarseSourceModel

data SourceSolutionDecision : Set where
  positiveGSolutionDecision negativeGSolutionDecision : SourceSolutionDecision

coarseSourceModelObserve : SourceModelFixture → CoarseSourceModel
coarseSourceModelObserve _ = sameSourceModel

sourceSolutionDecision : SourceModelFixture → SourceSolutionDecision
sourceSolutionDecision positiveGModelFixture = positiveGSolutionDecision
sourceSolutionDecision negativeGModelFixture = negativeGSolutionDecision

sourceModelCollision :
  coarseSourceModelObserve positiveGModelFixture
    ≡ coarseSourceModelObserve negativeGModelFixture
sourceModelCollision = refl

sameSourceModelDoesNotFixSourceSolution :
  sourceSolutionDecision positiveGModelFixture
    ≡ sourceSolutionDecision negativeGModelFixture → ⊥
sameSourceModelDoesNotFixSourceSolution ()

record SignedGSourceDynamicsBoundary : Set where
  constructor signed-g-source-dynamics-boundary
  field
    sameSourceModelMeansSameSolvedSourceState : Bool
    signConditionedSourceSolutionRequired : Bool
    negativeGMayReusePositiveGOrbitWithoutReSolving : Bool
    negativeGWaveSourceMayReusePositiveGBinaryTrajectoryWithoutReceipt : Bool
    sameSourceModelLawMayBeRetainedAcrossSignPair : Bool
    sourceSolutionDerivationRequiredPerSign : Bool

canonicalSignedGSourceDynamicsBoundary : SignedGSourceDynamicsBoundary
canonicalSignedGSourceDynamicsBoundary =
  signed-g-source-dynamics-boundary false true false false true true
