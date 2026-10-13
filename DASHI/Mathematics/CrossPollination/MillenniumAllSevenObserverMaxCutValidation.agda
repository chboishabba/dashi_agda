module DASHI.Mathematics.CrossPollination.MillenniumAllSevenObserverMaxCutValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.EisensteinNineRingInterferenceExact as ECarrier
import DASHI.Mathematics.CrossPollination.MillenniumSubstantiveCrossPollinationGateExact as Gate
import DASHI.Mathematics.CrossPollination.EisensteinObserverRecoverableQuotientExact as E
import DASHI.Mathematics.CrossPollination.EisensteinObserverRecoverableQuotientValidation
import DASHI.Physics.ThreeBody.EisensteinC3FourierExact as ThreeBody
import DASHI.Physics.ThreeBody.EisensteinC3FourierValidation
import DASHI.Mathematics.Arithmetic.EisensteinJZeroCubicSymmetryExact as Cubic
import DASHI.Mathematics.Arithmetic.EisensteinJZeroCubicSymmetryValidation

sevenClayProblemsIndexed : Gate.clayProblemLaneCount ≡ 7
sevenClayProblemsIndexed = refl

sixOpenClayProblemsIndexed : Gate.openClayProblemLaneCount ≡ 6
sixOpenClayProblemsIndexed = refl

navierStokesRemainsAnalyticBoundary :
  Gate.finalClosureStatus Gate.navierStokesStatus
  ≡ Gate.analyticOrGeometricBoundary
navierStokesRemainsAnalyticBoundary = refl

yangMillsRemainsAnalyticBoundary :
  Gate.finalClosureStatus Gate.yangMillsStatus
  ≡ Gate.analyticOrGeometricBoundary
yangMillsRemainsAnalyticBoundary = refl

poincareRemainsExternalSolvedBoundary :
  Gate.finalClosureStatus Gate.poincareHistoricalStatus
  ≡ Gate.externalClassificationBoundary
poincareRemainsExternalSolvedBoundary = refl

phaseReopensTwentyThree :
  E.reopen3 (E.phaseOfNat 23) (E.quotient3 23) ≡ 23
phaseReopensTwentyThree = E.reopenPhaseQuotient 23

phaseCollisionStillDoesNotGiveIdentity :
  E.phaseOfNat 0 ≡ E.phaseOfNat 3
phaseCollisionStillDoesNotGiveIdentity = refl

threeBodyEdgeIsExactOmegaEigenAction :
  (state : ThreeBody.PlanarThreeBodyState) →
  ThreeBody.mode1 (ThreeBody.cyclicPermute state)
  ≡ ECarrier.multiply ECarrier.omega (ThreeBody.mode1 state)
threeBodyEdgeIsExactOmegaEigenAction =
  Gate.threeBodyCyclicModeOneIsOmegaEigen

jZeroCubicEdgeHasOrderThreeAction :
  (B : ECarrier.Eisenstein) → Cubic.EisensteinCubicC3Action B
jZeroCubicEdgeHasOrderThreeAction = Gate.eisensteinCubicActionAvailable
