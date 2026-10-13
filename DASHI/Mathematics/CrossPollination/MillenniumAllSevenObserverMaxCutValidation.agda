module DASHI.Mathematics.CrossPollination.MillenniumAllSevenObserverMaxCutValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.CrossPollination.MillenniumSubstantiveCrossPollinationGateExact as Gate
import DASHI.Mathematics.CrossPollination.EisensteinObserverRecoverableQuotientExact as E
import DASHI.Mathematics.CrossPollination.EisensteinObserverRecoverableQuotientValidation

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
