module DASHI.Analysis.RiemannAristotleTwoZeroThreeTaperReturnRegression where

open import DASHI.Core.Prelude

import DASHI.Analysis.RiemannAristotleTwoZeroThreeTaperReturnExact as Return

leanOwnerRecorded :
  Return.TwoZeroThreeTaperReturn.machineCheckedInOwner
    Return.canonicalTwoZeroThreeTaperReturn ≡ true
leanOwnerRecorded = refl

leanProofNotTransportedIntoAgda :
  Return.TwoZeroThreeTaperReturn.transportedIntoAgda
    Return.canonicalTwoZeroThreeTaperReturn ≡ false
leanProofNotTransportedIntoAgda = refl

twoSelectedNuisancesAreExact :
  Return.TwoZeroThreeTaperReturn.twoSelectedNuisancesEliminatedExactly
    Return.canonicalTwoZeroThreeTaperReturn ≡ true
twoSelectedNuisancesAreExact = refl

targetSurvives :
  Return.TwoZeroThreeTaperReturn.targetResidualNonzero
    Return.canonicalTwoZeroThreeTaperReturn ≡ true
targetSurvives = refl

farTailStillOpen :
  Return.TwoZeroThreeTaperReturn.projectedFarTailBudgetClosed
    Return.canonicalTwoZeroThreeTaperReturn ≡ false
farTailStillOpen = refl

selectedDebtIsZero :
  Return.TwoZeroFarTailFrontier.localSelectedResidualDebt
    Return.canonicalTwoZeroFarTailFrontier ≡ false
selectedDebtIsZero = refl

oldAbsoluteMajorantNotRevived :
  Return.TwoZeroFarTailFrontier.absoluteMajorantRouteRevived
    Return.canonicalTwoZeroFarTailFrontier ≡ false
oldAbsoluteMajorantNotRevived = refl

rhStillNotDerived :
  Return.TwoZeroThreeTaperReturn.riemannHypothesisDerived
    Return.canonicalTwoZeroThreeTaperReturn ≡ false
rhStillNotDerived = refl
