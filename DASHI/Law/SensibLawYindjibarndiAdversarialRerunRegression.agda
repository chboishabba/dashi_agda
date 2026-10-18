module DASHI.Law.SensibLawYindjibarndiAdversarialRerunRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawYindjibarndiAdversarialRerunExact as Y

exactYunupinguReuseRemainsEnabled :
  Y.exactYunupinguCoordinateReused Y.canonicalYindjibarndiRerunBoundary ≡ true
exactYunupinguReuseRemainsEnabled = refl

exactMaboReuseRemainsEnabled :
  Y.exactMaboCoordinateReused Y.canonicalYindjibarndiRerunBoundary ≡ true
exactMaboReuseRemainsEnabled = refl

maboCounterStillDoesNotEraseAllDefeaters :
  Y.maboCounterErasesAllDefeaters Y.canonicalYindjibarndiRerunBoundary ≡ false
maboCounterStillDoesNotEraseAllDefeaters = refl

yunupinguScopeObjectionsRemainLive :
  Y.yunupinguScopeObjectionsRemainLive Y.canonicalYindjibarndiRerunBoundary ≡ true
yunupinguScopeObjectionsRemainLive = refl

rerunStillSearchesCounterDefeaters :
  Y.rerunSearchesCounterDefeatersAgain Y.canonicalYindjibarndiRerunBoundary ≡ true
rerunStillSearchesCounterDefeaters = refl

routeStateStillDoesNotPredictOutcome :
  Y.routeStatePredictsJudicialOutcome Y.canonicalYindjibarndiRerunBoundary ≡ false
routeStateStillDoesNotPredictOutcome = refl

genericMaboStillCannotPayRoute :
  Y.GenericMaboJoinPaysRoute → ⊥
genericMaboStillCannotPayRoute =
  Y.genericMaboStillCannotPay
