module DASHI.Governance.BoloBoloOWSSpokesRateShiftRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloOWSSpokesRateShiftExact as Shift

reportBackPostCrossPinned : Shift.postCrossProduct Shift.reportBackRateShift ≡ 105
reportBackPostCrossPinned = refl

delegatePostCrossPinned : Shift.postCrossProduct Shift.delegateRateShift ≡ 140
delegatePostCrossPinned = refl

workingGroupPostCrossPinned : Shift.postCrossProduct Shift.workingGroupRateShift ≡ 1715
workingGroupPostCrossPinned = refl

preDurationMeanPinned : Shift.preDurationMeanMinutes Shift.canonicalDurationDescriptiveSnapshot ≡ 231
preDurationMeanPinned = refl

solePostDurationPinned : Shift.solePostDurationMinutes Shift.canonicalDurationDescriptiveSnapshot ≡ 220
solePostDurationPinned = refl

holdoutUntouched : Shift.protectedHoldoutConsumed Shift.canonicalRateShiftBoundary ≡ false
holdoutUntouched = refl

notCausalEffect : Shift.normalizedLexicalShiftIsCoordinationCostEffect Shift.canonicalRateShiftBoundary ≡ false
notCausalEffect = refl
