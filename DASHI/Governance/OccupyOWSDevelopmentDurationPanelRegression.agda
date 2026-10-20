module DASHI.Governance.OccupyOWSDevelopmentDurationPanelRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyOWSDevelopmentDurationPanelExact as Panel

sixDurationRowsPaid : Panel.rowCount Panel.canonicalOWSDurationRows ≡ 6
sixDurationRowsPaid = refl

sep18Approximate : Panel.precision Panel.sep18 ≡ Panel.approximateEndClock
sep18Approximate = refl

sep18DurationPinned : Panel.durationMinutes Panel.sep18 ≡ 450
sep18DurationPinned = refl

oct19DurationPinned : Panel.durationMinutes Panel.oct19 ≡ 140
oct19DurationPinned = refl

oct21CrossMidnightPinned : Panel.durationMinutes Panel.oct21 ≡ 440
oct21CrossMidnightPinned = refl

nov02DurationPinned : Panel.durationMinutes Panel.nov02 ≡ 60
nov02DurationPinned = refl

nov04DurationPinned : Panel.durationMinutes Panel.nov04 ≡ 65
nov04DurationPinned = refl

nov10DurationPinned : Panel.durationMinutes Panel.nov10 ≡ 220
nov10DurationPinned = refl

durationIsNotBurden : Panel.durationEqualsCoordinationBurden Panel.canonicalOWSDurationBoundary ≡ false
durationIsNotBurden = refl

holdoutExcluded : Panel.protectedHoldoutRecordUsedInDurationPanel Panel.canonicalOWSDurationBoundary ≡ false
holdoutExcluded = refl
