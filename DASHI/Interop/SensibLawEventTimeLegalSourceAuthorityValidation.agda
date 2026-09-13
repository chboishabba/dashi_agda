module DASHI.Interop.SensibLawEventTimeLegalSourceAuthorityValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.SensibLawEventTimeLegalSourceAuthorityExact as EventTime

open EventTime.EventTimeLegalSourceAuthorityBoundary

indexed : eventDateIndexed EventTime.canonicalEventTimeLegalSourceAuthorityBoundary ≡ true
indexed = refl
interval : explicitVersionIntervalRequired EventTime.canonicalEventTimeLegalSourceAuthorityBoundary ≡ true
interval = refl
locator : exactProvisionLocatorRequired EventTime.canonicalEventTimeLegalSourceAuthorityBoundary ≡ true
locator = refl
pointInTime : officialPointInTimeSourceRequired EventTime.canonicalEventTimeLegalSourceAuthorityBoundary ≡ true
pointInTime = refl
history : officialLegislativeHistoryRequired EventTime.canonicalEventTimeLegalSourceAuthorityBoundary ≡ true
history = refl
sameSource : exactMeetSourceWeldRequired EventTime.canonicalEventTimeLegalSourceAuthorityBoundary ≡ true
sameSource = refl
operative : sourceOperativeAtEventTimeRequired EventTime.canonicalEventTimeLegalSourceAuthorityBoundary ≡ true
operative = refl
unindexedNotEnough : unindexedCurrentValidityPaysHistoricalValidity EventTime.canonicalEventTimeLegalSourceAuthorityBoundary ≡ false
unindexedNotEnough = refl
historicalNotPresent : historicalValidityProvesPresentValidity EventTime.canonicalEventTimeLegalSourceAuthorityBoundary ≡ false
historicalNotPresent = refl
presentNotHistorical : presentValidityProvesHistoricalValidity EventTime.canonicalEventTimeLegalSourceAuthorityBoundary ≡ false
presentNotHistorical = refl
