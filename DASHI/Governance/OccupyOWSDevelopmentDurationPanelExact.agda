module DASHI.Governance.OccupyOWSDevelopmentDurationPanelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.OccupyOWSManifestExact as Manifest

------------------------------------------------------------------------
-- OWS DEVELOPMENT-ONLY MEETING DURATION PANEL.
--
-- Source layer: the underlying OWS GA minute text supplies clock expressions.
-- DASHI layer: parser/manual audit selects explicit start/end statements and
-- computes minute differences. Protected holdout records are not read here.
------------------------------------------------------------------------

data DurationPrecision : Set where
  exactClockBounds : DurationPrecision
  approximateEndClock : DurationPrecision

record OWSDurationRow : Set where
  constructor owsDurationRow
  field
    manifestRecord : Manifest.OWSRecord
    sourceStartText : String
    sourceEndText : String
    durationMinutes : Nat
    precision : DurationPrecision

open OWSDurationRow public

rowCount : List OWSDurationRow → Nat
rowCount [] = 0
rowCount (_ ∷ xs) = 1 + rowCount xs

sep18 : OWSDurationRow
sep18 =
  owsDurationRow
    Manifest.record3
    "Meeting Date/Time: 9/18/2011 / 3pm EST"
    "At this point the assembly broke up for the evening, around 10:30 PM."
    450
    approximateEndClock

oct19 : OWSDurationRow
oct19 =
  owsDurationRow
    Manifest.record26
    "Meeting Date/Time: 10/19/2011 / 7pm EST"
    "F: GA adjourned at 9:20."
    140
    exactClockBounds

oct21 : OWSDurationRow
oct21 =
  owsDurationRow
    Manifest.record28
    "Meeting Date/Time: 10/21/2011 / 7pm EST"
    "F: Adjourned! (Meeting adjourned at 2:20AM)"
    440
    exactClockBounds

nov02 : OWSDurationRow
nov02 =
  owsDurationRow
    Manifest.record38
    "Meeting Date/Time: 11/2/2011 / 7pm EST"
    "Adjourned 8 pm."
    60
    exactClockBounds

nov04 : OWSDurationRow
nov04 =
  owsDurationRow
    Manifest.record40
    "Meeting Date/Time: 11/4/2011 / 7pm EST"
    "[GA concluded at 8:05 pm]"
    65
    exactClockBounds

nov10 : OWSDurationRow
nov10 =
  owsDurationRow
    Manifest.record43
    "Date / Time: Thursday 10/11/2011 / 7:00pm EST"
    "[GA concludes 10:40 pm]"
    220
    exactClockBounds

canonicalOWSDurationRows : List OWSDurationRow
canonicalOWSDurationRows = sep18 ∷ oct19 ∷ oct21 ∷ nov02 ∷ nov04 ∷ nov10 ∷ []

record OWSDurationBoundary : Set where
  constructor owsDurationBoundary
  field
    durationEqualsCoordinationBurden : Bool
    approximateEndTreatedAsExact : Bool
    sourceDateTypoSilentlyCorrected : Bool
    protectedHoldoutRecordUsedInDurationPanel : Bool
    sixDevelopmentDurationsPaid : Bool

open OWSDurationBoundary public

canonicalOWSDurationBoundary : OWSDurationBoundary
canonicalOWSDurationBoundary =
  owsDurationBoundary
    false
    false
    false
    false
    true

canonicalOWSDurationReceipt : GenericReceipt.GenericReceipt
canonicalOWSDurationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "OWS development-only meeting duration panel"
    "DASHI.Governance.OccupyOWSDevelopmentDurationPanelExact"
    "canonicalOWSDurationBoundary"
    "extracts six start/end clock-bound rows from development-only OWS GA records and computes durations of approximately 450, and exactly 140, 440, 60, 65 and 220 minutes respectively"
    "the September 18 end is explicitly approximate; the November 10 source's date string is retained verbatim rather than silently corrected; duration is not coordination burden and no protected holdout record is consumed"
    "agda -i . DASHI/Governance/OccupyOWSDevelopmentDurationPanelRegression.agda"
