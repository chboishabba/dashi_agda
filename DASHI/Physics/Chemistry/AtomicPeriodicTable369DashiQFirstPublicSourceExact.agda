module DASHI.Physics.Chemistry.AtomicPeriodicTable369DashiQFirstPublicSourceExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AttributionLedgerExact as A

------------------------------------------------------------------------
-- Earliest located public/repository source stating the periodic-table programme.
--
-- Repository archaeology shows that dashiQ's initial README contained only its
-- two-line title.  Commit bbedb3bed85e31125eb68255379b57788a434939 then
-- expands README.md from those two lines to the long end-to-end synthesis and
-- explicitly introduces "Chemistry & the periodic table (first major test)".
-- The source states that shell structure from kernel filling, period lengths
-- 1--3, valence structure, noble-gas closure and alkali recurrence had been
-- obtained, while exact energies, fine structure, relativistic corrections and
-- nuclear-stability details had not.
--
-- This is a priority/provenance receipt.  It is not retroactively promoted into
-- a proof-assistant theorem or into external peer-reviewed publication.

firstPublicPeriodicProgramme : A.AttributionReceipt
firstPublicPeriodicProgramme =
  A.attributionReceipt
    "Johl Brown"
    "dashiQ README: Chemistry & the periodic table (first major test)"
    "authored 2026-01-03T00:16:42Z; committed 2026-01-03T02:18:18Z"
    "unassigned"
    "periodic table Q10693; atom Q9121"
    "primary public repository source for the historical programme statement"
    "546 / 539.7 classification cues"
    "https://github.com/chboishabba/dashiQ/commit/bbedb3bed85e31125eb68255379b57788a434939"
    "README.md expanded from the initial two-line repository README to the end-to-end DASHI synthesis"
    "priority and historical-programme authority only"
    "explicitly records kernel-filling shell structure, period lengths 1--3, valence structure, noble-gas closure and alkali recurrence, with exact energies/fine structure/relativistic corrections/nuclear stability left open"

------------------------------------------------------------------------
-- Exact chronology split: the preceding README state is the two-line file.

record FirstPublicSourceChronology : Set where
  constructor firstPublicSourceChronology
  field
    initialReadmeCommit : String
    initialReadmeContent : String
    periodicProgrammeCommit : String
    periodicProgrammeAuthored : String
    periodicProgrammeCommitted : String
    periodicProgrammePredatesDashiAgdaInit : Bool
    periodicProgrammePredatesDashiAgdaInitIsTrue :
      periodicProgrammePredatesDashiAgdaInit ≡ true

canonicalFirstPublicSourceChronology : FirstPublicSourceChronology
canonicalFirstPublicSourceChronology =
  firstPublicSourceChronology
    "9d91b1b255e5f97d12d3dc873fb4e49a3eddb368"
    "# dashiQ / hella I guess?"
    "bbedb3bed85e31125eb68255379b57788a434939"
    "2026-01-03T00:16:42Z"
    "2026-01-03T02:18:18Z"
    true refl

------------------------------------------------------------------------
-- Non-promotion boundary.

record FirstPublicSourceBoundary : Set where
  constructor firstPublicSourceBoundary
  field
    publicRepoStatementEqualsPeerReviewedPublication : Bool
    publicRepoStatementEqualsPeerReviewedPublicationIsFalse :
      publicRepoStatementEqualsPeerReviewedPublication ≡ false

    historicalWeDidEqualsKernelCheckedTheorem : Bool
    historicalWeDidEqualsKernelCheckedTheoremIsFalse :
      historicalWeDidEqualsKernelCheckedTheorem ≡ false

    statementOfOpenPhysicalItemsEqualsTheirRecovery : Bool
    statementOfOpenPhysicalItemsEqualsTheirRecoveryIsFalse :
      statementOfOpenPhysicalItemsEqualsTheirRecovery ≡ false

canonicalFirstPublicSourceBoundary : FirstPublicSourceBoundary
canonicalFirstPublicSourceBoundary =
  firstPublicSourceBoundary false refl false refl false refl
