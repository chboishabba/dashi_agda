module DASHI.Culture.HicksEventTimeRoleDiscontinuityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.ApplicationCapabilityCustodyBidiExact as C

record HicksEventTimeSurface : Set where
  constructor hicks-event-time-surface
  field
    jplServiceStart : String
    jplServiceEnd : String
    deathDate : String
    dartScienceTeamHistorical : Bool
    neatHistorical : Bool
    dawnHistorical : Bool
    deepSpace1Historical : Bool
    post2022JplRoleOwned : Bool
    post2022MissionAccessOwned : Bool
    sourceReference : String
open HicksEventTimeSurface public

hicksEventTimeSurface : HicksEventTimeSurface
hicksEventTimeSurface = hicks-event-time-surface
  "1998" "2022" "2023-07-30" true true true true false false
  "AAS Division for Planetary Sciences memorial; University of Arizona LPL memorial; JPL Family News October 2023"

hicksEventTimeContinuity : C.AccessContinuityReceipt
hicksEventTimeContinuity = C.access-continuity-receipt
  "JPL small-body / mission-specific application transformation"
  "JPL research scientist and mission science-team roles through 2022"
  "event-time 2023 operational role/access"
  false
  "institutional memorials explicitly end JPL service in 2022; no primary post-2022 JPL/mission continuity receipt located in this pass"
  "Historical mission expertise remains established, but event-time JPL application possession cannot be inherited across the 2022 departure without a separate continuity receipt."

record HicksTemporalBoundary : Set where
  constructor hicks-temporal-boundary
  field
    priorMissionTeamImpliesEventTimeAccess : Bool
    priorMissionTeamImpliesEventTimeAccessIsFalse : priorMissionTeamImpliesEventTimeAccess ≡ false
    formerJplScientistImpliesCurrentJplCustody : Bool
    formerJplScientistImpliesCurrentJplCustodyIsFalse : formerJplScientistImpliesCurrentJplCustody ≡ false
    postDepartureConsultingNotLocatedImpliesAbsent : Bool
    postDepartureConsultingNotLocatedImpliesAbsentIsFalse : postDepartureConsultingNotLocatedImpliesAbsent ≡ false
    eventTimeContinuityRequiresSeparateReceipt : Bool
    eventTimeContinuityRequiresSeparateReceiptIsTrue : eventTimeContinuityRequiresSeparateReceipt ≡ true
canonicalHicksTemporalBoundary : HicksTemporalBoundary
canonicalHicksTemporalBoundary = hicks-temporal-boundary false refl false refl false refl true refl

data HicksEventTimeReverseTarget : Set where
  acquirePost2022Consulting acquirePost2022MissionRole acquirePost2022RepositoryAccess
  acquirePost2022ObservingProgramme acquirePost2022DataCustody acquireEventTimeInstitutionalAffiliation
  : HicksEventTimeReverseTarget
