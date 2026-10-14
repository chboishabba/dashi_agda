module DASHI.Governance.BoloBoloPortoAlegreCurrentProcessEvidenceRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloPortoAlegreCurrentProcessEvidenceExact as Porto

currentMeetingDurationPaid :
  Porto.currentCOPMeetingDurationMinutes Porto.canonicalPortoCurrentProcessEvidence ≡ 180
currentMeetingDurationPaid = refl

currentCouncilSizePaid :
  Porto.currentCouncilMemberCount Porto.canonicalPortoCurrentProcessEvidence ≡ 92
currentCouncilSizePaid = refl

reported2025CycleParticipationPaid :
  Porto.reported2025AssemblyParticipationCount Porto.canonicalPortoCurrentProcessEvidence ≡ 18055
reported2025CycleParticipationPaid = refl

all92AttendanceNotPaid :
  Porto.all92CouncillorsAttendedObservedMeeting Porto.canonicalPortoCurrentProcessBoundary ≡ false
all92AttendanceNotPaid = refl

noObservedPersonMinuteProduct :
  Porto.currentMeetingDurationTimesCouncilSizeIsObservedWorkload Porto.canonicalPortoCurrentProcessBoundary ≡ false
noObservedPersonMinuteProduct = refl

cycleCountNotUniqueIdentity :
  Porto.reportedCycleParticipationEstablishesUniquePersonsAcrossAssemblies Porto.canonicalPortoCurrentProcessBoundary ≡ false
cycleCountNotUniqueIdentity = refl

municipalSourceNotBolo :
  Porto.officialMunicipalObservationIsBoloTargetEvidence Porto.canonicalPortoCurrentProcessBoundary ≡ false
municipalSourceNotBolo = refl
