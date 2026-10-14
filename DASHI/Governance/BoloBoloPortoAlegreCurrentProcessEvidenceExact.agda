module DASHI.Governance.BoloBoloPortoAlegreCurrentProcessEvidenceExact where

open import DASHI.Core.Prelude

import DASHI.Core.CriticalRelationalGrammarSourceRegistryExact as Registry
import DASHI.Governance.BoloBoloComparatorInstitutionalVersioningExact as Versioning

------------------------------------------------------------------------
-- CURRENT PORTO ALEGRE PROCESS EVIDENCE
--
-- Independent comparator evidence only.  The municipal sources below are not
-- bolo'bolo sources and do not create target-bolo cost coefficients.
--
-- Source layer 1: City of Porto Alegre current OP institutional description.
-- It reports 17 regional + 6 thematic assemblies, fortnightly regional /
-- thematic forums, and a 92-councillor collegiate body meeting fortnightly.
--
-- Source layer 2: City of Porto Alegre news report published 2025-02-05.
-- It reports that the first ordinary 2025 COP meeting, held 2025-02-04, lasted
-- three hours while government representatives and councillors discussed the
-- budget and demands of the 17 regions and six thematic streams.
--
-- Source layer 3: City of Porto Alegre 2025-cycle summary, published
-- 2025-08-13. It reports 18,055 participants across the 23 assemblies in the
-- cycle.  This is retained as the source-reported cycle participation count;
-- DASHI does not infer that every count corresponds to a unique individual
-- across assemblies.
--
-- The meeting-duration article does NOT establish that all 92 councillors
-- attended that meeting. Therefore DASHI records a 180-minute meeting
-- observation but does not multiply 92 * 180 into observed person-minutes.
------------------------------------------------------------------------

portoCurrentArchitectureSource : Registry.SourceReference
portoCurrentArchitectureSource = Registry.source-reference
  "Prefeitura de Porto Alegre / Secretaria Municipal de Governança Cidadã e Desenvolvimento Rural"
  "Orçamento Participativo"
  "official municipal institutional description"
  2026
  "https://www.prefeitura.poa.br/smgov/orcamento-participativo"
  "official municipal administrative source"
  "source for the current OP institutional version: 17 regions, six thematic streams, 23 assemblies, fortnightly regional/thematic forums and a 92-councillor collegiate body meeting fortnightly"

portoFirstOrdinary2025MeetingSource : Registry.SourceReference
portoFirstOrdinary2025MeetingSource = Registry.source-reference
  "Prefeitura de Porto Alegre"
  "Orçamento Participativo faz sua primeira reunião ordinária do ano"
  "official municipal news report, 2025-02-05"
  2025
  "https://prefeitura.poa.br/gp/noticias/orcamento-participativo-faz-sua-primeira-reuniao-ordinaria-do-ano"
  "official municipal event report"
  "source for the reported three-hour duration of the 2025-02-04 first ordinary COP meeting and its budget/demand agenda; not an attendance roster or total workload audit"

porto2025CycleParticipationSource : Registry.SourceReference
porto2025CycleParticipationSource = Registry.source-reference
  "Prefeitura de Porto Alegre / Secretaria Municipal de Governança Cidadã e Desenvolvimento Rural"
  "Orçamento Participativo de 2025 mobilizou 18 mil pessoas"
  "official municipal cycle summary, 2025-08-13"
  2025
  "https://prefeitura.poa.br/smgov/noticias/orcamento-participativo-de-2025-mobilizou-18-mil-pessoas"
  "official municipal participation summary"
  "source for the reported 18,055 participants across 23 OP assemblies in the 2025 cycle; does not establish cross-assembly unique-person identity, person-hours or target-bolo scaling"

record PortoCurrentProcessEvidence : Set where
  constructor porto-current-process-evidence
  field
    currentRegionCount : Nat
    currentThematicCount : Nat
    currentAssemblyStreamCount : Nat
    currentCouncilMemberCount : Nat
    regionalThematicForumFortnightly : Bool
    councilFortnightly : Bool
    observedMeetingDateYear : Nat
    observedMeetingDateMonth : Nat
    observedMeetingDateDay : Nat
    currentCOPMeetingDurationMinutes : Nat
    reported2025AssemblyParticipationCount : Nat

open PortoCurrentProcessEvidence public

canonicalPortoCurrentProcessEvidence : PortoCurrentProcessEvidence
canonicalPortoCurrentProcessEvidence =
  porto-current-process-evidence
    17 6 23 92
    true true
    2025 2 4
    180
    18055

currentStructureAgreesWithVersionOwner :
  currentCouncilMemberCount canonicalPortoCurrentProcessEvidence ≡
  Versioning.currentCouncillorCount Versioning.canonicalPortoAlegreCurrent2026Version
currentStructureAgreesWithVersionOwner = refl

currentAssemblyStreamsAgreeWithVersionOwner :
  currentAssemblyStreamCount canonicalPortoCurrentProcessEvidence ≡
  Versioning.currentAssemblyStreamCount Versioning.canonicalPortoAlegreCurrent2026Version
currentAssemblyStreamsAgreeWithVersionOwner = refl

record PortoCurrentProcessBoundary : Set where
  constructor porto-current-process-boundary
  field
    officialCurrentArchitecturePaid : Bool
    officialThreeHourMeetingObservationPaid : Bool
    official2025CycleParticipationCountPaid : Bool
    all92CouncillorsAttendedObservedMeeting : Bool
    currentMeetingDurationTimesCouncilSizeIsObservedWorkload : Bool
    threeHourMeetingIsTotalParticipationWorkload : Bool
    reportedCycleParticipationEstablishesUniquePersonsAcrossAssemblies : Bool
    reportedCycleParticipationIsPersonHours : Bool
    oneMeetingIdentifiesLongRunCouncilBurden : Bool
    currentPortoObservationTransfersToHistorical44MemberVersion : Bool
    officialMunicipalObservationIsBoloTargetEvidence : Bool
    comparatorMayConstrainPlausibleMeasurementDesign : Bool

open PortoCurrentProcessBoundary public

canonicalPortoCurrentProcessBoundary : PortoCurrentProcessBoundary
canonicalPortoCurrentProcessBoundary =
  porto-current-process-boundary
    true true true
    false false false false false false false false
    true
