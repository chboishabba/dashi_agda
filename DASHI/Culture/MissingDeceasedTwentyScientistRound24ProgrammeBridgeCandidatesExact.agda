module DASHI.Culture.MissingDeceasedTwentyScientistRound24ProgrammeBridgeCandidatesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ROUND 24: LITERAL PROGRAMME-BRIDGE CANDIDATES
--
-- This owner is intentionally fail-closed.  A programme/object identifier,
-- thematic adjacency, shared institution, command authority, later
-- procurement, historical citation, or failed search cannot by itself pay H2.
-- Every candidate retains source identity/kind, the exact same-object claim,
-- temporal scope, what the source pays, and what it does not pay.
------------------------------------------------------------------------

data BridgePromotionStatus : Set where
  acquisitionOnly
  secondPersonCandidateOnly
  sameObjectSemanticsUnpaid
  H2programmeBridgePaid
  H3operationalBridgePaid : BridgePromotionStatus

record ProgrammeBridgeCandidate : Set where
  constructor programme-bridge-candidate
  field
    candidateName : String
    objectIdentifier : String
    personA : String
    personBCandidate : String
    sourceIdentity : String
    sourceKind : String
    sameObjectEvidence : String
    temporalScope : String
    custodyEvidence : String
    pays : String
    doesNotPay : String
    sameObjectSemanticsPaid : Bool
    crossPersonIdentityPaid : Bool
    preEventTemporalOverlapPaid : Bool
    preEventOperationalReceiptPaid : Bool
    promotionStatus : BridgePromotionStatus
    paretoPriority : Nat

open ProgrammeBridgeCandidate public

ningArmyCandidate : ProgrammeBridgeCandidate
ningArmyCandidate = programme-bridge-candidate
  "Ning Li / AC Gravity Army prototype"
  "DAAH01-01-9-R001"
  "Ning Li"
  "second retained scientist not identified"
  "public secondary reproductions of the FY2001 DoD Other Transaction row; original annual-report/SOW/closeout bytes still to acquire"
  "secondary reproduction / acquisition lead"
  "single award row ties AC Gravity and the Gravito-Electro Magnetic Superconductivity Experiment to the Army identifier; no second retained person is named in the acquired surface"
  "effective 2001-04-25 to 2002-09-25 as reproduced; primary custody verification unpaid"
  "award identifier and programme title visible in reproduced row; primary SOW/personnel/facility custody unpaid"
  "programme-object acquisition target and Ning-side anchor"
  "a second retained scientist, literal same-object role, H2, targeting, or primary-source custody"
  false false false false acquisitionOnly 1

amyNingCandidate : ProgrammeBridgeCandidate
amyNingCandidate = programme-bridge-candidate
  "Amy Eskridge -> Ning Li historical-reference path"
  "HAL5-Dec2018 anti-gravity presentation / Ning Li & Doug Torr AC Gravity slide"
  "Amy Eskridge"
  "Ning Li"
  "Amy Eskridge HAL5 2018 presentation transcript/archive already retained by the investigation"
  "presentation / historical-reference source"
  "Amy explicitly discusses Ning Li, Doug Torr, AC Gravity, and the reported 2001 DoD contract; the presentation does not place Amy on that programme object"
  "2018 retrospective reference to 1990s/2001 work"
  "literal person-to-person/work awareness is paid; Amy technical/release-object custody remains separate"
  "historical awareness and a concrete acquisition vocabulary for Amy's own reviewed object"
  "shared programme membership, shared apparatus, temporal overlap on the Army object, H2, or operational linkage"
  false true false false sameObjectSemanticsUnpaid 1

rezaMcCaslandCandidate : ProgrammeBridgeCandidate
rezaMcCaslandCandidate = programme-bridge-candidate
  "Reza / Mondaloy / McCasland"
  "FA930020P5032 plus pre-2013 Mondaloy record still required"
  "Monica Jacinto / Monica Reza"
  "William Neil McCasland"
  "SAM.gov FA930020P5032; AFRL institutional chronology; pre-2013 Mondaloy work-package source still unpaid"
  "primary procurement notice plus separate institutional chronology"
  "SAM.gov pays a 2020 AFRL/RQRE Mondaloy 200 billet procurement; McCasland's AFRL leadership chronology is separate and earlier"
  "2020 procurement is later than McCasland's 2011-2013 AFRL command"
  "later Mondaloy procurement custody at AFRL is paid; pre-2013 role-level custody is not"
  "Mondaloy persisted as an AFRL/RQRE procurement object in 2020"
  "McCasland participation in Mondaloy, a pre-2013 shared work package, H2, or targeting"
  false true false false sameObjectSemanticsUnpaid 1

jplCandidate : ProgrammeBridgeCandidate
jplCandidate = programme-bridge-candidate
  "Hicks / Maiwald JPL work-package bridge"
  "exact shared JPL mission/instrument/procurement/work-package identifier not yet located"
  "Michael David Hicks"
  "Frank W. Maiwald"
  "separate JPL institutional/science objects already retained"
  "institutional/object acquisition state"
  "shared institution is paid; exact shared technical object remains unpaid"
  "overlapping institutional era is insufficient without object-specific dates"
  "separate JPL science-object custody only"
  "candidate pair and exact acquisition target"
  "same programme, same instrument, same work package, H2, or operational linkage"
  false true false false sameObjectSemanticsUnpaid 2

nudtCandidate : ProgrammeBridgeCandidate
nudtCandidate = programme-bridge-candidate
  "Chen / Feng / Zhang Daibing NUDT task bridge"
  "exact shared PLA/NUDT task, project, laboratory, codebase or work-package identifier not yet located"
  "Chen Shuming"
  "Feng Yanghe / Zhang Daibing candidate set"
  "separate NUDT institutional and technical-object surfaces already retained"
  "institutional/object acquisition state"
  "strategic institution overlap is paid; literal shared task/code/work-package semantics remain unpaid"
  "institutional overlap alone does not establish project-time overlap"
  "separate NUDT programme/object custody only"
  "candidate cluster and exact acquisition target"
  "same task, same codebase, H2, or operational linkage"
  false true false false sameObjectSemanticsUnpaid 2

round24Candidates : List ProgrammeBridgeCandidate
round24Candidates =
  ningArmyCandidate ∷ amyNingCandidate ∷ rezaMcCaslandCandidate ∷ jplCandidate ∷ nudtCandidate ∷ []

round24CandidateCount : Nat
round24CandidateCount = 5

round24H2PaidCount : Nat
round24H2PaidCount = 0

round24H3PaidCount : Nat
round24H3PaidCount = 0

promotionRequiresSameObjectAndCrossPersonIdentity : Bool
promotionRequiresSameObjectAndCrossPersonIdentity = true

sameInstitutionCannotPaySameProgramme : Bool
sameInstitutionCannotPaySameProgramme = true

laterProcurementCannotPayEarlierPersonalParticipation : Bool
laterProcurementCannotPayEarlierPersonalParticipation = true

historicalReferenceCannotPaySharedMembership : Bool
historicalReferenceCannotPaySharedMembership = true

searchFailureIsNotNonexistence : Bool
searchFailureIsNotNonexistence = true

round24Pareto : String
round24Pareto = "Acquire primary DAAH01-01-9-R001 FY2001/SOW/closeout personnel and apparatus custody; recover a pre-2013 Mondaloy AFRL role/work-package object; inspect Amy's own reviewed technical/release objects for AC Gravity/Army/apparatus/personnel cross-reference; then exact JPL and NUDT work-package/task identifiers. Promote H2 only after literal same-object semantics plus cross-person identity are both paid."
