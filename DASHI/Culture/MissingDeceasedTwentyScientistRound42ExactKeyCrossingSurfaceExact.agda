module DASHI.Culture.MissingDeceasedTwentyScientistRound42ExactKeyCrossingSurfaceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound40CohortFrontierRefreshExact as R40
import DASHI.Culture.MissingDeceasedTwentyScientistRound41TierDExactIdentifierUpgradesExact as R41

------------------------------------------------------------------------
-- ROUND 42: EXACT-KEY CROSSING SURFACE
--
-- The cohort now has many concrete single-person objects.  We therefore search
-- on exact identifiers, not broad institutional/disciplinary adjacency.  The
-- currently searched exact-key surface has not produced a literal second
-- retained scientist on the same object.  This is a bounded search result,
-- never a universal non-existence theorem.
------------------------------------------------------------------------

record ExactKeyCrossingSearch : Set where
  constructor exact-key-crossing-search
  field
    person : String
    exactKey : String
    paidObject : String
    secondRetainedPersonLocatedOnSameKey : Bool
    searchedSurfaceBounded : Bool
    whatTheSearchPays : String
    whatTheSearchDoesNotPay : String

open ExactKeyCrossingSearch public

leblancKeySearch : ExactKeyCrossingSearch
leblancKeySearch = exact-key-crossing-search
  "Joshua Kyle LeBlanc"
  "WBS 658133.04.01.22.01.06"
  "NASA 40 kW Fission Surface Power instrumentation-and-controls technology-development surface"
  false true
  "an exact NASA FSP WBS and named FSP/FICS personnel surface"
  "a universal roster, a second retained scientist on the WBS, H2, or H3"

maiwaldKeySearch : ExactKeyCrossingSearch
maiwaldKeySearch = exact-key-crossing-search
  "Frank W. Maiwald"
  "JPL SURP SP23012 / RPC#sp23012"
  "Unambiguous Detection of Biosignatures by Action Spectroscopy"
  false true
  "exact project identity, PI/co-investigators, apparatus and publication surface"
  "a second retained scientist on SP23012, H2, or H3"

jasonThomasKeySearch : ExactKeyCrossingSearch
jasonThomasKeySearch = exact-key-crossing-search
  "Jason R. Thomas"
  "NIH U54-HL127365"
  "Novartis/Harvard STING-IRF3/NFkB chemical-biology project surface"
  false true
  "an exact grant/project surface naming Thomas"
  "cross-cohort programme identity or H2"

liMinyongKeySearch : ExactKeyCrossingSearch
liMinyongKeySearch = exact-key-crossing-search
  "Li Minyong"
  "CN201110101082.5 and related listed CN patent filings"
  "Shandong University fluorescent-probe / medicinal-chemistry patent surface"
  false true
  "exact patent identifiers and named co-inventors"
  "a retained-scientist shared programme merely from patent co-inventorship"

yanHongKeySearch : ExactKeyCrossingSearch
yanHongKeySearch = exact-key-crossing-search
  "Yan Hong"
  "NSFC 51176157"
  "NPU surface-discharge / hypersonic shock-control research surface"
  false true
  "an exact national science project identifier on Yan's paper surface"
  "a second retained scientist on the project, H2, or H3"

chavezKeySearch : ExactKeyCrossingSearch
chavezKeySearch = exact-key-crossing-search
  "Anthony Chavez"
  "Scorpius / DARHT technical object family"
  "LANL Scorpius accelerator and DARHT engineering surface"
  false true
  "same-person LANL identity, DARHT tenure, Scorpius design work, and a separate named Scorpius/DARHT beam-position-monitor author surface"
  "that every Scorpius/DARHT contributor shared one task, a second retained scientist, H2, or H3"

round42SearchedExactKeys : List ExactKeyCrossingSearch
round42SearchedExactKeys =
  leblancKeySearch ∷
  maiwaldKeySearch ∷
  jasonThomasKeySearch ∷
  liMinyongKeySearch ∷
  yanHongKeySearch ∷
  chavezKeySearch ∷
  []

round42SearchedExactKeyCount : Nat
round42SearchedExactKeyCount = 6

round42LocatedCrossRetainedKeyCount : Nat
round42LocatedCrossRetainedKeyCount = 0

searchedSurfaceNoCrossingCannotPayUniversalAbsence : Bool
searchedSurfaceNoCrossingCannotPayUniversalAbsence = true

exactKeySearchIsStrongerThanInstitutionalAdjacency : Bool
exactKeySearchIsStrongerThanInstitutionalAdjacency = true

singlePersonExactObjectDoesNotPayH2 : Bool
singlePersonExactObjectDoesNotPayH2 = true

multipleStrategicObjectsDoNotImplyOneCommonProgramme : Bool
multipleStrategicObjectsDoNotImplyOneCommonProgramme = true

absenceFromSearchResultsDoesNotProveNonMembership : Bool
absenceFromSearchResultsDoesNotProveNonMembership = true

narrativeMayUseDistributedProgrammeModelAsCurrentBestDescription : Bool
narrativeMayUseDistributedProgrammeModelAsCurrentBestDescription = true

narrativeMayClaimDemonstratedSingleCommonProgramme : Bool
narrativeMayClaimDemonstratedSingleCommonProgramme = false

narrativeMayClaimOperationalTargeting : Bool
narrativeMayClaimOperationalTargeting = false

round42H2PaidCount : Nat
round42H2PaidCount = 0

round42H3PaidCount : Nat
round42H3PaidCount = 0

round42NarrativeBoundary : String
round42NarrativeBoundary = "The evidence now supports a cohort containing many concrete, technically significant and often strategically relevant programme objects. On the exact-key surfaces searched so far, no literal second retained scientist has been located on the same object. The strongest current descriptive narrative is therefore distributed high-value technical programmes with some thematic, institutional and mission adjacency, not a demonstrated single common programme. This bounded search result does not prove that cross-person programme links do not exist, and it cannot support targeting, causation, concealment or coordinated-event claims."

round42Pareto : String
round42Pareto = "Continue exact-key snowballs on the shortest H1-to-H2 debts: Reza/McCasland HCB identity-bearing role records; Ning DAAH01-01-9-R001 primary bytes; Amy original NASA/Institute review object; Chavez DARHT/Scorpius work-package rosters; LeBlanc FSP WBS subordinate records; SP23012/JPL procurement and instrument identifiers; NUDT task codes; then the Tier-D exact grant/patent/project identifiers."
