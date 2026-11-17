module DASHI.Culture.AmyEskridgeVideoClaimProducerWeldExact where

-- A strict same-claim/source producer weld over ALL 86 claims in the user-
-- supplied video transcript. Reuses existing repo owners, not their summaries.
--
-- Original source owners (imported directly, not copied into the video):
-- Amy Eskridge, A Historical Perspective on Anti-Gravity Technology,
-- HAL5, 2018-12-06, https://www.hal5.org/PDF/HAL5-Dec2018-Talk-AntiGravity.pdf
-- Ning Li and D. G. Torr, Physical Review D 43 (1991) 457,
-- DOI 10.1103/PhysRevD.43.457 (abstract-inspected in source owner)
-- E. Podkletnov and R. Nieminen, Physica C 203 (1992) 441-444,
-- DOI 10.1016/0921-4534(92)90055-H (abstract-inspected in source owner)
-- J. Woodward, Foundations of Physics Letters 5 (1992) 425-442,
-- DOI 10.1007/BF00690424 (abstract-inspected in source owner)
-- US2949550A, US3626605A, US1655144A, US1655114A: patent-provenance
-- inspection in AmyEskridgeVideoSourceRegistryExact.
-- US House Oversight, FBI letter 2026-04-20, primary legislative inquiry:
-- https://oversight.house.gov/wp-content/uploads/2026/04/FBI-Missing-Scientists-Letter_4.20.26.pdf
-- Clip quotation and patent/source mention do not confer independent truth.
-- This complete 86-row aggregator must not convert unresolved claims to
-- positive fact by assigning them a cited source.

open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Core.AttributedSourceCore as A
import DASHI.Culture.AmyEskridgeVideoClaimAttributionLedgerExact as Video
import DASHI.Culture.AmyEskridgeVideoSourceRegistryExact as Source
import DASHI.Culture.AmyEskridgeHAL5AntigravitySourceEntitlementExact as Hal5
import DASHI.Culture.AmyEskridgeHAL5PrimaryLiteratureSnowballExact as Papers
import DASHI.Culture.MissingDeceasedInvestigativeAttributedSourceAtlasExact as Atlas
import DASHI.Culture.MissingDeceasedRosterExtensionNingLiNickPopeExact as Extension
import DASHI.Culture.AmyEskridgeOSINTSnowballExact as OSINT
import DASHI.Culture.AmyEskridgeDemiseCircumstancesSnowballExact as Demise
import DASHI.Culture.AmyEskridgeVideoZoomClipSourceWeldExact as Zoom

data EvidentiaryCarrier : Set where
  unpaidCarrier : String → EvidentiaryCarrier
  documentSource : Source.ScopedSource → EvidentiaryCarrier
  hal5Talk : Hal5.HAL5TalkSourceReceipt → EvidentiaryCarrier
  researchAbstract : Papers.AmyPrimaryLiteratureSnowballAtom → EvidentiaryCarrier
  atlasSource : A.AttributedSource → EvidentiaryCarrier
  historicalRoster : Extension.RosterExtensionReceipt → EvidentiaryCarrier
  obituaryRecord : Demise.DemiseSnowballAtom → EvidentiaryCarrier
  clipSource : Zoom.ExactClipJoin → EvidentiaryCarrier
  pairedCarriers : EvidentiaryCarrier → EvidentiaryCarrier → EvidentiaryCarrier

record VideoClaimJoin : Set where
  constructor video-claim-join
  field
    transcriptClaim : Video.RawAttributedClaim
    producerOrGap : EvidentiaryCarrier
    boundedSourceReading : String
    stillUnpaid : String

open VideoClaimJoin public

claimJoin001 : VideoClaimJoin
claimJoin001 = video-claim-join
  Video.claim001
  (clipSource Zoom.openingThreat)
  "Original Zoom 35:40-35:53; Amy recounts alleged threats, not an inspected threatening actor, agency record or causal proof"
  "Claim 001 at 00:00 remains subject to exact provenance/independent-evidence gate"

claimJoin002 : VideoClaimJoin
claimJoin002 = video-claim-join
  Video.claim002
  (clipSource Zoom.nsaFive)
  "Original Zoom 30:44-31:22; Amy attributes NSA five-person list to alleged secret-space-program contact; no original NSA roster"
  "Claim 002 at 00:05 remains subject to exact provenance/independent-evidence gate"

claimJoin003 : VideoClaimJoin
claimJoin003 = video-claim-join
  Video.claim003
  (clipSource Zoom.fourSuppressions)
  "Original Zoom 34:18-34:38; repeated informant allegedly asserted four suppressions; named cases and causal proof absent"
  "Claim 003 at 00:11 remains subject to exact provenance/independent-evidence gate"

claimJoin004 : VideoClaimJoin
claimJoin004 = video-claim-join
  Video.claim004
  (pairedCarriers (atlasSource OSINT.foxDeathCharacterizationSource) (documentSource Source.houseApril2026))
  "Morgan Phillips/Fox 2026-04-17 explicitly lists a media eleven including Amy plus the same ten reconstructed in the House source owner; House 2026-04-20 calls its underlying ten-case reports unconfirmed. The specific video narrator source is not independently identified"
  "Claim 004 at 00:21 remains subject to exact provenance/independent-evidence gate"

claimJoin005 : VideoClaimJoin
claimJoin005 = video-claim-join
  Video.claim005
  (clipSource Zoom.lexusSurveillance)
  "Original Zoom 2:53:41-2:56:11; first-person report of surveillance, not independent confirmation"
  "Claim 005 at 00:31 remains subject to exact provenance/independent-evidence gate"

claimJoin006 : VideoClaimJoin
claimJoin006 = video-claim-join
  Video.claim006
  (clipSource Zoom.lexusVehicle)
  "Original Zoom 2:54:11-2:56:11; reported tinted Lexus and plates, not independently verified registries"
  "Claim 006 at 00:36 remains subject to exact provenance/independent-evidence gate"

claimJoin007 : VideoClaimJoin
claimJoin007 = video-claim-join
  Video.claim007
  (clipSource Zoom.lexusPlateChange)
  "Original Zoom 2:55:05-2:56:11; first-person report of person changing plate, no independent corroboration"
  "Claim 007 at 01:03 remains subject to exact provenance/independent-evidence gate"

claimJoin008 : VideoClaimJoin
claimJoin008 = video-claim-join
  Video.claim008
  (unpaidCarrier "unlocated-01:23")
  "The NSA-list and eleven-scientist membership are not evidenced by any named roster or NSA primary document"
  "Claim 008 at 01:23 remains subject to exact provenance/independent-evidence gate"

claimJoin009 : VideoClaimJoin
claimJoin009 = video-claim-join
  Video.claim009
  (pairedCarriers (hal5Talk Hal5.canonicalHAL5TalkSourceReceipt) (obituaryRecord Demise.familyObituaryDateAtom))
  "HAL5 documents Amy’s 2018 historical research talk; family obituary separately dates her death 2022-06-11; neither validates a cause"
  "Claim 009 at 01:32 remains subject to exact provenance/independent-evidence gate"

claimJoin010 : VideoClaimJoin
claimJoin010 = video-claim-join
  Video.claim010
  (clipSource Zoom.futureP52)
  "Original Zoom 52:22-52:59; Amy reports P47/P52 future-human ideas, not physical evidence"
  "Claim 010 at 01:41 remains subject to exact provenance/independent-evidence gate"

claimJoin011 : VideoClaimJoin
claimJoin011 = video-claim-join
  Video.claim011
  (unpaidCarrier "unlocated-01:54")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 011 at 01:54 remains subject to exact provenance/independent-evidence gate"

claimJoin012 : VideoClaimJoin
claimJoin012 = video-claim-join
  Video.claim012
  (documentSource Source.burischCamelot)
  "Same original Dan Burisch interview supports attribution of testimony only; repeated clips are not independent witnesses"
  "Claim 012 at 02:04 remains subject to exact provenance/independent-evidence gate"

claimJoin013 : VideoClaimJoin
claimJoin013 = video-claim-join
  Video.claim013
  (unpaidCarrier "unlocated-02:35")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 013 at 02:35 remains subject to exact provenance/independent-evidence gate"

claimJoin014 : VideoClaimJoin
claimJoin014 = video-claim-join
  Video.claim014
  (unpaidCarrier "unlocated-02:42")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 014 at 02:42 remains subject to exact provenance/independent-evidence gate"

claimJoin015 : VideoClaimJoin
claimJoin015 = video-claim-join
  Video.claim015
  (hal5Talk Hal5.canonicalHAL5TalkSourceReceipt)
  "Official HAL5 programme/deck pays the existence, title, and historical discussion"
  "Claim 015 at 03:02 remains subject to exact provenance/independent-evidence gate"

claimJoin016 : VideoClaimJoin
claimJoin016 = video-claim-join
  Video.claim016
  (pairedCarriers (atlasSource OSINT.foxReviewSource) (documentSource Source.houseApril2026))
  "Fox explicitly reports no publicly established link among Amy and the other cases; House asked about an unconfirmed pattern, without concluding suppression"
  "Claim 016 at 03:14 remains subject to exact provenance/independent-evidence gate"

claimJoin017 : VideoClaimJoin
claimJoin017 = video-claim-join
  Video.claim017
  (unpaidCarrier "unlocated-03:20")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 017 at 03:20 remains subject to exact provenance/independent-evidence gate"

claimJoin018 : VideoClaimJoin
claimJoin018 = video-claim-join
  Video.claim018
  (unpaidCarrier "unlocated-04:28")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 018 at 04:28 remains subject to exact provenance/independent-evidence gate"

claimJoin019 : VideoClaimJoin
claimJoin019 = video-claim-join
  Video.claim019
  (unpaidCarrier "unlocated-04:54")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 019 at 04:54 remains subject to exact provenance/independent-evidence gate"

claimJoin020 : VideoClaimJoin
claimJoin020 = video-claim-join
  Video.claim020
  (unpaidCarrier "unlocated-05:22")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 020 at 05:22 remains subject to exact provenance/independent-evidence gate"

claimJoin021 : VideoClaimJoin
claimJoin021 = video-claim-join
  Video.claim021
  (unpaidCarrier "unlocated-05:32")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 021 at 05:32 remains subject to exact provenance/independent-evidence gate"

claimJoin022 : VideoClaimJoin
claimJoin022 = video-claim-join
  Video.claim022
  (documentSource Source.brown1960)
  "The Brown patent pays electrode-system claims, not successful gravity reduction"
  "Claim 022 at 06:21 remains subject to exact provenance/independent-evidence gate"

claimJoin023 : VideoClaimJoin
claimJoin023 = video-claim-join
  Video.claim023
  (unpaidCarrier "unlocated-06:40")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 023 at 06:40 remains subject to exact provenance/independent-evidence gate"

claimJoin024 : VideoClaimJoin
claimJoin024 = video-claim-join
  Video.claim024
  (documentSource Source.brown1960)
  "Patent identity, inventor and 1960 publication are established"
  "Claim 024 at 06:46 remains subject to exact provenance/independent-evidence gate"

claimJoin025 : VideoClaimJoin
claimJoin025 = video-claim-join
  Video.claim025
  (documentSource Source.hallgarthChandlerPatent)
  "US1655144A names Hallgarth and Chandler and concerns grain treatment; direct contradiction of Tesla attribution"
  "Claim 025 at 06:51 remains subject to exact provenance/independent-evidence gate"

claimJoin026 : VideoClaimJoin
claimJoin026 = video-claim-join
  Video.claim026
  (documentSource Source.teslaAerialPatent)
  "US1655114A concerns propeller-driven aerial transport, not space-drive propulsion"
  "Claim 026 at 07:01 remains subject to exact provenance/independent-evidence gate"

claimJoin027 : VideoClaimJoin
claimJoin027 = video-claim-join
  Video.claim027
  (unpaidCarrier "unlocated-07:22")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 027 at 07:22 remains subject to exact provenance/independent-evidence gate"

claimJoin028 : VideoClaimJoin
claimJoin028 = video-claim-join
  Video.claim028
  (unpaidCarrier "unlocated-07:32")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 028 at 07:32 remains subject to exact provenance/independent-evidence gate"

claimJoin029 : VideoClaimJoin
claimJoin029 = video-claim-join
  Video.claim029
  (unpaidCarrier "unlocated-07:42")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 029 at 07:42 remains subject to exact provenance/independent-evidence gate"

claimJoin030 : VideoClaimJoin
claimJoin030 = video-claim-join
  Video.claim030
  (unpaidCarrier "unlocated-07:59")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 030 at 07:59 remains subject to exact provenance/independent-evidence gate"

claimJoin031 : VideoClaimJoin
claimJoin031 = video-claim-join
  Video.claim031
  (unpaidCarrier "unlocated-08:15")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 031 at 08:15 remains subject to exact provenance/independent-evidence gate"

claimJoin032 : VideoClaimJoin
claimJoin032 = video-claim-join
  Video.claim032
  (unpaidCarrier "unlocated-08:32")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 032 at 08:32 remains subject to exact provenance/independent-evidence gate"

claimJoin033 : VideoClaimJoin
claimJoin033 = video-claim-join
  Video.claim033
  (documentSource Source.wallace1971)
  "Wallace patent describes a claimed secondary gravitational field; no replication"
  "Claim 033 at 08:38 remains subject to exact provenance/independent-evidence gate"

claimJoin034 : VideoClaimJoin
claimJoin034 = video-claim-join
  Video.claim034
  (unpaidCarrier "unlocated-09:01")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 034 at 09:01 remains subject to exact provenance/independent-evidence gate"

claimJoin035 : VideoClaimJoin
claimJoin035 = video-claim-join
  Video.claim035
  (unpaidCarrier "unlocated-09:19")
  "Precise official event/test/administrative record is missing; anecdote is not institutional proof"
  "Claim 035 at 09:19 remains subject to exact provenance/independent-evidence gate"

claimJoin036 : VideoClaimJoin
claimJoin036 = video-claim-join
  Video.claim036
  (researchAbstract Papers.liTorr1991Atom)
  "Published abstract for Li/Torr theoretical superconductor mechanism, not demonstrated force"
  "Claim 036 at 09:30 remains subject to exact provenance/independent-evidence gate"

claimJoin037 : VideoClaimJoin
claimJoin037 = video-claim-join
  Video.claim037
  (atlasSource Atlas.nasaNingNCC8124Source)
  "NASA NTRS NCC8-124 records work and failure to complete all-up experiments"
  "Claim 037 at 09:55 remains subject to exact provenance/independent-evidence gate"

claimJoin038 : VideoClaimJoin
claimJoin038 = video-claim-join
  Video.claim038
  (unpaidCarrier "unlocated-09:59")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 038 at 09:59 remains subject to exact provenance/independent-evidence gate"

claimJoin039 : VideoClaimJoin
claimJoin039 = video-claim-join
  Video.claim039
  (atlasSource Atlas.nasaNingNCC8124Source)
  "NASA cooperative agreement is NOT the later Army/AC Gravity contract"
  "Claim 039 at 10:03 remains subject to exact provenance/independent-evidence gate"

claimJoin040 : VideoClaimJoin
claimJoin040 = video-claim-join
  Video.claim040
  (unpaidCarrier "unlocated-10:16")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 040 at 10:16 remains subject to exact provenance/independent-evidence gate"

claimJoin041 : VideoClaimJoin
claimJoin041 = video-claim-join
  Video.claim041
  (historicalRoster Extension.ningLiRosterRepair)
  "Historical obituary/work identity places Ning Li death in 2021; cause not established"
  "Claim 041 at 10:27 remains subject to exact provenance/independent-evidence gate"

claimJoin042 : VideoClaimJoin
claimJoin042 = video-claim-join
  Video.claim042
  (unpaidCarrier "unlocated-10:34")
  "Precise official event/test/administrative record is missing; anecdote is not institutional proof"
  "Claim 042 at 10:34 remains subject to exact provenance/independent-evidence gate"

claimJoin043 : VideoClaimJoin
claimJoin043 = video-claim-join
  Video.claim043
  (researchAbstract Papers.podkletnov1992Atom)
  "1992 abstract reports 0.05-0.3% apparent weight reduction, NOT this narrated approximately 2% figure; different later work may be relevant"
  "Claim 043 at 10:43 remains subject to exact provenance/independent-evidence gate"

claimJoin044 : VideoClaimJoin
claimJoin044 = video-claim-join
  Video.claim044
  (unpaidCarrier "unlocated-10:58")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 044 at 10:58 remains subject to exact provenance/independent-evidence gate"

claimJoin045 : VideoClaimJoin
claimJoin045 = video-claim-join
  Video.claim045
  (unpaidCarrier "unlocated-11:05")
  "Precise official event/test/administrative record is missing; anecdote is not institutional proof"
  "Claim 045 at 11:05 remains subject to exact provenance/independent-evidence gate"

claimJoin046 : VideoClaimJoin
claimJoin046 = video-claim-join
  Video.claim046
  (unpaidCarrier "unlocated-11:08")
  "Precise official event/test/administrative record is missing; anecdote is not institutional proof"
  "Claim 046 at 11:08 remains subject to exact provenance/independent-evidence gate"

claimJoin047 : VideoClaimJoin
claimJoin047 = video-claim-join
  Video.claim047
  (unpaidCarrier "unlocated-11:12")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 047 at 11:12 remains subject to exact provenance/independent-evidence gate"

claimJoin048 : VideoClaimJoin
claimJoin048 = video-claim-join
  Video.claim048
  (unpaidCarrier "unlocated-11:19")
  "Precise official event/test/administrative record is missing; anecdote is not institutional proof"
  "Claim 048 at 11:19 remains subject to exact provenance/independent-evidence gate"

claimJoin049 : VideoClaimJoin
claimJoin049 = video-claim-join
  Video.claim049
  (unpaidCarrier "unlocated-11:31")
  "Legislative restriction and secret-classification inference are distinct; inspect amendment text and funding chain"
  "Claim 049 at 11:31 remains subject to exact provenance/independent-evidence gate"

claimJoin050 : VideoClaimJoin
claimJoin050 = video-claim-join
  Video.claim050
  (unpaidCarrier "unlocated-11:42")
  "Legislative restriction and secret-classification inference are distinct; inspect amendment text and funding chain"
  "Claim 050 at 11:42 remains subject to exact provenance/independent-evidence gate"

claimJoin051 : VideoClaimJoin
claimJoin051 = video-claim-join
  Video.claim051
  (researchAbstract Papers.woodward1992Atom)
  "1992 abstract discusses apparent weight-shift hypothesis, not independent propulsion demonstration"
  "Claim 051 at 12:01 remains subject to exact provenance/independent-evidence gate"

claimJoin052 : VideoClaimJoin
claimJoin052 = video-claim-join
  Video.claim052
  (unpaidCarrier "unlocated-12:24")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 052 at 12:24 remains subject to exact provenance/independent-evidence gate"

claimJoin053 : VideoClaimJoin
claimJoin053 = video-claim-join
  Video.claim053
  (unpaidCarrier "unlocated-12:36")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 053 at 12:36 remains subject to exact provenance/independent-evidence gate"

claimJoin054 : VideoClaimJoin
claimJoin054 = video-claim-join
  Video.claim054
  (unpaidCarrier "unlocated-12:55")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 054 at 12:55 remains subject to exact provenance/independent-evidence gate"

claimJoin055 : VideoClaimJoin
claimJoin055 = video-claim-join
  Video.claim055
  (unpaidCarrier "unlocated-13:14")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 055 at 13:14 remains subject to exact provenance/independent-evidence gate"

claimJoin056 : VideoClaimJoin
claimJoin056 = video-claim-join
  Video.claim056
  (unpaidCarrier "unlocated-13:42")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 056 at 13:42 remains subject to exact provenance/independent-evidence gate"

claimJoin057 : VideoClaimJoin
claimJoin057 = video-claim-join
  Video.claim057
  (unpaidCarrier "original-DIA-FOIA-inventory")
  "DIA document counts require exact inventory and release-version audit; published titles do not equal working technology"
  "Claim 057 at 14:07 remains subject to exact provenance/independent-evidence gate"

claimJoin058 : VideoClaimJoin
claimJoin058 = video-claim-join
  Video.claim058
  (unpaidCarrier "unlocated-14:14")
  "Identify DIA original document and inspect actual conclusion; report title and funding do not establish technological success"
  "Claim 058 at 14:14 remains subject to exact provenance/independent-evidence gate"

claimJoin059 : VideoClaimJoin
claimJoin059 = video-claim-join
  Video.claim059
  (unpaidCarrier "unlocated-14:40")
  "Identify DIA original document and inspect actual conclusion; report title and funding do not establish technological success"
  "Claim 059 at 14:40 remains subject to exact provenance/independent-evidence gate"

claimJoin060 : VideoClaimJoin
claimJoin060 = video-claim-join
  Video.claim060
  (unpaidCarrier "unlocated-15:01")
  "Identify DIA original document and inspect actual conclusion; report title and funding do not establish technological success"
  "Claim 060 at 15:01 remains subject to exact provenance/independent-evidence gate"

claimJoin061 : VideoClaimJoin
claimJoin061 = video-claim-join
  Video.claim061
  (unpaidCarrier "unlocated-15:10")
  "Identify DIA original document and inspect actual conclusion; report title and funding do not establish technological success"
  "Claim 061 at 15:10 remains subject to exact provenance/independent-evidence gate"

claimJoin062 : VideoClaimJoin
claimJoin062 = video-claim-join
  Video.claim062
  (unpaidCarrier "unlocated-15:22")
  "Identify DIA original document and inspect actual conclusion; report title and funding do not establish technological success"
  "Claim 062 at 15:22 remains subject to exact provenance/independent-evidence gate"

claimJoin063 : VideoClaimJoin
claimJoin063 = video-claim-join
  Video.claim063
  (pairedCarriers (atlasSource OSINT.foxReviewSource) (documentSource Source.houseApril2026))
  "Fox reports no public evidence linking deaths; official concern over unconfirmed cases does not establish systematic suppression"
  "Claim 063 at 15:40 remains subject to exact provenance/independent-evidence gate"

claimJoin064 : VideoClaimJoin
claimJoin064 = video-claim-join
  Video.claim064
  (documentSource Source.burischCamelot)
  "Same original Dan Burisch interview supports attribution of testimony only; repeated clips are not independent witnesses"
  "Claim 064 at 16:02 remains subject to exact provenance/independent-evidence gate"

claimJoin065 : VideoClaimJoin
claimJoin065 = video-claim-join
  Video.claim065
  (documentSource Source.burischCamelot)
  "Same original Dan Burisch interview supports attribution of testimony only; repeated clips are not independent witnesses"
  "Claim 065 at 16:09 remains subject to exact provenance/independent-evidence gate"

claimJoin066 : VideoClaimJoin
claimJoin066 = video-claim-join
  Video.claim066
  (unpaidCarrier "unlocated-16:49")
  "Quoted claims, scientific analogy and narrated synthesis require independent operational, physical, or contextual evidence"
  "Claim 066 at 16:49 remains subject to exact provenance/independent-evidence gate"

claimJoin067 : VideoClaimJoin
claimJoin067 = video-claim-join
  Video.claim067
  (unpaidCarrier "unlocated-17:13")
  "Quoted claims, scientific analogy and narrated synthesis require independent operational, physical, or contextual evidence"
  "Claim 067 at 17:13 remains subject to exact provenance/independent-evidence gate"

claimJoin068 : VideoClaimJoin
claimJoin068 = video-claim-join
  Video.claim068
  (unpaidCarrier "unlocated-17:42")
  "Quoted claims, scientific analogy and narrated synthesis require independent operational, physical, or contextual evidence"
  "Claim 068 at 17:42 remains subject to exact provenance/independent-evidence gate"

claimJoin069 : VideoClaimJoin
claimJoin069 = video-claim-join
  Video.claim069
  (documentSource Source.burischCamelot)
  "Same original Dan Burisch interview supports attribution of testimony only; repeated clips are not independent witnesses"
  "Claim 069 at 18:02 remains subject to exact provenance/independent-evidence gate"

claimJoin070 : VideoClaimJoin
claimJoin070 = video-claim-join
  Video.claim070
  (documentSource Source.bem2011)
  "NLM abstract pays the existence of Bem's 9-psychology-experiment paper, not the narration's anticipatory physiology or successful replication"
  "Claim 070 at 18:35 remains subject to exact provenance/independent-evidence gate"

claimJoin071 : VideoClaimJoin
claimJoin071 = video-claim-join
  Video.claim071
  (documentSource Source.burischCamelot)
  "Same original Dan Burisch interview supports attribution of testimony only; repeated clips are not independent witnesses"
  "Claim 071 at 19:15 remains subject to exact provenance/independent-evidence gate"

claimJoin072 : VideoClaimJoin
claimJoin072 = video-claim-join
  Video.claim072
  (documentSource Source.burischCamelot)
  "Same original Dan Burisch interview supports attribution of testimony only; repeated clips are not independent witnesses"
  "Claim 072 at 19:26 remains subject to exact provenance/independent-evidence gate"

claimJoin073 : VideoClaimJoin
claimJoin073 = video-claim-join
  Video.claim073
  (documentSource Source.burischCamelot)
  "Same original Dan Burisch interview supports attribution of testimony only; repeated clips are not independent witnesses"
  "Claim 073 at 20:00 remains subject to exact provenance/independent-evidence gate"

claimJoin074 : VideoClaimJoin
claimJoin074 = video-claim-join
  Video.claim074
  (documentSource Source.burischCamelot)
  "Same original Dan Burisch interview supports attribution of testimony only; repeated clips are not independent witnesses"
  "Claim 074 at 21:35 remains subject to exact provenance/independent-evidence gate"

claimJoin075 : VideoClaimJoin
claimJoin075 = video-claim-join
  Video.claim075
  (unpaidCarrier "unlocated-23:01")
  "Quoted claims, scientific analogy and narrated synthesis require independent operational, physical, or contextual evidence"
  "Claim 075 at 23:01 remains subject to exact provenance/independent-evidence gate"

claimJoin076 : VideoClaimJoin
claimJoin076 = video-claim-join
  Video.claim076
  (documentSource Source.burischCamelot)
  "Same original Dan Burisch interview supports attribution of testimony only; repeated clips are not independent witnesses"
  "Claim 076 at 24:09 remains subject to exact provenance/independent-evidence gate"

claimJoin077 : VideoClaimJoin
claimJoin077 = video-claim-join
  Video.claim077
  (documentSource Source.burischCamelot)
  "Same original Dan Burisch interview supports attribution of testimony only; repeated clips are not independent witnesses"
  "Claim 077 at 24:32 remains subject to exact provenance/independent-evidence gate"

claimJoin078 : VideoClaimJoin
claimJoin078 = video-claim-join
  Video.claim078
  (unpaidCarrier "unlocated-24:52")
  "Quoted claims, scientific analogy and narrated synthesis require independent operational, physical, or contextual evidence"
  "Claim 078 at 24:52 remains subject to exact provenance/independent-evidence gate"

claimJoin079 : VideoClaimJoin
claimJoin079 = video-claim-join
  Video.claim079
  (documentSource Source.burischCamelot)
  "Same original Dan Burisch interview supports attribution of testimony only; repeated clips are not independent witnesses"
  "Claim 079 at 26:39 remains subject to exact provenance/independent-evidence gate"

claimJoin080 : VideoClaimJoin
claimJoin080 = video-claim-join
  Video.claim080
  (documentSource Source.burischCamelot)
  "Same original Dan Burisch interview supports attribution of testimony only; repeated clips are not independent witnesses"
  "Claim 080 at 27:08 remains subject to exact provenance/independent-evidence gate"

claimJoin081 : VideoClaimJoin
claimJoin081 = video-claim-join
  Video.claim081
  (unpaidCarrier "unlocated-27:17")
  "Quoted claims, scientific analogy and narrated synthesis require independent operational, physical, or contextual evidence"
  "Claim 081 at 27:17 remains subject to exact provenance/independent-evidence gate"

claimJoin082 : VideoClaimJoin
claimJoin082 = video-claim-join
  Video.claim082
  (documentSource Source.burischCamelot)
  "Same original Dan Burisch interview supports attribution of testimony only; repeated clips are not independent witnesses"
  "Claim 082 at 28:41 remains subject to exact provenance/independent-evidence gate"

claimJoin083 : VideoClaimJoin
claimJoin083 = video-claim-join
  Video.claim083
  (documentSource Source.burischCamelot)
  "Same original Dan Burisch interview supports attribution of testimony only; repeated clips are not independent witnesses"
  "Claim 083 at 29:11 remains subject to exact provenance/independent-evidence gate"

claimJoin084 : VideoClaimJoin
claimJoin084 = video-claim-join
  Video.claim084
  (documentSource Source.burischCamelot)
  "Same original Dan Burisch interview supports attribution of testimony only; repeated clips are not independent witnesses"
  "Claim 084 at 29:49 remains subject to exact provenance/independent-evidence gate"

claimJoin085 : VideoClaimJoin
claimJoin085 = video-claim-join
  Video.claim085
  (documentSource Source.burischCamelot)
  "Same original Dan Burisch interview supports attribution of testimony only; repeated clips are not independent witnesses"
  "Claim 085 at 31:35 remains subject to exact provenance/independent-evidence gate"

claimJoin086 : VideoClaimJoin
claimJoin086 = video-claim-join
  Video.claim086
  (unpaidCarrier "unlocated-32:04")
  "Original carrier, exact source passage and independent outcome or alternative explanation remain separate obligations"
  "Claim 086 at 32:04 remains subject to exact provenance/independent-evidence gate"

allVideoClaimJoins : List VideoClaimJoin
allVideoClaimJoins =
  claimJoin001 ∷
  claimJoin002 ∷
  claimJoin003 ∷
  claimJoin004 ∷
  claimJoin005 ∷
  claimJoin006 ∷
  claimJoin007 ∷
  claimJoin008 ∷
  claimJoin009 ∷
  claimJoin010 ∷
  claimJoin011 ∷
  claimJoin012 ∷
  claimJoin013 ∷
  claimJoin014 ∷
  claimJoin015 ∷
  claimJoin016 ∷
  claimJoin017 ∷
  claimJoin018 ∷
  claimJoin019 ∷
  claimJoin020 ∷
  claimJoin021 ∷
  claimJoin022 ∷
  claimJoin023 ∷
  claimJoin024 ∷
  claimJoin025 ∷
  claimJoin026 ∷
  claimJoin027 ∷
  claimJoin028 ∷
  claimJoin029 ∷
  claimJoin030 ∷
  claimJoin031 ∷
  claimJoin032 ∷
  claimJoin033 ∷
  claimJoin034 ∷
  claimJoin035 ∷
  claimJoin036 ∷
  claimJoin037 ∷
  claimJoin038 ∷
  claimJoin039 ∷
  claimJoin040 ∷
  claimJoin041 ∷
  claimJoin042 ∷
  claimJoin043 ∷
  claimJoin044 ∷
  claimJoin045 ∷
  claimJoin046 ∷
  claimJoin047 ∷
  claimJoin048 ∷
  claimJoin049 ∷
  claimJoin050 ∷
  claimJoin051 ∷
  claimJoin052 ∷
  claimJoin053 ∷
  claimJoin054 ∷
  claimJoin055 ∷
  claimJoin056 ∷
  claimJoin057 ∷
  claimJoin058 ∷
  claimJoin059 ∷
  claimJoin060 ∷
  claimJoin061 ∷
  claimJoin062 ∷
  claimJoin063 ∷
  claimJoin064 ∷
  claimJoin065 ∷
  claimJoin066 ∷
  claimJoin067 ∷
  claimJoin068 ∷
  claimJoin069 ∷
  claimJoin070 ∷
  claimJoin071 ∷
  claimJoin072 ∷
  claimJoin073 ∷
  claimJoin074 ∷
  claimJoin075 ∷
  claimJoin076 ∷
  claimJoin077 ∷
  claimJoin078 ∷
  claimJoin079 ∷
  claimJoin080 ∷
  claimJoin081 ∷
  claimJoin082 ∷
  claimJoin083 ∷
  claimJoin084 ∷
  claimJoin085 ∷
  claimJoin086 ∷ []

-- A finite coverage theorem: the projection of the explicit same-row joins
-- reconstructs the original 86-row ledger, in order, without extra claims.
-- This proves enumeration/attachment integrity, NOT evidence sufficiency.
forgetProducer : List VideoClaimJoin → List Video.RawAttributedClaim
forgetProducer [] = []
forgetProducer (x ∷ xs) = transcriptClaim x ∷ forgetProducer xs

all86RowsAccountedFor :
  forgetProducer allVideoClaimJoins ≡ Video.transcriptClaims
all86RowsAccountedFor = refl

-- Negative promotion gates: no proof constructor exists to turn a merely
-- associated source into a witnessed causal event, replicated phenomenon,
-- same-person roster inclusion, or a validated hidden device.
data VideoCitationImpliesPhysics : Set where
data VideoCitationImpliesMurder : Set where
data HouseTenAutomaticallyEqualsVideoEleven : Set where
data InterviewRepeatCreatesIndependentWitness : Set where

noCitationPhysicsShortcut : VideoCitationImpliesPhysics → ⊥
noCitationPhysicsShortcut ()

noCitationMurderShortcut : VideoCitationImpliesMurder → ⊥
noCitationMurderShortcut ()

noTenToElevenShortcut : HouseTenAutomaticallyEqualsVideoEleven → ⊥
noTenToElevenShortcut ()

noInterviewIndependenceShortcut : InterviewRepeatCreatesIndependentWitness → ⊥
noInterviewIndependenceShortcut ()
