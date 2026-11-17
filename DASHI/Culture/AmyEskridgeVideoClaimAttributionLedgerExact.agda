module DASHI.Culture.AmyEskridgeVideoClaimAttributionLedgerExact where

-- DASHI extension: transcription and provenance ledger for the supplied
-- 32:44 video transcript "She Researched Something THEY DON'T ALLOW. Then She Died".
-- Source: user-provided transcript on 17 November 2026, timestamps included.
-- Not a scholarly source; title is a transcript identifier, not an endorsement.
-- External source leads (not automatically inspected primary evidence):
-- Amy Eskridge, A Historical Perspective on Anti-Gravity Technology,
-- HAL5, December 2018:
-- https://www.hal5.org/PDF/HAL5-Dec2018-Talk-AntiGravity.pdf
-- Dan Burisch, "Stargate Secrets", Project Camelot, June 2007:
-- https://projectcamelot.org/dan_burisch.html
-- Daryl J Bem, Feeling the Future, JPSP 100(3), 2011,
-- DOI 10.1037/a0021524
-- Attribution policy: Docs/SourceAttributionPolicy.md.
-- Claim capture != independent verification != causation != proof.
-- Statuses record an audit queue, never established physics.
-- This row ledger is intentionally separate from the pre-existing 71-page
-- attachment: no transfer of evidence authority across source objects.

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

record RawAttributedClaim : Set where
  constructor claim
  field
    timestamp : String
    propositionText : String
    speaker : String
    purportedCarrier : String
    currentAuditStatus : String
    nextReceipt : String

claim001 : RawAttributedClaim
claim001 = claim "00:00" "NSA kill/suppression warning quotation" "clip" "unlocated" "unverified" "identify speaker and recording"

claim002 : RawAttributedClaim
claim002 = claim "00:05" "NSA maintains list of independent antigravity discoverers" "clip" "unlocated" "unverified" "original NSA record"

claim003 : RawAttributedClaim
claim003 = claim "00:11" "Antigravity independently discovered four other times and suppressed" "clip" "unlocated" "unverified" "identify inventors and outcomes"

claim004 : RawAttributedClaim
claim004 = claim "00:21" "Eleven scientists recently vanished or died unusually" "narrator" "unnamed roster" "unverified" "enumerated roster plus event records and denominator"

claim005 : RawAttributedClaim
claim005 = claim "00:31" "Amy Eskridge physically surveilled" "Eskridge clip" "interview quotation" "reported" "original recording and independent investigation"

claim006 : RawAttributedClaim
claim006 = claim "00:36" "Dark-window Lexus repeatedly parked outside residence" "Eskridge clip" "interview quotation" "reported" "dated photos and vehicle records"

claim007 : RawAttributedClaim
claim007 = claim "01:03" "Person changed Lexus license plate within sight" "Eskridge clip" "interview quotation" "reported" "recording and vehicle registry"

claim008 : RawAttributedClaim
claim008 = claim "01:23" "Others on the list had NASA Los Alamos or military links" "narrator" "unnamed roster" "unverified" "named people and employment records"

claim009 : RawAttributedClaim
claim009 = claim "01:32" "Eskridge researched antigravity propulsion and died in 2022" "narrator" "biography" "mixed" "employment publications and official death record"

claim010 : RawAttributedClaim
claim010 = claim "01:41" "P-52s are humans from 52000 years in future" "Eskridge clip" "interview quotation" "reported" "physical corroboration"

claim011 : RawAttributedClaim
claim011 = claim "01:54" "Dan Burisch worked inside Majestic 12" "narrator" "interview attribution" "unverified" "authenticated programme and employment records"

claim012 : RawAttributedClaim
claim012 = claim "02:04" "P-45 humans coexist 45000 years ahead on another timeline" "Burisch clip" "Project Camelot" "reported" "physical corroboration"

claim013 : RawAttributedClaim
claim013 = claim "02:35" "Sources say Eskridge worked on antigravity propulsion system" "narrator" "unnamed secondary" "unverified" "named source technical apparatus"

claim014 : RawAttributedClaim
claim014 = claim "02:42" "Antigravity technology would obsolete oil aerospace and defence" "narrator" "economic inference" "unverified" "energetic technoeconomic counterfactual"

claim015 : RawAttributedClaim
claim015 = claim "03:02" "Eskridge published a research presentation" "narrator" "HAL5 presentation" "located" "inspect December 2018 HAL5 slides"

claim016 : RawAttributedClaim
claim016 = claim "03:14" "Antigravity researchers repeatedly disappear after progress" "narrator" "pattern inference" "unverified" "cohort controls baseline mechanisms"

claim017 : RawAttributedClaim
claim017 = claim "03:20" "Newtonian and Einstein gravity are two mathematically correct explanations" "narrator" "physics summary" "oversimplified" "specify approximation domains"

claim018 : RawAttributedClaim
claim018 = claim "04:28" "Three non-gravity forces are described by Standard Model" "narrator" "physics summary" "background" "standard textbooks"

claim019 : RawAttributedClaim
claim019 = claim "04:54" "No graviton has been detected" "narrator" "physics summary" "background" "particle evidence review"

claim020 : RawAttributedClaim
claim020 = claim "05:22" "Any method reducing gravitational effect counts as antigravity" "narrator" "definition" "ambiguous" "distinguish support lift shielding metric"

claim021 : RawAttributedClaim
claim021 = claim "05:32" "Reducing gravity would fundamentally change propulsion energy cost" "narrator" "engineering extrapolation" "unverified" "whole-system energy momentum accounting"

claim022 : RawAttributedClaim
claim022 = claim "06:21" "Thomas Townsend Brown invented a high-voltage gravitator" "narrator" "Brown patents" "located" "original patents test reports"

claim023 : RawAttributedClaim
claim023 = claim "06:40" "Brown performed vacuum test and effect was non-ionic" "narrator" "unspecified experiment" "unverified" "original vacuum protocol and replication"

claim024 : RawAttributedClaim
claim024 = claim "06:46" "Brown filed a 1960 patent" "narrator" "US2949550A" "located" "patent specification"

claim025 : RawAttributedClaim
claim025 = claim "06:51" "Tesla filed space-drive patent 1655144" "narrator" "misattributed patent" "contradicted" "compare US1655144 and US1655114"

claim026 : RawAttributedClaim
claim026 = claim "07:01" "Tesla proposed ether vortices and electropulsation space drive" "narrator" "historical assertions" "mixed" "original Tesla writings"

claim027 : RawAttributedClaim
claim027 = claim "07:22" "US government seized Tesla papers and fate remains unclear" "narrator" "custody narrative" "mixed" "historical custody inventories"

claim028 : RawAttributedClaim
claim028 = claim "07:32" "Babson founded Gravity Research Foundation in 1948" "narrator" "institution history" "located" "foundation records"

claim029 : RawAttributedClaim
claim029 = claim "07:42" "Hawking and five later Nobel laureates won foundation prizes" "narrator" "prize history" "needs audit" "award records precise counts"

claim030 : RawAttributedClaim
claim030 = claim "07:59" "John Searl claimed free-energy antigravity generator in 1946" "narrator" "inventor testimony" "reported" "original apparatus and independent tests"

claim031 : RawAttributedClaim
claim031 = claim "08:15" "Norman Dean claimed exhaustless reactionless drive" "narrator" "patent invention" "reported" "patent and friction controlled replication"

claim032 : RawAttributedClaim
claim032 = claim "08:32" "US military took serious interest in Dean drive" "narrator" "unnamed military records" "unverified" "agency documents"

claim033 : RawAttributedClaim
claim033 = claim "08:38" "Henry Wallace patented nuclear-spin rotating field device" "narrator" "US3626605A US3626606A" "located" "patent claims and tests"

claim034 : RawAttributedClaim
claim034 = claim "09:01" "Eric Laithwaite demonstrated unusual gyro behaviour in 1974" "narrator" "Royal Institution lecture" "traceable" "original lecture recording"

claim035 : RawAttributedClaim
claim035 = claim "09:19" "Royal Institution expelled Laithwaite for his gyro claims" "narrator" "institution allegation" "unverified" "fellowship and meeting records"

claim036 : RawAttributedClaim
claim036 = claim "09:30" "Ning Li theorized gravitational effects of superconductors" "narrator" "Li Torr papers" "traceable" "papers exact hypotheses"

claim037 : RawAttributedClaim
claim037 = claim "09:55" "Li collaborated with NASA Marshall" "narrator" "NASA agreement" "traceable" "NASA NCC8-124 project records"

claim038 : RawAttributedClaim
claim038 = claim "09:59" "Popular Mechanics published Li work in 1999 then removed article" "narrator" "magazine article" "mixed" "issue archive and publishing history"

claim039 : RawAttributedClaim
claim039 = claim "10:03" "Li founded AC Gravity LLC and received DoD half-million contract" "narrator" "procurement report" "partially located" "original Army agreement award and closeout"

claim040 : RawAttributedClaim
claim040 = claim "10:16" "Li disappeared from public record" "narrator" "absence inference" "unverified" "chronological record and family evidence"

claim041 : RawAttributedClaim
claim041 = claim "10:27" "Li suffered vehicle strike in 2014 and later died" "narrator" "biography event" "needs primary" "incident and death documentation"

claim042 : RawAttributedClaim
claim042 = claim "10:34" "Li accident suspicious" "narrator" "online speculation" "unverified" "evidence for foul play"

claim043 : RawAttributedClaim
claim043 = claim "10:43" "Podkletnov observed approximately 2 percent weight reduction" "narrator" "scientific report" "reported" "original methodology independent controls"

claim044 : RawAttributedClaim
claim044 = claim "10:58" "Podkletnov collaborated with NASA and patented device in 2001" "narrator" "patent and agency claim" "mixed" "patent records and NASA collaboration"

claim045 : RawAttributedClaim
claim045 = claim "11:05" "Tampere University removed Podkletnov" "narrator" "institution allegation" "unverified" "employment records"

claim046 : RawAttributedClaim
claim046 = claim "11:08" "Giovanni Modanese Wikipedia page deleted" "narrator" "web history assertion" "unverified" "Wikipedia log"

claim047 : RawAttributedClaim
claim047 = claim "11:12" "Claude Poher partially replicated Podkletnov" "narrator" "claimed experiment" "reported" "primary paper distinct physical setup"

claim048 : RawAttributedClaim
claim048 = claim "11:19" "NASA tested Poher apparatus in 2015 without publishing outcome" "narrator" "unnamed NASA test" "unverified" "test identifier and report"

claim049 : RawAttributedClaim
claim049 = claim "11:31" "1973 Mansfield Amendment prohibited non-military DoD research" "narrator" "statute" "misdated" "1969 amendment and later versions"

claim050 : RawAttributedClaim
claim050 = claim "11:42" "Restriction forced antigravity into classified budgets or private sector" "narrator" "causal inference" "unverified" "classification directives funding records"

claim051 : RawAttributedClaim
claim051 = claim "12:01" "James Woodward proposed Mach effect thrust" "narrator" "published research" "traceable" "theory and independent thrust measurements"

claim052 : RawAttributedClaim
claim052 = claim "12:24" "Woodward Mach effects enable negative mass warp drive" "narrator" "speculative extrapolation" "unverified" "conditions and physical feasibility"

claim053 : RawAttributedClaim
claim053 = claim "12:36" "Boeing Phantom Works GRASP publicly admitted only in 2014" "narrator" "2002 Jane's reporting" "contradicted chronology" "Nick Cook July 2002 report"

claim054 : RawAttributedClaim
claim054 = claim "12:55" "Boeing GRASP examined Podkletnov gravity research" "narrator" "Jane's report" "traceable" "programme records and outputs"

claim055 : RawAttributedClaim
claim055 = claim "13:14" "TR3B triangular plasma antigravity craft exists" "narrator" "anonymous witnesses" "unverified" "craft identification independent instrument data"

claim056 : RawAttributedClaim
claim056 = claim "13:42" "AATIP ran 2007 to 2012 and disclosed in 2017" "narrator" "DIA records press" "traceable" "AAWSAP AATIP distinction and dated records"

claim057 : RawAttributedClaim
claim057 = claim "14:07" "FOIA released titles of 38 DIA studies" "narrator" "FOIA inventory" "traceable" "exact inventory versions and counts"

claim058 : RawAttributedClaim
claim058 = claim "14:14" "Eric Davis wrote Traversable Wormholes Stargates and Negative Energy" "narrator" "DIA research paper" "located" "original DIA report"

claim059 : RawAttributedClaim
claim059 = claim "14:40" "Warp Drive Dark Energy and Manipulation of Extra Dimensions funded" "narrator" "DIA research paper" "located" "original report"

claim060 : RawAttributedClaim
claim060 = claim "15:01" "Antigravity for Aerospace Applications funded" "narrator" "DIA research paper" "located" "original report"

claim061 : RawAttributedClaim
claim061 = claim "15:10" "Advanced Space Propulsion Based on Vacuum Engineering funded" "narrator" "DIA research paper" "located" "original report"

claim062 : RawAttributedClaim
claim062 = claim "15:22" "Pentagon papers were kept secret for nearly decade" "narrator" "classification narrative" "needs audit" "contract dates release restrictions"

claim063 : RawAttributedClaim
claim063 = claim "15:40" "Every researcher making real progress disappeared and findings classified" "narrator" "generalised causal pattern" "unverified" "complete roster independent events and selection denominator"

claim064 : RawAttributedClaim
claim064 = claim "16:02" "Two or more concurrent timelines exist" "Burisch clip" "Project Camelot" "reported" "physical test and independent evidence"

claim065 : RawAttributedClaim
claim065 = claim "16:09" "Elites circulated a cube to choose future paths" "Burisch clip" "Project Camelot" "reported" "object custody and instrumentation"

claim066 : RawAttributedClaim
claim066 = claim "16:49" "Philip K Dick advocated recurrent overlapping present lives" "Dick clip" "1977 Metz speech" "traceable" "full speech context"

claim067 : RawAttributedClaim
claim067 = claim "17:13" "David Deutsch says other universes interfere quantum mechanically" "Deutsch clip" "many-worlds interview" "traceable" "original interview and theory context"

claim068 : RawAttributedClaim
claim068 = claim "17:42" "Shared false memories indicate timeline instability" "narrator" "Mandela-effect inference" "unverified" "cognitive controls independent physical prediction"

claim069 : RawAttributedClaim
claim069 = claim "18:02" "We live in modified timeline one due to interventions" "Burisch clip" "Project Camelot" "reported" "independent falsifiable evidence"

claim070 : RawAttributedClaim
claim070 = claim "18:35" "Daryl Bem experiments demonstrated anticipatory physiology" "narrator and clip" "Bem 2011 and separate presentiment study" "conflated" "identify precise footage experimental methods replication"

claim071 : RawAttributedClaim
claim071 = claim "19:15" "Yellow cube interacted with user to change seen futures" "Burisch clip" "Project Camelot" "reported" "device record independent test"

claim072 : RawAttributedClaim
claim072 = claim "19:26" "Looking Glass displays future probabilities" "Burisch clip" "Project Camelot" "reported" "device measurement and calibration"

claim073 : RawAttributedClaim
claim073 = claim "20:00" "Emotions alter provenance of cube output" "Burisch clip" "Project Camelot" "reported" "blinded reproducible protocol"

claim074 : RawAttributedClaim
claim074 = claim "21:35" "Looking Glass uses energetic concentric rings and central barrel" "Burisch clip" "Project Camelot" "reported" "engineering drawings and apparatus"

claim075 : RawAttributedClaim
claim075 = claim "23:01" "Repeated frame appearance gives calibrated future probabilities" "narrator" "interpretive synthesis" "unverified" "original quantitative predictions and scoring"

claim076 : RawAttributedClaim
claim076 = claim "24:09" "Looking Glass reverse-engineered from Stargate and cylinder seals" "Burisch clip" "Project Camelot" "reported" "authenticated archaeological engineering chain"

claim077 : RawAttributedClaim
claim077 = claim "24:32" "Stargates built to contact visitors from other timelines" "Burisch clip" "Project Camelot" "reported" "independent programme evidence"

claim078 : RawAttributedClaim
claim078 = claim "24:52" "Natural geophysical hotspots allow time-space portals" "narrator" "analogy and unnamed accounts" "unverified" "site-specific portal measurement"

claim079 : RawAttributedClaim
claim079 = claim "26:39" "Planet has natural electromagnetic nodes that open wormholes" "Burisch clip" "Project Camelot" "reported" "site observable distinct from magnetic anomaly"

claim080 : RawAttributedClaim
claim080 = claim "27:08" "Frenchman Mountain is an example portal site" "Burisch clip" "Project Camelot" "reported" "geophysical and independent portal observations"

claim081 : RawAttributedClaim
claim081 = claim "27:17" "Governments secretly mapped global unusual network of sites" "narrator" "unnamed agencies" "unverified" "named mapping dataset and relevance"

claim082 : RawAttributedClaim
claim082 = claim "28:41" "More than fifty manmade Stargate access devices existed" "Burisch clip" "Project Camelot" "reported" "inventory engineering custody"

claim083 : RawAttributedClaim
claim083 = claim "29:11" "Manmade devices piggyback natural Einstein Rosen bridges" "Burisch clip" "Project Camelot" "reported" "physics bridge conditions and evidence"

claim084 : RawAttributedClaim
claim084 = claim "29:49" "Looking Glass technology currently not used" "Burisch clip" "Project Camelot" "reported" "operational records"

claim085 : RawAttributedClaim
claim085 = claim "31:35" "Devices dismantled components split EU UN and NATO" "Burisch clip" "Project Camelot" "reported" "official custody transfer inventory"

claim086 : RawAttributedClaim
claim086 = claim "32:04" "Narrator claims recurring pattern despite uncertainty" "narrator" "rhetorical synthesis" "not evidence" "distinguish theme from causal proof"

transcriptClaims : List RawAttributedClaim
transcriptClaims =
  claim001 ∷
  claim002 ∷
  claim003 ∷
  claim004 ∷
  claim005 ∷
  claim006 ∷
  claim007 ∷
  claim008 ∷
  claim009 ∷
  claim010 ∷
  claim011 ∷
  claim012 ∷
  claim013 ∷
  claim014 ∷
  claim015 ∷
  claim016 ∷
  claim017 ∷
  claim018 ∷
  claim019 ∷
  claim020 ∷
  claim021 ∷
  claim022 ∷
  claim023 ∷
  claim024 ∷
  claim025 ∷
  claim026 ∷
  claim027 ∷
  claim028 ∷
  claim029 ∷
  claim030 ∷
  claim031 ∷
  claim032 ∷
  claim033 ∷
  claim034 ∷
  claim035 ∷
  claim036 ∷
  claim037 ∷
  claim038 ∷
  claim039 ∷
  claim040 ∷
  claim041 ∷
  claim042 ∷
  claim043 ∷
  claim044 ∷
  claim045 ∷
  claim046 ∷
  claim047 ∷
  claim048 ∷
  claim049 ∷
  claim050 ∷
  claim051 ∷
  claim052 ∷
  claim053 ∷
  claim054 ∷
  claim055 ∷
  claim056 ∷
  claim057 ∷
  claim058 ∷
  claim059 ∷
  claim060 ∷
  claim061 ∷
  claim062 ∷
  claim063 ∷
  claim064 ∷
  claim065 ∷
  claim066 ∷
  claim067 ∷
  claim068 ∷
  claim069 ∷
  claim070 ∷
  claim071 ∷
  claim072 ∷
  claim073 ∷
  claim074 ∷
  claim075 ∷
  claim076 ∷
  claim077 ∷
  claim078 ∷
  claim079 ∷
  claim080 ∷
  claim081 ∷
  claim082 ∷
  claim083 ∷
  claim084 ∷
  claim085 ∷
  claim086 ∷ []

-- These are *impossibility of automatic promotion* boundaries in the
-- representation, not claims that an empirical theory has been refuted.
-- A transcript quotation carries no independent verification constructor.
data TranscriptAloneEstablishesPhysics : Set where
data InterviewAloneEstablishesCausality : Set where
data PatentAloneEstablishesReplication : Set where
data SourceTitleAloneEstablishesTruth : Set where

transcriptNotPhysicsProof : TranscriptAloneEstablishesPhysics → ⊥
transcriptNotPhysicsProof ()

interviewNotCausalProof : InterviewAloneEstablishesCausality → ⊥
interviewNotCausalProof ()

patentNotReplicationProof : PatentAloneEstablishesReplication → ⊥
patentNotReplicationProof ()

citationNotTruthProof : SourceTitleAloneEstablishesTruth → ⊥
citationNotTruthProof ()

-- All audit classifications are attributed judgements in this new DASHI
-- ledger; they are not original assertions by the cited interviewees.
data AuditBoundary : Set where
  carrierIdentityDistinctFromClaimContent : AuditBoundary
  sourceClaimDistinctFromDASHIInference : AuditBoundary
  missingEvidenceDoesNotProveSuppression : AuditBoundary

boundaryStillExplicit : AuditBoundary ≡ AuditBoundary
boundaryStillExplicit = refl
