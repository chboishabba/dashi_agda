module DASHI.Culture.AmyEskridgeVideoOriginalClipLineageExact where

-- Source-role-exact clip lineage for the original Be Inspired video:
-- https://www.youtube.com/watch?v=acw16d6CCnY
-- "She Researched Something THEY DON'T ALLOW. Then She Died"
-- Be Inspired, published 2026-05-12 (channel-indexed), 32:47.
-- These are source locators, not independent validation.
-- Primary oral sources:
-- Amy Eskridge Zoom with Jeremy Rys and Mark Sokol, 2020,
-- original https://www.youtube.com/watch?v=l0O4cEIkUZc
-- transcript archived 2024-01-27:
-- https://blockedepistemology.substack.com/p/archive-amy-eskridge-zoom
-- Project Camelot, Kerry Cassidy / Bill Ryan interview with Dan Burisch,
-- "Out From Under Majestic", 2006:
-- https://projectcamelot.org/dan_burisch_interview_transcript_2.html
-- Project Camelot, Dan Burisch "Stargate Secrets", 2007:
-- https://projectcamelot.org/dan_burisch.html
-- Philip K Dick, speech at Metz, 1977:
-- https://www.youtube.com/watch?v=DQbYiXyRZjM
-- NOTE: not every Burisch edit comes from the SAME original interview.
-- Preserve distinction between 2006 Part 2 and 2007 Stargate Secrets.
-- Deutsch 1995 Noorderlicht interview identified by original video ID and
-- independent scholarly bibliography. Presentiment audiovisual clip still open;
-- Cornell 2010 Bem source quotation and Radin physiological studies remain
-- separate evidence objects.

open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

data ClipIdentityState : Set where
  exactWordingLocated : ClipIdentityState
  clipFamilyIdentified : ClipIdentityState
  voiceAttributedOriginalUnlocated : ClipIdentityState
  originalNotLocated : ClipIdentityState

record ClipLineage : Set where
  constructor clip-lineage
  field
    videoTime : String
    attributedVoice : String
    originalWork : String
    originalYear : String
    originalLocator : String
    bestOriginalOffset : String
    identityState : ClipIdentityState
    sourceClaimBoundary : String
open ClipLineage public

clip01 : ClipLineage
clip01 = clip-lineage
  "00:00–00:21"
  "Amy Eskridge"
  "Amy Eskridge Zoom, Jeremy Rys & Mark Sokol"
  "2020"
  "https://www.youtube.com/watch?v=l0O4cEIkUZc"
  "00:30–00:35 (multiple non-contiguous excerpts)"
  clipFamilyIdentified
  "NSA-list and kill/suppression allegations are secondhand story inside Amy's recorded first-person account"

clip02 : ClipLineage
clip02 = clip-lineage
  "00:31–01:23"
  "Amy Eskridge"
  "Amy Eskridge Zoom, Jeremy Rys & Mark Sokol"
  "2020"
  "https://blockedepistemology.substack.com/p/archive-amy-eskridge-zoom"
  "~02:53–02:57 (Lexus portion)"
  clipFamilyIdentified
  "Lexus account is an allegation voiced by Amy; independent plate/physical surveillance proof absent"

clip03 : ClipLineage
clip03 = clip-lineage
  "01:41–01:53"
  "Amy Eskridge"
  "Amy Eskridge Zoom, Jeremy Rys & Mark Sokol"
  "2020"
  "https://blockedepistemology.substack.com/p/archive-amy-eskridge-zoom"
  "~00:52–00:53 P-52 discussion"
  clipFamilyIdentified
  "Amy repeats P-52 future-human story, no verification"

clip04 : ClipLineage
clip04 = clip-lineage
  "02:04–02:35"
  "Dan Burisch; Project Camelot"
  "Out From Under Majestic / transcript Part 2"
  "2006"
  "https://projectcamelot.org/dan_burisch_interview_transcript_2.html"
  "2012: Two Timelines / P-45s section"
  exactWordingLocated
  "The verbatim P-45 question and 45,000-year answer appear in the older Burisch interview; not evidence of Majestic employment"

clip05 : ClipLineage
clip05 = clip-lineage
  "16:02–16:49"
  "Dan Burisch; Project Camelot"
  "Stargate Secrets"
  "2007"
  "https://projectavalon.net/lang/en/dan_burisch_stargate_secrets_interview_transcript_1_en.html"
  "Part 1 lines 284-289: Cube circulated among national elites; timeline segment exact offset open"
  clipFamilyIdentified
  "Two-timeline/yellow cube interviews; 2007 interview source only"

clip06 : ClipLineage
clip06 = clip-lineage
  "16:49–17:13"
  "Philip K. Dick"
  "If You Find This World Bad, You Should See Some of the Others"
  "1977"
  "https://www.youtube.com/watch?v=DQbYiXyRZjM"
  "Metz speech on déjà vu and concurrent realities"
  exactWordingLocated
  "Speaker's speculation/philosophy, not technical confirmation of time travel"

clip07 : ClipLineage
clip07 = clip-lineage
  "17:13–17:40"
  "David Deutsch"
  "Noorderlicht - The Multiverse (David Deutsch interview)"
  "1995"
  "https://www.youtube.com/watch?v=SDZ454K_lBY"
  "original public video ~20:10 onward; independent 2017 scholarly bibliography cites 1995 Noorderlicht recording"
  exactWordingLocated
  "Recorded Deutsch multiverse explanation, NOT operational proof of timeline modification; source publication independently cited in scholarly literature"

clip08 : ClipLineage
clip08 = clip-lineage
  "18:02–18:33"
  "Dan Burisch; Project Camelot"
  "Out From Under Majestic / Stargate Secrets family"
  "2006–2007"
  "https://projectcamelot.org/dan_burisch_interview_transcript_2.html"
  "timeline-one and timeline-two discussion; exact edited cut pending"
  clipFamilyIdentified
  "Burisch asserts claimed future branching; no independent timeline measurement"

clip09 : ClipLineage
clip09 = clip-lineage
  "18:35–19:10"
  "Unidentified interview speaker; narrator invokes Daryl Bem"
  "Daryl Bem paraphrase / unidentified original speaker; Radin is a separate experimental primary"
  "2010–2011"
  "https://news.cornell.edu/stories/2010/12/study-looks-brains-ability-see-future"
  "Cornell News 2010 reproduces near-identical Bem physiology explanation; exact audiovisual voice still NOT identified"
  voiceAttributedOriginalUnlocated
  "Do not silently label this as an actual Bem physiological trial; psychophysiological presentiment experiment by Radin is independent (not video speaker established)"

clip10 : ClipLineage
clip10 = clip-lineage
  "19:15–20:23"
  "Dan Burisch; Project Camelot"
  "Stargate Secrets"
  "2007"
  "https://projectavalon.net/lang/en/dan_burisch_stargate_secrets_interview_transcript_1_en.html"
  "Part 1 lines 164-186: Yellow Cube/Book and user's emotions"
  clipFamilyIdentified
  "Claim of cube operator emotion effect; no independent device evidence"

clip11 : ClipLineage
clip11 = clip-lineage
  "21:22–23:00"
  "Dan Burisch; Project Camelot"
  "Stargate Secrets"
  "2007"
  "https://projectavalon.net/lang/en/dan_burisch_stargate_secrets_interview_transcript_1_en.html"
  "Part 1 lines 537-579: rings, frequency and kaleidoscopes"
  clipFamilyIdentified
  "Technical-sounding apparatus descriptions remain unverified oral reports"

clip12 : ClipLineage
clip12 = clip-lineage
  "24:00–24:43"
  "Dan Burisch; Project Camelot"
  "Stargate Secrets"
  "2007"
  "https://projectavalon.net/lang/en/dan_burisch_stargate_secrets_interview_transcript_1_en.html"
  "Part 1 lines 91-109: Stargate and cylinder-seal genealogy"
  clipFamilyIdentified
  "Cylinder seal ancestry is speaker testimony, not archaeology/engineering proof"

clip13 : ClipLineage
clip13 = clip-lineage
  "26:39–27:15"
  "Dan Burisch; Project Camelot"
  "Stargate Secrets"
  "2007"
  "https://projectavalon.net/lang/en/dan_burisch_stargate_secrets_interview_transcript_2_en.html"
  "Part 2 lines 431-465: Frenchman Mountain and natural portals; exact segment offset open"
  clipFamilyIdentified
  "Geophysical anomaly does not establish a portal"

clip14 : ClipLineage
clip14 = clip-lineage
  "28:41–29:24"
  "Dan Burisch; Project Camelot"
  "Stargate Secrets"
  "2007"
  "https://projectavalon.net/lang/en/dan_burisch_stargate_secrets_interview_transcript_1_en.html"
  "Part 1 lines 50-76: over fifty devices, ERB"
  clipFamilyIdentified
  "Number over fifty is speaker report without inventory"

clip15 : ClipLineage
clip15 = clip-lineage
  "29:24–30:21"
  "Dan Burisch; Project Camelot"
  "Stargate Secrets"
  "2007"
  "https://projectavalon.net/lang/en/dan_burisch_stargate_secrets_interview_transcript_1_en.html"
  "Part 1 lines 630-663: non-use and predicted 2016/2017 restoration"
  clipFamilyIdentified
  "2016/2017 reactivation prediction is stated without evidence of occurrence"

clip16 : ClipLineage
clip16 = clip-lineage
  "31:26–32:04"
  "Dan Burisch; Project Camelot"
  "Stargate Secrets"
  "2007"
  "https://projectavalon.net/lang/en/dan_burisch_stargate_secrets_interview_transcript_1_en.html"
  "Part 1 lines 664-671: three components allegedly separated EU/UN/NATO"
  clipFamilyIdentified
  "Claimed distribution of three components has no custody or procurement receipt"

originalClipLineages : List ClipLineage
originalClipLineages =
  clip01 ∷
  clip02 ∷
  clip03 ∷
  clip04 ∷
  clip05 ∷
  clip06 ∷
  clip07 ∷
  clip08 ∷
  clip09 ∷
  clip10 ∷
  clip11 ∷
  clip12 ∷
  clip13 ∷
  clip14 ∷
  clip15 ∷
  clip16 ∷ []

-- Source repetition controls: no source-to-fact coercion.
data ReusedInterviewEqualsIndependentWitness : Set where
data EditedClipProvesInstitutionalRecord : Set where
data OriginalClipDateEqualsEditedUploadDate : Set where

noIndependentWitnessByRepetition : ReusedInterviewEqualsIndependentWitness → ⊥
noIndependentWitnessByRepetition ()

noInstitutionFromInterview : EditedClipProvesInstitutionalRecord → ⊥
noInstitutionFromInterview ()

noOriginalDateFromUpload : OriginalClipDateEqualsEditedUploadDate → ⊥
noOriginalDateFromUpload ()
