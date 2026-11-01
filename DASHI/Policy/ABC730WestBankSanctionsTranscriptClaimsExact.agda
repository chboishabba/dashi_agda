module DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Transcript-native claim ledger for the user-supplied ABC 7.30 transcript,
-- 9 September 2026.  This owner records what the transcript says and how it
-- says it.  It does NOT silently promote embedded allegations, legal claims,
-- causal claims, predictions, or evaluative rhetoric into independently
-- verified world facts.

record SourceSpan : Set where
  constructor span
  field
    firstLine : String
    lastLine : String
open SourceSpan public

data ClaimClass : Set where
  reporterNarration : ClaimClass
  attributedQuotation : ClaimClass
  reportedAllegation : ClaimClass
  policyPosition : ClaimClass
  legalCharacterisation : ClaimClass
  causalOrPredictive : ClaimClass
  evaluativeRhetoric : ClaimClass
  biographicalClaim : ClaimClass
  interviewQuestion : ClaimClass
  incidentalSpeech : ClaimClass

data TranscriptSupport : Set where
  directTranscriptSupport : TranscriptSupport
  nestedAttributionOnly : TranscriptSupport
  questionOnly : TranscriptSupport
  speakerUnresolved : TranscriptSupport

record TranscriptClaim : Set where
  constructor transcriptClaim
  field
    claimId : String
    sourceSpan : SourceSpan
    speakerOrAttributor : String
    claimClass : ClaimClass
    support : TranscriptSupport
    proposition : String
    residual : String
open TranscriptClaim public

------------------------------------------------------------------------
-- Reporter package: lines 2-32.

c001 = transcriptClaim "ABC730-2026-09-09-C001" (span "2" "2") "ABC reporter" reporterNarration directTranscriptSupport "Britain's new foreign minister delivered a major speech in the House of Commons." "Transcript support only; 'historic' is evaluative framing."
c002 = transcriptClaim "ABC730-2026-09-09-C002" (span "2" "2") "ABC reporter" legalCharacterisation nestedAttributionOnly "The speech declared Israel's occupation of the West Bank unlawful." "Legal correctness requires independent authority verification."
c003 = transcriptClaim "ABC730-2026-09-09-C003" (span "2" "2") "ABC reporter" policyPosition directTranscriptSupport "Ed Miliband announced trade bans concerning Israeli settlers/settlements." "Exact legal instrument and scope require source instrument."
c004 = transcriptClaim "ABC730-2026-09-09-C004" (span "2" "4") "ABC reporter" reporterNarration directTranscriptSupport "Australia has worked with the UK and other countries against settlement expansion but did not join this UK action." "Transcript-level policy comparison."
c005 = transcriptClaim "ABC730-2026-09-09-C005" (span "4" "6") "ABC reporter" reporterNarration directTranscriptSupport "Israeli bulldozers were shown/reported tearing down a Palestinian farmer's olive groves." "Underlying event requires independent event-source verification."
c006 = transcriptClaim "ABC730-2026-09-09-C006" (span "6" "6") "Palestinian farmer" attributedQuotation directTranscriptSupport "Seeing olive trees uprooted by bulldozers breaks his heart." "Speaker identity is contextual rather than explicitly labelled in transcript text."
c007 = transcriptClaim "ABC730-2026-09-09-C007" (span "6" "6") "local officials, via ABC reporter" reportedAllegation nestedAttributionOnly "Two Palestinian teenagers were killed by Israeli settlers and soldiers in an attack on their village." "ABC attributes this to local officials; event responsibility not independently established by transcript."
c008 = transcriptClaim "ABC730-2026-09-09-C008" (span "6" "8") "ABC reporter" causalOrPredictive directTranscriptSupport "Settlement activity is adding to anxiety and fears about the future of a Palestinian state." "Causal/predictive framing; not a standalone measured causal estimate."
c009 = transcriptClaim "ABC730-2026-09-09-C009" (span "8" "8") "Ed Miliband" evaluativeRhetoric directTranscriptSupport "Events in Palestine under the eyes of the international community produce a deep sense of shame." "Normative/evaluative statement attributed in transcript."
c010 = transcriptClaim "ABC730-2026-09-09-C010" (span "8" "8") "ABC reporter" biographicalClaim directTranscriptSupport "Ed Miliband is the son of a Holocaust survivor." "Biographical claim present in transcript; external verification separate."
c011 = transcriptClaim "ABC730-2026-09-09-C011" (span "8" "10") "ABC reporter" reporterNarration directTranscriptSupport "Miliband became the first British foreign secretary to declare the post-1967 West Bank occupation unlawful." "Historical-first claim requires independent historical verification."
c012 = transcriptClaim "ABC730-2026-09-09-C012" (span "10" "10") "Ed Miliband" legalCharacterisation directTranscriptSupport "The British government had long said settlements were illegal but had remained silent on legality of the occupation as a whole." "Statement of UK government's prior position as attributed to Miliband."
c013 = transcriptClaim "ABC730-2026-09-09-C013" (span "10" "12") "Ed Miliband / ABC reporter" legalCharacterisation nestedAttributionOnly "The International Court of Justice concluded in 2024 that the occupation was unlawful." "Requires exact ICJ source and scope before legal promotion."
c014 = transcriptClaim "ABC730-2026-09-09-C014" (span "12" "12") "Ed Miliband" policyPosition directTranscriptSupport "The official view of the British government is that the occupation is unlawful." "Government-position claim, distinct from independent legal truth."
c015 = transcriptClaim "ABC730-2026-09-09-C015" (span "12" "14") "ABC reporter / Miliband" reporterNarration directTranscriptSupport "Israel issued tenders for more than 1,200 homes in the E1 area east of Jerusalem." "Underlying tender facts require source verification."
c016 = transcriptClaim "ABC730-2026-09-09-C016" (span "14" "14") "Ed Miliband" causalOrPredictive directTranscriptSupport "E1 would create facts on the ground making a two-state solution unviable." "Predictive/causal political claim."
c017 = transcriptClaim "ABC730-2026-09-09-C017" (span "14" "14") "ABC reporter / UK government" policyPosition directTranscriptSupport "Britain is moving to impose an import ban on goods from settlements in the occupied territories." "Policy action as reported in transcript."
c018 = transcriptClaim "ABC730-2026-09-09-C018" (span "14" "16") "UK government / Miliband" reportedAllegation nestedAttributionOnly "There is ethnic cleansing of Palestinians in parts of the West Bank perpetrated by settler terrorists." "Serious allegation; transcript records attribution only."
c019 = transcriptClaim "ABC730-2026-09-09-C019" (span "16" "16") "UK government / Miliband" reportedAllegation nestedAttributionOnly "The Israeli government has turned a blind eye to settler violence and members have supported forced displacement." "Attribution preserved; factual/legal verification separate."
c020 = transcriptClaim "ABC730-2026-09-09-C020" (span "16" "18") "Israeli foreign minister" evaluativeRhetoric directTranscriptSupport "The British foreign secretary's accusations were outrageous lies." "Counter-characterisation; does not itself refute underlying claims."
c021 = transcriptClaim "ABC730-2026-09-09-C021" (span "16" "18") "ABC reporter" reporterNarration directTranscriptSupport "Israel's foreign minister responded with a threat/vow to close the British Consulate in East Jerusalem." "Reported policy response."
c022 = transcriptClaim "ABC730-2026-09-09-C022" (span "18" "18") "Israeli position" policyPosition nestedAttributionOnly "Foreign activity in the area must occur through accepted channels and without violating Israel's sovereignty." "Attributed sovereignty position; legal merits separate."
c023 = transcriptClaim "ABC730-2026-09-09-C023" (span "18" "20") "ABC reporter" reporterNarration directTranscriptSupport "Canada, France, Spain and Sweden were among countries planning restrictions on trade from settlements." "Country-specific implementation details require independent verification."
c024 = transcriptClaim "ABC730-2026-09-09-C024" (span "20" "20") "ABC reporter" reporterNarration directTranscriptSupport "The Trump administration was reluctant to criticise Britain's move and said it shared the goal of stability." "Reported US reaction."
c025 = transcriptClaim "ABC730-2026-09-09-C025" (span "20" "20") "ABC reporter" reporterNarration directTranscriptSupport "Germany, Italy, Japan and New Zealand were notable non-participants/abstentions in the described action." "Exact status differs by state and requires source-specific verification."
c026 = transcriptClaim "ABC730-2026-09-09-C026" (span "22" "22") "ABC reporter" policyPosition directTranscriptSupport "The Australian government chose not to join Britain's blanket trade ban at that time." "Supported as transcript-level Australian position."
c027 = transcriptClaim "ABC730-2026-09-09-C027" (span "22" "22") "ABC reporter" reporterNarration directTranscriptSupport "Israel's ambassador welcomed Australia's decision not to join the blanket ban." "Reported diplomatic reaction."
c028 = transcriptClaim "ABC730-2026-09-09-C028" (span "22" "22") "Penny Wong / Australian government" policyPosition directTranscriptSupport "Australia was not at that time pursuing a blanket-style import ban." "Directly represented in transcript."
c029 = transcriptClaim "ABC730-2026-09-09-C029" (span "22" "22") "Penny Wong / Australian government" policyPosition directTranscriptSupport "Australia cited implementation concerns and unintended consequences for Australian businesses, Palestinians and Israelis." "Rationale attribution; effectiveness/validity of rationale separate."
c030 = transcriptClaim "ABC730-2026-09-09-C030" (span "22" "24") "progressive/backbench voice, speaker unresolved" policyPosition speakerUnresolved "One cannot support Palestinian statehood while ignoring settlements that undermine the emergence of that state." "Exact speaker identity not labelled in supplied transcript."
c031 = transcriptClaim "ABC730-2026-09-09-C031" (span "24" "24") "speaker unresolved" policyPosition speakerUnresolved "Australia needs to take action on settlements." "Speaker unresolved at transcript cut."
c032 = transcriptClaim "ABC730-2026-09-09-C032" (span "24" "24") "speaker unresolved" evaluativeRhetoric speakerUnresolved "The stated reason for not taking action is apparently to help Palestinians; this is 'unbelievable gaslighting from Labor'." "Exact wording supported; speaker identity unresolved."
c033 = transcriptClaim "ABC730-2026-09-09-C033" (span "24" "24") "government-defending voice, speaker unresolved" causalOrPredictive speakerUnresolved "The objective is a two-state solution, and it is uncertain whether these sanctions advance that objective." "Speaker identity unresolved; substantive policy assessment not promoted."
c034 = transcriptClaim "ABC730-2026-09-09-C034" (span "26" "26") "ABC reporter" reporterNarration directTranscriptSupport "A year earlier Australia worked with Canada, France and the UK on recognition of a Palestinian state." "Historical policy claim requires underlying source for independent promotion."
c035 = transcriptClaim "ABC730-2026-09-09-C035" (span "26" "28") "ABC reporter" policyPosition directTranscriptSupport "Australia instead emphasised direct action targeting supporters of the settler movement, including sanctions preventing Australians trading with sanctioned persons/entities in the West Bank." "Legal scope of sanctions requires instrument-level verification."
c036 = transcriptClaim "ABC730-2026-09-09-C036" (span "28" "28") "ABC reporter" policyPosition directTranscriptSupport "Other reasons advanced against the UK-style ban included Australia's trading-nation status and the view that the ban is a blunt instrument." "Attributed policy rationales, not independently validated premises."
c037 = transcriptClaim "ABC730-2026-09-09-C037" (span "28" "28") "ABC reporter" reporterNarration directTranscriptSupport "The Prime Minister has a long history of political conflict with the Greens over boycott, divestment and sanctions against Israel." "Historical/political framing requiring separate source history if promoted."
c038 = transcriptClaim "ABC730-2026-09-09-C038" (span "28" "30") "Australian government voice" policyPosition directTranscriptSupport "Australia has taken action that the Netanyahu government has made clear displeases it." "Attributed Australian government characterization."
c039 = transcriptClaim "ABC730-2026-09-09-C039" (span "30" "30") "ABC reporter" reporterNarration directTranscriptSupport "Israel was heading to an election in late October and tensions over settlements were expected to continue." "Election timing and prediction require external source verification."
c040 = transcriptClaim "ABC730-2026-09-09-C040" (span "30" "32") "Australian government" policyPosition directTranscriptSupport "Australia's official position was to pursue further targeted measures against illegal settlement activity and settler violence." "Government-position claim."
c041 = transcriptClaim "ABC730-2026-09-09-C041" (span "30" "32") "Australian government" causalOrPredictive directTranscriptSupport "Rapid settlement expansion, E1 and settler violence are extinguishing the possibility of a two-state solution." "Strong causal/predictive characterization; not transcript-verified causation."
c042 = transcriptClaim "ABC730-2026-09-09-C042" (span "32" "32") "Australian government" policyPosition directTranscriptSupport "A two-state solution remains Australia's stated path to enduring peace and security for Israelis and Palestinians." "Policy objective, not prediction of success."

------------------------------------------------------------------------
-- Emily Thornberry interview package: lines 34-102.

c043 = transcriptClaim "ABC730-2026-09-09-C043" (span "34" "38") "Dame Emily Thornberry" reporterNarration directTranscriptSupport "The new UK Labour government took foreign policy in a different direction but had not gone far enough on the Middle East; a change of prime minister created an opportunity to go further." "Political interpretation by interviewee."
c044 = transcriptClaim "ABC730-2026-09-09-C044" (span "38" "40") "Dame Emily Thornberry" policyPosition directTranscriptSupport "She and others had campaigned for years for stronger action and welcomed the new leadership's agreement to go further." "Self-report/political history."
c045 = transcriptClaim "ABC730-2026-09-09-C045" (span "40" "42") "Dame Emily Thornberry" policyPosition directTranscriptSupport "The UK has preferential trade arrangements with Israel proper but not the West Bank and needed to stop trade with the West Bank." "Trade-law specifics require instrument verification."
c046 = transcriptClaim "ABC730-2026-09-09-C046" (span "42" "44") "Dame Emily Thornberry" reporterNarration directTranscriptSupport "Settlement-project flats were being advertised in London." "Underlying advertisements require source artifact."
c047 = transcriptClaim "ABC730-2026-09-09-C047" (span "42" "44") "Dame Emily Thornberry" policyPosition directTranscriptSupport "The UK action should stop services and financial/professional assistance from London contributing to settlement construction." "Policy scope as described by Thornberry; exact legal scope requires instrument."
c048 = transcriptClaim "ABC730-2026-09-09-C048" (span "44" "44") "Dame Emily Thornberry" evaluativeRhetoric directTranscriptSupport "The far-right Netanyahu government is attempting to 'snuff out Palestine' and Britain should not assist it." "Evaluative/political characterization."
c049 = transcriptClaim "ABC730-2026-09-09-C049" (span "46" "50") "ABC interviewer / Thornberry" causalOrPredictive directTranscriptSupport "Some senior Israelis opposed to Netanyahu and settlements argued the UK should wait until after the election because sanctions could bolster Netanyahu." "Nested prediction attributed to unnamed senior Israelis."
c050 = transcriptClaim "ABC730-2026-09-09-C050" (span "50" "52") "Dame Emily Thornberry" evaluativeRhetoric directTranscriptSupport "The action should have happened at least two years earlier rather than being delayed." "Normative timing judgment."
c051 = transcriptClaim "ABC730-2026-09-09-C051" (span "50" "52") "Dame Emily Thornberry" reporterNarration directTranscriptSupport "The new UK government had been in office for about seven weeks." "Temporal claim in transcript."
c052 = transcriptClaim "ABC730-2026-09-09-C052" (span "54" "56") "Dame Emily Thornberry" reportedAllegation nestedAttributionOnly "New reports said Netanyahu or his government had been warned of the attack on Israeli citizens and failed to react." "Serious nested allegation; no independent verification from transcript."
c053 = transcriptClaim "ABC730-2026-09-09-C053" (span "54" "56") "Dame Emily Thornberry" causalOrPredictive directTranscriptSupport "Those reports may generate anger in Israel and affect Netanyahu's re-election prospects." "Speculative causal/predictive claim."
c054 = transcriptClaim "ABC730-2026-09-09-C054" (span "56" "56") "Dame Emily Thornberry" reporterNarration directTranscriptSupport "Israel is a democracy with substantial internal disagreement." "General political characterization."
c055 = transcriptClaim "ABC730-2026-09-09-C055" (span "56" "56") "Dame Emily Thornberry" causalOrPredictive directTranscriptSupport "Israel's international isolation is linked to the behaviour of its far-right government, and changing direction could help Israel re-enter the international fold." "Causal/predictive political claim."
c056 = transcriptClaim "ABC730-2026-09-09-C056" (span "58" "60") "ABC interviewer" interviewQuestion questionOnly "Australia works closely with the UK and others on Palestinian statehood and settlement restraint; did Thornberry expect Australia to join?" "Question embeds premises; not independently promoted as reporter-verified facts here."
c057 = transcriptClaim "ABC730-2026-09-09-C057" (span "60" "60") "Dame Emily Thornberry" policyPosition directTranscriptSupport "It was hoped Australia might join, but each country makes its own decision." "Interviewee view."
c058 = transcriptClaim "ABC730-2026-09-09-C058" (span "60" "60") "Dame Emily Thornberry" evaluativeRhetoric directTranscriptSupport "She has a lot of time for Penny Wong and assumes Wong believes her decision serves Palestinians and justice, while the UK takes a different view." "Personal/political assessment."
c059 = transcriptClaim "ABC730-2026-09-09-C059" (span "62" "66") "Dame Emily Thornberry" reporterNarration directTranscriptSupport "The Palestinian ambassador had significant influence on the UK discussion and argued the measure was in Palestinians' interests." "Nested attribution to ambassador preserved."
c060 = transcriptClaim "ABC730-2026-09-09-C060" (span "64" "68") "Dame Emily Thornberry" policyPosition directTranscriptSupport "Existing UK-Israel trade arrangements already distinguish Israel proper from Palestinian/occupied-territory goods, so the UK believes rules-of-origin problems can be handled." "Implementation claim requiring trade-law/source verification."
c061 = transcriptClaim "ABC730-2026-09-09-C061" (span "68" "68") "Dame Emily Thornberry" policyPosition directTranscriptSupport "The UK and Australia may start from different institutional positions, and she would be willing to try to persuade Australian counterparts." "Political/implementation assessment."
c062 = transcriptClaim "ABC730-2026-09-09-C062" (span "68" "70") "ABC interviewer" reporterNarration directTranscriptSupport "UK trade with the settlements was understood to be very small, though no exact number was given." "Quantitative claim explicitly uncertain."
c063 = transcriptClaim "ABC730-2026-09-09-C063" (span "70" "72") "Dame Emily Thornberry" evaluativeRhetoric directTranscriptSupport "The action is about doing the right thing in law and morality rather than merely symbolism." "Normative/legal characterization by interviewee."
c064 = transcriptClaim "ABC730-2026-09-09-C064" (span "70" "72") "Dame Emily Thornberry" policyPosition directTranscriptSupport "The UK should move beyond sanctions on particular individuals to a broader approach and take a clear stance." "Policy prescription."
c065 = transcriptClaim "ABC730-2026-09-09-C065" (span "74" "78") "Dame Emily Thornberry" reporterNarration directTranscriptSupport "Within UK Labour there had been discontent that Middle East policy was repeatedly too little and too late; she personally pressed the new prime minister and Ed Miliband to change course." "Self-reported internal political history."
c066 = transcriptClaim "ABC730-2026-09-09-C066" (span "78" "80") "Dame Emily Thornberry" reporterNarration directTranscriptSupport "She had campaigned for recognition of Palestine for about fifteen years and thought recognition should have happened earlier." "Self-report plus normative timing judgment."
c067 = transcriptClaim "ABC730-2026-09-09-C067" (span "80" "82") "Dame Emily Thornberry" policyPosition directTranscriptSupport "The new government offered an opportunity for Britain to stop trailing events and change both tone and approach." "Political interpretation/prescription."
c068 = transcriptClaim "ABC730-2026-09-09-C068" (span "82" "84") "ABC interviewer" interviewQuestion questionOnly "Miliband described deep urgency over the West Bank and settlements; Australia concurs with that urgency; what practical effect will the UK action have?" "Question embeds attributed premises."
c069 = transcriptClaim "ABC730-2026-09-09-C069" (span "84" "86") "Dame Emily Thornberry" causalOrPredictive directTranscriptSupport "E1 would cut a future Palestine in two and separate it from East Jerusalem, with a massive effect on Palestine." "Strong predictive/territorial characterization; external geographic/legal verification separate."
c070 = transcriptClaim "ABC730-2026-09-09-C070" (span "86" "88") "Dame Emily Thornberry" reporterNarration directTranscriptSupport "The United States had previously restrained Israel on E1 but appeared distracted and insufficiently attentive." "Political assessment requiring independent diplomatic source."
c071 = transcriptClaim "ABC730-2026-09-09-C071" (span "88" "90") "Dame Emily Thornberry" reporterNarration directTranscriptSupport "E1 contracts/tenders were expected to be signed shortly before Israel's general election, and she inferred the timing was deliberate." "Factual timing plus explicit inference; both require source verification."
c072 = transcriptClaim "ABC730-2026-09-09-C072" (span "90" "92") "Dame Emily Thornberry" policyPosition directTranscriptSupport "Britain does not want British architects, contractors, materials, money or assistance involved in E1 contracts." "Policy intent."
c073 = transcriptClaim "ABC730-2026-09-09-C073" (span "90" "92") "Dame Emily Thornberry" legalCharacterisation directTranscriptSupport "E1 is in breach of international law and morally wrong." "Legal and moral characterization by interviewee; independent legal admission separate."
c074 = transcriptClaim "ABC730-2026-09-09-C074" (span "92" "96") "ABC interviewer / Dame Emily Thornberry" reporterNarration directTranscriptSupport "The US response, including Marco Rubio's, was described as measured/mild despite Israel's strong reaction." "Comparative diplomatic characterization."
c075 = transcriptClaim "ABC730-2026-09-09-C075" (span "94" "94") "Dame Emily Thornberry" legalCharacterisation directTranscriptSupport "What Britain is doing is in accordance with international law." "Legal characterization by interviewee; requires independent legal source for promotion."
c076 = transcriptClaim "ABC730-2026-09-09-C076" (span "96" "98") "Dame Emily Thornberry" reportedAllegation nestedAttributionOnly "The Israeli government has explicitly said it is acting to extinguish the possibility of a Palestinian state." "Nested attribution; requires exact Israeli source."
c077 = transcriptClaim "ABC730-2026-09-09-C077" (span "96" "98") "Dame Emily Thornberry" policyPosition directTranscriptSupport "Other sovereign nations should do everything they can to try to stop that course." "Normative foreign-policy prescription."
c078 = transcriptClaim "ABC730-2026-09-09-C078" (span "98" "100") "Dame Emily Thornberry" reporterNarration directTranscriptSupport "Britain has a special historical responsibility arising from the Mandate period and its role in encouraging creation of Israel." "Historical/normative characterization; independent historical analysis separate."
c079 = transcriptClaim "ABC730-2026-09-09-C079" (span "98" "100") "Dame Emily Thornberry" evaluativeRhetoric directTranscriptSupport "Britain let Palestinians down; Palestinians deserve a state and justice; Britain should not merely stand aside." "Normative/historical judgment."

------------------------------------------------------------------------
-- Incidental recording artefacts / transition.

c080 = transcriptClaim "ABC730-2026-09-09-C080" (span "48" "48") "unidentified off-air voices" incidentalSpeech directTranscriptSupport "There is incidental conversation about recording/borrowing a device during the transcript." "Not part of the sanctions-policy claim surface."
c081 = transcriptClaim "ABC730-2026-09-09-C081" (span "104" "106") "ABC program transition" reporterNarration directTranscriptSupport "The program transitions to Australian bushfires and farm-preparation content." "Outside the West Bank sanctions matter."

allTranscriptClaims : List TranscriptClaim
allTranscriptClaims =
  c001 ∷ c002 ∷ c003 ∷ c004 ∷ c005 ∷ c006 ∷ c007 ∷ c008 ∷ c009 ∷ c010 ∷
  c011 ∷ c012 ∷ c013 ∷ c014 ∷ c015 ∷ c016 ∷ c017 ∷ c018 ∷ c019 ∷ c020 ∷
  c021 ∷ c022 ∷ c023 ∷ c024 ∷ c025 ∷ c026 ∷ c027 ∷ c028 ∷ c029 ∷ c030 ∷
  c031 ∷ c032 ∷ c033 ∷ c034 ∷ c035 ∷ c036 ∷ c037 ∷ c038 ∷ c039 ∷ c040 ∷
  c041 ∷ c042 ∷ c043 ∷ c044 ∷ c045 ∷ c046 ∷ c047 ∷ c048 ∷ c049 ∷ c050 ∷
  c051 ∷ c052 ∷ c053 ∷ c054 ∷ c055 ∷ c056 ∷ c057 ∷ c058 ∷ c059 ∷ c060 ∷
  c061 ∷ c062 ∷ c063 ∷ c064 ∷ c065 ∷ c066 ∷ c067 ∷ c068 ∷ c069 ∷ c070 ∷
  c071 ∷ c072 ∷ c073 ∷ c074 ∷ c075 ∷ c076 ∷ c077 ∷ c078 ∷ c079 ∷ c080 ∷
  c081 ∷ []

------------------------------------------------------------------------
-- Canonical high-value coordinates consumed elsewhere.

abcLaborGaslightingClaim : TranscriptClaim
abcLaborGaslightingClaim = c032

abcAustraliaNoBlanketBanClaim : TranscriptClaim
abcAustraliaNoBlanketBanClaim = c028

abcAustraliaUnintendedConsequencesRationale : TranscriptClaim
abcAustraliaUnintendedConsequencesRationale = c029

abcUKImportBanClaim : TranscriptClaim
abcUKImportBanClaim = c017

abcE1TwoStateThreatClaim : TranscriptClaim
abcE1TwoStateThreatClaim = c016

------------------------------------------------------------------------
-- Non-collapse invariants are encoded by construction:
-- * directTranscriptSupport means the proposition is present on the transcript
--   surface, not that it is independently true.
-- * nestedAttributionOnly preserves 'X said/reported Y' without promoting Y.
-- * speakerUnresolved prevents a quote from paying a named-speaker consumer.
-- * questionOnly prevents interviewer premises from silently becoming findings.
