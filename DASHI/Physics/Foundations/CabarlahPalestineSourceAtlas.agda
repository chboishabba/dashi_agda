module DASHI.Physics.Foundations.CabarlahPalestineSourceAtlas where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.Round5SourceAtlas as Sources

------------------------------------------------------------------------
-- Sources are attached to bounded roles.  Government and journalism records
-- use explicit no-DOI markers rather than invented scholarly identifiers.

wolfeSettlerColonialismSource : Sources.SourceRecord
wolfeSettlerColonialismSource =
  Sources.sourceRecord
    "Patrick Wolfe"
    "Settler Colonialism and the Elimination of the Native"
    "Journal of Genocide Research 8(4), 387-409"
    2006
    "10.1080/14623520601056240"
    "Supports the structural logic-of-elimination analysis of settler colonialism and the distinction between eliminatory structure and genocide as identical categories."
    "The article does not prove that Australian settlers at Cabarlah literally used the word Amalek or that Australian and Palestinian histories are identical."

azzamAmalekSource : Sources.SourceRecord
azzamAmalekSource =
  Sources.sourceRecord
    "Abed Azzam"
    "Blot Out the Memory of Amalek from Under Heaven: The Gaza Genocide and the Political Theological Legacy of the Biblical Amalek"
    "Analyse & Kritik 47(2), 407-425"
    2025
    "10.1515/auk-2025-2018"
    "Supports analysis of modern Amalek rhetoric as a political-theological enemy construction directed at Palestinians."
    "The rhetorical genealogy is not promoted to the claim that every Israeli, every Jewish tradition, or every use of the term has one uniform meaning."

kiteWurmDuungidjawuSource : Sources.SourceRecord
kiteWurmDuungidjawuSource =
  Sources.sourceRecord
    "Suzanne Kite; S. A. Wurm"
    "The Duungidjawu Language of Southeast Queensland: Grammar, Texts and Vocabulary"
    "Pacific Linguistics 553, Australian National University"
    2004
    "10.15144/PL-553"
    "Supports bounded comparison with a documented southeast Queensland language system, including phonological contrasts and the need for language-specific analysis."
    "Duungidjawu evidence is not promoted to a unique reconstruction of the poorly recorded Jarowair or Wakka source of Cabarlah."

jarowairStateLibrarySource : Sources.SourceRecord
jarowairStateLibrarySource =
  Sources.sourceRecord
    "Desmond Crump; State Library of Queensland"
    "Language of the Week: Week Six - Jarowair"
    "State Library of Queensland"
    2020
    "No DOI assigned; State Library of Queensland web resource"
    "Supports locating Jarowair in the Toowoomba-to-Crows-Nest region, its relation to the Wakka Wakka language chain, variant spellings, and the limited surviving data."
    "The resource does not certify one exact historical pronunciation or lexical derivation of Cabarlah."

aiatsisAustLangSource : Sources.SourceRecord
aiatsisAustLangSource =
  Sources.sourceRecord
    "Australian Institute of Aboriginal and Torres Strait Islander Studies"
    "AustLang"
    "AIATSIS"
    2026
    "No DOI assigned; living language database"
    "Supports treating multiple names and spellings as normal in Australian Indigenous language documentation and using stable language identifiers where available."
    "Variant spelling evidence does not make every invented respelling equally historically supported."

brisbaneLineAWMSource : Sources.SourceRecord
brisbaneLineAWMSource =
  Sources.sourceRecord
    "Australian War Memorial"
    "Brisbane Line"
    "Australian War Memorial Encyclopedia"
    2020
    "No DOI assigned; Australian War Memorial web resource"
    "Supports describing the Brisbane Line as an alleged and politically consequential plan associated with Japanese invasion, while recording that the Royal Commission did not find it to have been official policy."
    "The alleged line is not promoted to a verified fixed boundary through Cabarlah or to a Cold War communist concession line."

blaxlandSignalsHistorySource : Sources.SourceRecord
blaxlandSignalsHistorySource =
  Sources.sourceRecord
    "John Blaxland"
    "The Role of Signals Intelligence in Australian Military Operations, 1939-72"
    "Australian Army Journal 2(2)"
    2005
    "No DOI assigned; Australian Army Research Centre journal article"
    "Supports the institutional lineage from wartime special wireless units through the permanent Cabarlah base and later operational experience in Malaya, Borneo and Vietnam."
    "Institutional continuity is not promoted to identity of the Japanese, Indonesian, communist, Viet Cong, or North Vietnamese adversaries."

malayanSIGINTSource : Sources.SourceRecord
malayanSIGINTSource =
  Sources.sourceRecord
    "Australian Signals Directorate"
    "Australia's Signals Intelligence Contribution to the Malayan Emergency, 1952-1962"
    "Australian Signals Directorate historical release"
    2022
    "No DOI assigned; Australian Government historical web resource"
    "Supports the documented deployment of 101 Wireless Regiment personnel to search for Malayan Communist transmissions."
    "The postwar signals role does not imply that Cabarlah itself was territory designated for concession to communism."

pineGapPalestine2025Source : Sources.SourceRecord
pineGapPalestine2025Source =
  Sources.sourceRecord
    "Alex Barwick; Matthew Qvortrup"
    "Pine Gap Protesters Reject Prime Minister's Recognition of Palestine"
    "ABC News"
    2025
    "No DOI assigned; ABC News report dated 11 August 2025"
    "Supports the documented conjunction of demands for Palestinian justice, closure of Pine Gap, and return of land to traditional owners, together with protesters' concern about possible intelligence use."
    "The report does not publicly verify a Pine Gap intelligence chain to any named strike."

pineGapMarch2026Source : Sources.SourceRecord
pineGapMarch2026Source =
  Sources.sourceRecord
    "Emma Masters"
    "Hundreds March on Secretive Military Base Pine Gap in Alice Springs, in Biggest Protest at Site in Decades"
    "ABC News"
    2026
    "No DOI assigned; ABC News report dated 20 July 2026"
    "Supports the scale of the July 2026 protest, Arrernte participation, the closure demand, and the land-return demand."
    "A protest report is not promoted to an official operational disclosure about Pine Gap targeting."

canonicalCabarlahPalestineSources : List Sources.SourceRecord
canonicalCabarlahPalestineSources =
  wolfeSettlerColonialismSource
  ∷ azzamAmalekSource
  ∷ kiteWurmDuungidjawuSource
  ∷ jarowairStateLibrarySource
  ∷ aiatsisAustLangSource
  ∷ brisbaneLineAWMSource
  ∷ blaxlandSignalsHistorySource
  ∷ malayanSIGINTSource
  ∷ pineGapPalestine2025Source
  ∷ pineGapMarch2026Source
  ∷ []

sourceCount : List Sources.SourceRecord → Nat
sourceCount [] = 0
sourceCount (_ ∷ sources) = suc (sourceCount sources)

canonicalCabarlahPalestineSourceCount : Nat
canonicalCabarlahPalestineSourceCount =
  sourceCount canonicalCabarlahPalestineSources

canonicalCabarlahPalestineSourceCountIsTen :
  canonicalCabarlahPalestineSourceCount ≡ 10
canonicalCabarlahPalestineSourceCountIsTen = refl
