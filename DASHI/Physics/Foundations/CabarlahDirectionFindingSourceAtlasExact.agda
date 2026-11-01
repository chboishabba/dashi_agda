module DASHI.Physics.Foundations.CabarlahDirectionFindingSourceAtlasExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- CABARLAH DIRECTION-FINDING SOURCE ATLAS
--
-- These sources pay only bounded historical claims about Cabarlah, Army
-- signals intelligence, direction-finding capability, and later HF-DF arrays.
-- None of them, by themselves, identify a particular observed goniometer as a
-- Cabarlah object or prove a Bellini-Tosi installation at Cabarlah.
------------------------------------------------------------------------

armyResearchCabarlahSIGINT : Source.AttributedSource
armyResearchCabarlahSIGINT = Source.mkNoDOISource
  "John Blaxland"
  "The Role of Signals Intelligence in Australian Military Operations, 1939-72"
  "Australian Army Journal / Australian Army Research Centre"
  "2005"
  "https://researchcentre.army.gov.au/library/australian-army-journal-aaj/volume-2-number-2/role-signals-intelligence-australian-military-operations-1939-72"
  Source.governmentSource
  "government military-history source paying the bounded claims that No. 101 Wireless Regiment was based at Cabarlah, that Cabarlah became the permanent home of Army signals intelligence, and that its deployable 547 Signal Troop included airborne and experimental high-frequency direction-finding sections"
  Source.publicAttribution

cabarlahMediumRangeDFOralHistory : Source.AttributedSource
cabarlahMediumRangeDFOralHistory = Source.mkNoDOISource
  "Australians at War Film Archive interview participant"
  "Australians at War Film Archive transcript 1527"
  "Australians at War Film Archive / UNSW"
  "archival interview"
  "https://australiansatwarfilmarchive.unsw.edu.au/archive/htmlTranscript/1527?asPdf=y"
  Source.archivalSource
  "first-person archival testimony describing a medium-range direction-finding shed and aerials at Cabarlah; testimony is retained as source-bounded evidence and does not establish equipment model or goniometer identity"
  Source.publicAttribution

anuCabarlahCDAAHistory : Source.AttributedSource
anuCabarlahCDAAHistory = Source.mkNoDOISource
  "Desmond Ball and contributors"
  "Geography, Power, Strategy and Defence Policy"
  "ANU Press"
  "2016 edition / historical account"
  "https://press-files.anu.edu.au/downloads/press/p346293/html/ch03.xhtml?page=10&referer="
  Source.academicBookSource
  "historical source paying the bounded claim that circularly disposed antenna arrays for HF interception and direction-finding were installed at Cabarlah, alongside Pearce and Shoal Bay, in the mid-1970s"
  Source.publicAttribution

raafCabarlahHFDFConference : Source.AttributedSource
raafCabarlahHFDFConference = Source.mkNoDOISource
  "RAAF Air Power Conference contributors"
  "Smaller but Larger: Conventional Air Power into the 21st Century"
  "Royal Australian Air Force Air Power Conference proceedings"
  "1991"
  "https://airpower.airforce.gov.au/sites/default/files/2021-03/CONF01-RAAF-Air-Power-Conference-1991-Smaller-but-Larger-Conventional-Air-Power-into-the-21st-Century.pdf"
  Source.governmentSource
  "government conference source paying the bounded claim that Plessey circularly disposed antenna array high-frequency direction-finding systems were installed at Cabarlah, Pearce and Shoal Bay; not a Bellini-Tosi or goniometer identity source"
  Source.publicAttribution

aniCabarlahStrategicDFUpgrade : Source.AttributedSource
aniCabarlahStrategicDFUpgrade = Source.mkNoDOISource
  "Australian Naval Institute"
  "2019 McNeil Prize nomination for Peter Jenkins / JEDS"
  "Australian Naval Institute"
  "2019"
  "https://navalinstitute.com.au/wp-content/uploads/2019-ANI-McNeil-Prize-Nomination-for-Peter-Jenkins-JEDS-23Apr2019.pdf"
  Source.practitionerSource
  "practitioner/institutional lead stating that an Australian Army strategic RF direction-finding system at Cabarlah was upgraded in 1996; retained as a bounded historical lead, not proof of a specific hardware family"
  Source.publicAttribution

cabarlahDirectionFindingAtlas : Source.AttributedSourceAtlas
cabarlahDirectionFindingAtlas = Source.mkSourceAtlas
  "Cabarlah direction-finding acquisition atlas"
  "DASHI.Physics.Foundations.CabarlahDirectionFindingSourceAtlasExact"
  (armyResearchCabarlahSIGINT ∷ cabarlahMediumRangeDFOralHistory ∷ anuCabarlahCDAAHistory ∷ raafCabarlahHFDFConference ∷ aniCabarlahStrategicDFUpgrade ∷ [])
  "sources pay Cabarlah SIGINT and direction-finding lineage only; exact goniometer model, Bellini-Tosi installation, observed-object same identity, exact operational tasking, and authority remain separate"
