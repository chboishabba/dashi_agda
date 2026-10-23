module DASHI.Cognition.PsychotronicsSuccorSourceAtlasExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.EmpiricalSourceDiligenceAdmissionExact as Diligence
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- SUCCOR PUNCH / ORGONITE / ELECTRICAL-DISCHARGE SOURCE ATLAS
--
-- Attribution owner: each historical proposition remains its author's
-- assertion. DASHI owns only the source classification, cross-source
-- comparison, negative promotion boundary, and acquisition frontier.
--
-- Explicit limits:
--   * a patent documents a design, not treatment effectiveness;
--   * a contemporary report of psychic effects does not verify them;
--   * an Army-authored report is not an Army validation of its theory;
--   * Croft reprints / mirrors share one authorial root;
--   * visual resemblance cannot establish apparatus identity or lineage.
--
-- This module does NOT implement an orgone/scalar-wave physics theory.
------------------------------------------------------------------------

croftMay2002 : Source.AttributedSource
croftMay2002 = Source.mkNoDOISource
  "Don Croft"
  "What's A Succor Punch?"
  "18 May 2002 article; Croft Zappers preserves attributed reprint with original educate-yourself.org locator"
  "2002"
  "https://www.croftzappers.com/succor-punch"
  Source.practitionerSource
  "self-report of Mobius-wrapped crystal, 15 Hz zapper, psychic attacks and claimed protection; NOT validation of the reported entities or effects"
  Source.publicAttribution

croftJuly2002 : Source.AttributedSource
croftJuly2002 = Source.mkNoDOISource
  "Don Croft"
  "Succor Punch Explained"
  "22 July 2002 article; reprinted by Croft Zappers with original educate-yourself.org locator"
  "2002"
  "https://www.croftzappers.com/succor-punch"
  Source.practitionerSource
  "author's description of coil terminals, nine-volt frequency box and 15 cycles per second; claims of scalar protection remain attributed"
  Source.publicAttribution

croftAdventures : Source.AttributedSource
croftAdventures = Source.mkNoDOISource
  "Don Croft"
  "The Adventures of Don and Carol Croft: The Succor Punch is Born"
  "undated retrospective compilation; Internet Archive transcription preserves passage"
  "undated compilation; describes 2002-era activities"
  "https://archive.org/stream/DonCroftTheAdventuresOfDonAndCarolCroft/Don%20Croft%20-%20The%20Adventures%20of%20Don%20and%20Carol%20Croft_djvu.txt"
  Source.archivalSource
  "author explicitly narrates a Mobius coil on quartz, 15 Hz circuit, and placement between cloudbuster pipes; retrospective same-author source, not independent replication"
  Source.publicAttribution

reichMuseum : Source.AttributedSource
reichMuseum = Source.mkNoDOISource
  "Wilhelm Reich Museum"
  "Mythconceptions about Wilhelm Reich and his work"
  "institutional interpretive article, sections 14 and 15"
  "undated online edition; inspected 2026-10-24"
  "https://wilhelmreichmuseum.org/mythconceptions/"
  Source.institutionalSource
  "distinguishes Reich's hollow-tube water-connected cloudbuster from Welz/Croft quartz-metal-resin orgonite; museum account does not validate orgone physics"
  Source.publicAttribution

lakhovskyPatent : Source.AttributedSource
lakhovskyPatent = Source.mkNoDOISource
  "Georges Lakhovsky"
  "Apparatus with circuits oscillating under multiple wave lengths"
  "United States patent US1962565A; filed 13 November 1931; granted 12 June 1934"
  "1934"
  "https://patents.google.com/patent/US1962565A/en"
  Source.namedSourceKind "patent specification"
  "describes concentric insulated split rings excited by high-frequency impulses; not a clinical-efficacy or Succor-Punch pedigree receipt"
  Source.publicAttribution

channonManual : Source.AttributedSource
channonManual = Source.mkNoDOISource
  "James B. Channon"
  "The First Earth Battalion: Dare to Think the Unthinkable"
  "1979 concept paper reproduced by permission with editorial annotation in Journal of Non-lethal Combatives, February 2000"
  "1979; reproduction 2000"
  "https://ejmas.com/jnc/jncart_channon_0200.htm"
  Source.archivalSource
  "documents New Age-inspired military concept-paper proposals and an explicit non-official-policy disclaimer; not proof of psychic capacities"
  Source.publicAttribution

gateway1983 : Source.AttributedSource
gateway1983 = Source.mkNoDOISource
  "Wayne M. McDonnell"
  "Analysis and Assessment of Gateway Process"
  "US Army intelligence assessment, 9 June 1983; GovInfo GOVPUB-D101-PURL-gpo152943; CIA-RDP96-00788R001700210016-5"
  "1983"
  "https://www.govinfo.gov/app/details/GOVPUB-D101-PURL-gpo152943"
  Source.governmentSource
  "historical author-proposed holographic consciousness, frequency and matrix interpretation; government archival custody is not scientific endorsement"
  Source.publicAttribution

air1995 : Source.AttributedSource
air1995 = Source.mkNoDOISource
  "Michael D. Mumford; Andrew M. Rose; David S. Goslin"
  "An Evaluation of Remote Viewing: Research and Applications"
  "American Institutes for Research, 29 September 1995 final; CIA-RDP96-00791R000200180006-4 archival locator (CIA landing URL now 404); final-report PDF title and E-3 visually inspected 2026-10-24"
  "1995"
  "https://www.alice.id.tue.nl/references/mumford-rose-goslin-1995.pdf"
  Source.institutionalSource
  "independent programme evaluation; distinguishes contested statistical findings from insufficient operational intelligence utility; final version not 22 September draft"
  Source.publicAttribution

electricWhirl : Source.AttributedSource
electricWhirl = Source.mkNoDOISource
  "University of Colorado Boulder, Physics Undergraduate Labs"
  "Electric Whirl"
  "physics demonstration, updated 27 March 2026"
  "2026"
  "https://physicslabs.colorado.edu/demos/electricity-and-magnetism/electric-fields-and-potential/electrostatic-potential/electric-whirl/"
  Source.institutionalSource
  "ordinary high-voltage corona / ionic-wind rotor mechanism; separately demonstrable but not an identification of Instagram hardware"
  Source.publicAttribution

irvaTimeline : Source.AttributedSource
irvaTimeline = Source.mkNoDOISource
  "International Remote Viewing Association"
  "A Brief Timeline of Remote Viewing and IRVA"
  "professional association's retrospective chronology; 1986 and 1988 SUN STREAK / Ed Dames entries"
  "undated online chronology; inspected 2026-10-24"
  "https://www.irva.org/time-line"
  Source.communitySource
  "association timeline says Ed Dames joined the Fort Meade operational remote-viewing unit in 1986 and later left; contextual attribution, not independent success evidence"
  Source.publicAttribution

kingEarthEnergies : Source.AttributedSource
kingEarthEnergies = Source.mkNoDOISource
  "Serge Kahili King"
  "Earth Energies: A Quest for the Hidden Power of the Planet"
  "Quest Books / Theosophical Publishing House, ISBN 9780835606820; first edition"
  "1992"
  "https://books.google.com/books/about/Earth_Energies.html?id=qqnEtTMSaxwC"
  (Source.namedSourceKind "esoteric popular-press book")
  "named by Don Croft as his introduction to Reich/orgone in his autobiographical narrative; this documents Croft's attributed reading, NOT proof of the book's psychoenergetic claims"
  Source.publicAttribution

ipyramidsI9 : Source.AttributedSource
ipyramidsI9 = Source.mkNoDOISource
  "iPyramids"
  "iTorus i9, 9.5-inch Tachyon Vortex PEMF 4.0 product documentation"
  "commercial product specifications; supplier website inspected 2026-10-24"
  "undated product page"
  "https://ipyramids.com/products/full-spectrum-ipyramids-i9-nubian-quantum-vortex-shield"
  Source.practitionerSource
  "manufacturer describes audio/app-driven toroidal coil; 7-ohm-per-channel, 9.5-inch diameter and claimed field dimensions remain manufacturer attestations, not independent B-field mapping or healthcare outcomes"
  Source.publicAttribution

aurumayaQubit : Source.AttributedSource
aurumayaQubit = Source.mkNoDOISource
  "Aurumaya"
  "QUBIT CRYSTAL: Large Pulsed Quartz Succor Punch, 15 Hz Crystal Tech"
  "maker's commercial product listing; inspected 2026-10-24"
  "undated product page"
  "https://www.aurumaya.com.au/crystaltech"
  Source.practitionerSource
  "explicitly markets quartz/copper/15-Hz/9-V modern Succor Punch; maker reply in separate screenshot names Don Croft; this establishes *claimed design tradition*, not scalar-energy performance"
  Source.publicAttribution

oudinHistoricalDiagram : Source.AttributedSource
oudinHistoricalDiagram = Source.mkNoDOISource
  "Mihran Krikor Kassabian"
  "Roentgen Rays and Electro-Therapeutics: Oudin coil and circuit diagram"
  "1907 J.B. Lippincott published illustration, p.142 figs.61-62; Wikimedia Commons archivally describes image"
  "1907"
  "https://commons.wikimedia.org/wiki/File:Oudin_coil_and_circuit_diagram.png"
  Source.archivalSource
  "historical Oudin resonant high-voltage apparatus with handheld electrode and corona discharge; not same-object identification of @berndnindl footage or proof of medical efficacy"
  Source.publicAttribution

mayuVortex : Source.AttributedSource
mayuVortex = Source.mkNoDOISource
  "Cameron-Leigh Henning (edited by Joel Taylor), for MAYU Water"
  "What Is Vortexing Water?"
  "MAYU's commercial structured-water explainer; revised 3 February 2025"
  "2025"
  "https://mayuwater.com/a/resources/structured-water/what-is-vortexing-water"
  Source.practitionerSource
  "source explicitly advertises H3O2 and superior hydration; these remain unsupported commercial claims. Ordinary rotational aeration is a separate testable mechanism; screenshot carries an on-screen MAYU label"
  Source.publicAttribution

aapStructuredWater : Source.AttributedSource
aapStructuredWater = Source.mkNoDOISource
  "Soofia Tariq / Australian Associated Press FactCheck"
  "Claims of 'structured' water health benefits are mere fiction"
  "AAP FactCheck, 6 August 2024; quotes chemistry experts"
  "2024"
  "https://www.aap.com.au/factcheck/claims-of-structured-water-health-benefits-are-mere-fiction/"
  Source.newsSource
  "evidence-based challenge to purported distinct H3O2/hexagonal hydration fluid; not a claim that mechanical swirling cannot alter gas dissolution"
  Source.publicAttribution

atmosphericFieldMill : Source.AttributedSource
atmosphericFieldMill = Source.mkNoDOISource
  "PITHIA-NRF Research Infrastructure"
  "Field mill for the measurement of atmospheric electricity"
  "research infrastructure explainer, technical discussion of fair-weather atmospheric E fields"
  "undated web page; inspected 2026-10-24"
  "https://www.pithia-nrf.eu/activities-results/outreach/space-weather-research-instruments/electric-field-mills"
  Source.institutionalSource
  "atmospheric electric potential/field is measurable by a field mill; this does not authenticate a Pignatelli inventor, charged aerostat driver, usable motor power or continuous generation"
  Source.publicAttribution

oudinBeharyRestoration : Source.AttributedSource
oudinBeharyRestoration = Source.mkNoDOISource
  "Jeff Behary"
  "Oudin Coil 2010: Revisiting a Turn Of The Century Invention"
  "The Turn Of The Century Electrotherapy Museum; illustrated 2010 reconstruction and historical interpretation"
  "2010"
  "https://electrotherapymuseum.org/2010/Oudin2010/index.htm"
  Source.practitionerSource
  "describes heavy-gauge spaced windings and historically varying Oudin resonator geometry, with a demonstrated externally driven corona apparatus; NOT independent identification of berndnindl reel, output measurements, or therapy evidence"
  Source.publicAttribution

oudinBeharySphere : Source.AttributedSource
oudinBeharySphere = Source.mkNoDOISource
  "Jeff Behary"
  "Tesla / Oudin Coil with 6-inch Copper Sphere Topload"
  "The Turn Of The Century Electrotherapy Museum; illustrated maker's 2008 reconstruction and self-reported electrical measurements"
  "2008"
  "https://www.electrotherapymuseum.org/2008/CopperOudin/index.htm"
  Source.practitionerSource
  "maker documents round topload and air streamers on an Oudin/Tesla family resonator. Same authorial museum lineage as 2010 reconstruction, NOT independent replication or modern clip identity"
  Source.publicAttribution

guilleminotOudinDiagram : Source.AttributedSource
guilleminotOudinDiagram = Source.mkNoDOISource
  "W. Hyacinthe Guilleminot; Wellcome Collection (archival custodian)"
  "Oudin unipolar resonator circuit diagram, reproduced from Handbook of Electricity in Medicine"
  "original diagram in 1906 manual; Wellcome catalogue M0015155 / WT/D/1/20/1/135/34 records a September 1956 photographic negative"
  "1906 original; 1956 archive negative"
  "https://wellcomecollection.org/works/kgngz6kz"
  Source.archivalSource
  "source-distinct historical circuit diagram of a unipolar Oudin resonator; the modern photograph has no disclosed primary/secondary continuity, so this is a class comparator, not exact circuit identity or proof of clinical utility"
  Source.publicAttribution

jefimenkoElectrostaticMotors : Source.AttributedSource
jefimenkoElectrostaticMotors = Source.mkNoDOISource
  "Oleg D. Jefimenko; David K. Walker (credited with many illustrations)"
  "Electrostatic Motors: Their History, Types, and Principles of Operation"
  "Electret Scientific Company, Star City, 1973; publicly mirrored scan inspected: PDF pages 69-70, printed pages 114-117"
  "1973"
  "https://rexresearch1.com/Electrostatics/Electrostatic%20MotorsJefimenko.pdf"
  Source.academicBookSource
  "primary-author account of small electrostatic motors operated from earth-field antennas with explicitly unresolved larger-motor power; does not identify the viral 'Pignatelli motor' or yield a power measurement for that post"
  Source.publicAttribution

itorusAppPublisher : Source.AttributedSource
itorusAppPublisher = Source.mkNoDOISource
  "Itorus, LLC (Google Play developer); iPyramids named as hardware maker"
  "iTorus: official PEMF Therapy application listing"
  "Google Play app identifier com.goodbarber.itorus, public listing updated 13 July 2026; inspected 24 October 2026"
  "2026"
  "https://play.google.com/store/apps/details?id=com.goodbarber.itorus"
  Source.practitionerSource
  "direct app-publisher copy invokes Premium RIFE frequencies, Zero Point, 5D, biofield protection, EMF/5G shielding, chakra repair and pineal activation. This pays explicit modern thematic vocabulary, not effectiveness or the exact app session pictured"
  Source.publicAttribution

itorusHeartStoneReseller : Source.AttributedSource
itorusHeartStoneReseller = Source.mkNoDOISource
  "Revive Pro Tech (reseller)"
  "iTorus i9 Heart Stone: portable PEMF device listing"
  "commercial third-party product page inspected 24 October 2026; multiple stated coverage diameters on same named product page"
  "undated product listing"
  "https://reviveprotech.com/products/itorus-i9-heart-stone-portable-pemf-device"
  Source.practitionerSource
  "same page markets 55-ft, 30-ft and 24-ft diameters in distinct sections, plus nominal 8.5 ohm/channel rating; no common field threshold or model revision specified, and not the exact pictured SKU"
  Source.publicAttribution

aurumayaHomeCatalogue : Source.AttributedSource
aurumayaHomeCatalogue = Source.mkNoDOISource
  "Aurumaya"
  "AURUMAYA: Ancient Frequency Tools of the Future"
  "maker's home/catalogue landing page inspected 24 October 2026"
  "undated catalogue"
  "https://www.aurumaya.com.au/"
  Source.practitionerSource
  "maker home page co-lists Tesla multi-wave-oscillator discs, 369 ritual elixir, 432-MHz-labelled tensor jewellery and Croft-named QUBIT; it does NOT itself display 333-MHz pendant text, which appears on the distinct shop page; same-vendor vocabulary only"
  Source.publicAttribution

jefimenko1971 : Source.AttributedSource
jefimenko1971 = Source.mkDOISource
  "Oleg D. Jefimenko"
  "Operation of electric motors from atmospheric electric field"
  "American Journal of Physics 39, 776-779 (1971); publication identity verified against West Virginia University author bibliography"
  "1971"
  "10.1119/1.1986281"
  "https://doi.org/10.1119/1.1986281"
  Source.academicArticleSource
  "original same-author peer-reviewed publication of reported atmospheric-field motor operation; primary article full text not independently page-inspected in this cut; neither an independent experiment relative to 1973 monograph nor confirmation of Pignatelli identity"
  Source.publicAttribution

aurumayaShopCatalogue : Source.AttributedSource
aurumayaShopCatalogue = Source.mkNoDOISource
  "Aurumaya"
  "AURUMAYA: Shop Products"
  "same maker's separate shop catalogue, inspected 24 October 2026"
  "undated catalogue"
  "https://www.aurumaya.com.au/shop"
  Source.practitionerSource
  "directly indexes 15Hz QUBIT crystal kits, ACU-VAC 333Mhz labelled pendants, geometric Tesla multi-wave oscillator disks, orgonite; distinct URL same maker root as home page and QUBIT product"
  Source.publicAttribution

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas = Source.mkSourceAtlas
  "Psychotronics Succor Punch historical and physical source atlas"
  "DASHI.Cognition.PsychotronicsSuccorSourceAtlasExact"
  (croftMay2002 ∷ croftJuly2002 ∷ croftAdventures ∷ reichMuseum ∷
   lakhovskyPatent ∷ channonManual ∷ gateway1983 ∷ air1995 ∷
   electricWhirl ∷ irvaTimeline ∷ kingEarthEnergies ∷
   ipyramidsI9 ∷ aurumayaQubit ∷ oudinHistoricalDiagram ∷
   mayuVortex ∷ aapStructuredWater ∷ atmosphericFieldMill ∷
   oudinBeharyRestoration ∷ oudinBeharySphere ∷
   guilleminotOudinDiagram ∷ jefimenkoElectrostaticMotors ∷
   itorusAppPublisher ∷ itorusHeartStoneReseller ∷
   aurumayaHomeCatalogue ∷ aurumayaShopCatalogue ∷ jefimenko1971 ∷ [])
  "claim-relative historical sources and technical analogues only; no causal transmission, psychic effect, clinical efficacy, video identification or source-independence promotion"

-- The Croft 2002 pair, retrospective anthology, and reprints are distinct
-- document instances but cannot be counted as independent witnesses.
data LineageRoot : Set where
  croftAuthorRoot reichMuseumRoot lakhovskyPatentRoot : LineageRoot
  channonConceptRoot gatewayReportRoot airEvaluationRoot kingPublicationRoot : LineageRoot
  boulderDemonstrationRoot remoteViewingAssociationRoot : LineageRoot
  iPyramidsManufacturerRoot aurumayaMakerRoot oudinHistoricalRoot : LineageRoot
  mayuManufacturerRoot aapFactCheckRoot atmosphericResearchRoot : LineageRoot
  beharyRestorationRoot : LineageRoot
  guilleminotHistoricalManualRoot jefimenkoAuthorRoot : LineageRoot
  itorusAppPublisherRoot itorusRetailCopyRoot : LineageRoot

data EvidenceCeiling : Set where
  attributedAuthorReport : EvidenceCeiling
  externallyDescribedApparatus : EvidenceCeiling
  institutionalHistoricalInterpretation : EvidenceCeiling
  experimentalMechanismElsewhere : EvidenceCeiling
  modernVisualIdentificationUnpaid : EvidenceCeiling

record ClaimBound : Set where
  constructor claim-bound
  field
    proposition : String
    carrier : Source.AttributedSource
    exactLocator : String
    root : LineageRoot
    role : Diligence.SourceRole
    ceiling : EvidenceCeiling
    firstUnpaidResidual : String
    citationCreatesTruth : Bool
    citationCreatesTruthIsFalse : citationCreatesTruth ≡ false
    citationCreatesAuthority : Bool
    citationCreatesAuthorityIsFalse : citationCreatesAuthority ≡ false
open ClaimBound public

mkBound :
  String → Source.AttributedSource → String → LineageRoot →
  Diligence.SourceRole → EvidenceCeiling → String → ClaimBound
mkBound proposition carrier locator root role ceiling residual =
  claim-bound proposition carrier locator root role ceiling residual
    false refl false refl

croftCoLocatedDevice : ClaimBound
croftCoLocatedDevice = mkBound
  "Croft says he placed a quartz crystal/Mobius coil driven at 15 Hz between pipes of his cloudbuster"
  croftAdventures
  "The Succor Punch is Born (archive.org transcription, paragraph beginning 'I was inspired to make a mobius coil')"
  croftAuthorRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "independent contemporaneous build record and measured response; author's account cannot verify orgone"

croftCircuitDescription : ClaimBound
croftCircuitDescription = mkBound
  "Croft describes small alligator clips, nine-volt battery generator and approximately 15-Hz square-wave drive"
  croftJuly2002
  "Succor Punch Explained, 22 July 2002, paragraph beginning 'The terminals of the coil'"
  croftAuthorRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "schematic/bench measurement for a specific exemplar; claims of scalar fields remain unpaid"

croftReportedEntities : ClaimBound
croftReportedEntities = mkBound
  "Croft's May text alleges extraterrestrial psychic attacks, telepathic dialogue and protection"
  croftMay2002
  "What's A Succor Punch?, 18 May 2002, opening paragraphs"
  croftAuthorRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "independent verification of alleged entities, telepathy, or device effect absent"

croftNominalElectricalDrive : ClaimBound
croftNominalElectricalDrive = mkBound
  "Croft's July 2002 explanation claims about five milliamps through a nine-volt powered coil pulsed at 15 cycles per second"
  croftJuly2002
  "Succor Punch Explained, 22 July 2002, paragraph beginning 'I glue the coil to the crystal'"
  croftAuthorRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "reported nominal numbers only; no waveform/current instrumentation or exact model identity; cannot explain the separate visible Tesla-style arcs without new hardware evidence"

croftMentionsEdDames : ClaimBound
croftMentionsEdDames = mkBound
  "Croft's May 2002 text explicitly names Maj. Ed Dames when describing purported government psychics"
  croftMay2002
  "What's A Succor Punch?, 18 May 2002, paragraph beginning 'Some other folks'"
  croftAuthorRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "named mention documents awareness of a public figure; no correspondence, affiliation, technological dependence or effectiveness follows"

irvaDamesContext : ClaimBound
irvaDamesContext = mkBound
  "IRVA retrospectively lists Ed Dames joining the remote-viewing unit in 1986"
  irvaTimeline
  "A Brief Timeline of Remote Viewing and IRVA, 1986 SUN STREAK entry"
  remoteViewingAssociationRoot
  Diligence.contextualEvidence
  institutionalHistoricalInterpretation
  "association chronology is contextual, not an independent proof of remote-viewing ability"

croftNamesKing : ClaimBound
croftNamesKing = mkBound
  "Croft explicitly says he discovered Reich through Serge Kahili King's 1992 Earth Energies"
  croftAdventures
  "Episode 1 Moonbusting Part 1, archive transcription lines near 'just discovered the work of Wilhelm Reich through Serge Kahili King's excellent book'"
  croftAuthorRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "direct first-person reading claim, not independent proof of internal bibliographic or physics statements"

croftNamesStarTetrahedron : ClaimBound
croftNamesStarTetrahedron = mkBound
  "Croft describes a star tetrahedron superimposed on Earth's landmarks in the same autobiographical chapter"
  croftAdventures
  "Episode 1 Moonbusting Part 1, paragraph beginning 'Someone had marked some lines on the globe'"
  croftAuthorRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "cultural symbol in Croft narrative only; no creator/engineering link to Instagram copper cage"

croftNamesTeslaRife : ClaimBound
croftNamesTeslaRife = mkBound
  "Croft groups Tesla, Rife, Schauberger, Mesmer and others in his stated historical exemplars"
  croftAdventures
  "retrospective compilation, paragraph beginning 'The same is true of Tesla, Rife, Schauberger'"
  croftAuthorRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "documented name cluster, not proof of reading their originals, shared apparatus design, or experimental efficacy"

itorusSpecBound : ClaimBound
itorusSpecBound = mkBound
  "iPyramids advertises its iTorus i9 as a 9.5-inch amplifier-driven toroidal PEMF device rated 7 ohms per channel"
  ipyramidsI9
  "Manufacturer specification table and product description"
  iPyramidsManufacturerRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "unknown actual flux-density map, drive spectrum, safe exposure envelope and clinical effects; field radius is unverified advertising"

aurumayaCroftClaim : ClaimBound
aurumayaCroftClaim = mkBound
  "Aurumaya calls its low-voltage quartz/copper/15-Hz product a Succor Punch and names Croft in author screenshot"
  aurumayaQubit
  "Product page QUBIT CRYSTAL; screenshot 1000018577.png author reply"
  aurumayaMakerRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "marketed lineage supports maker's attribution only; does not establish original engineer-to-builder technical custody"

oudinHighVoltagePrecedent : ClaimBound
oudinHighVoltagePrecedent = mkBound
  "1907 electrotherapy text describes Oudin resonator, a high-voltage resonant apparatus giving brush discharges"
  oudinHistoricalDiagram
  "Kassabian 1907 p.142 figs.61-62 as described by Wikimedia reproduction"
  oudinHistoricalRoot
  Diligence.contextualEvidence
  externallyDescribedApparatus
  "historical class precedent, not identity/circuit/radiation measurement of berndnindl reels"

mayuMechanics : ClaimBound
mayuMechanics = mkBound
  "MAYU markets a mechanically rotating/vortexing water carafe with claimed aeration"
  mayuVortex
  "What is Vortexing Water? company page"
  mayuManufacturerRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "direct measurements of oxygen/pH/taste on the pictured example unresolved; special water phases not established"

structuredWaterChallenge : ClaimBound
structuredWaterChallenge = mkBound
  "AAP reports expert challenges to claims of stable H3O2 structured water and unusual hydration effects"
  aapStructuredWater
  "AAP FactCheck 6 August 2024, chemist quotations and conclusion"
  aapFactCheckRoot
  Diligence.contestingEvidence
  institutionalHistoricalInterpretation
  "does not disprove measurable hydrodynamic swirl or ordinary dissolved oxygen change"

atmosphericElectricityBoundary : ClaimBound
atmosphericElectricityBoundary = mkBound
  "Fair-weather atmospheric electric field exists and can be monitored by electric-field mills"
  atmosphericFieldMill
  "PITHIA-NRF field-mill explainer"
  atmosphericResearchRoot
  Diligence.contextualEvidence
  externallyDescribedApparatus
  "caption 'Pignatelli motor' unverified; voltage gradient alone not demonstration of delivered shaft power"

oudinSpacedWindingFamily : ClaimBound
oudinSpacedWindingFamily = mkBound
  "A contemporary Oudin reconstruction uses a spaced, relatively coarse winding; Oudin is a family of resonant high-voltage apparatus, not one universal winding geometry"
  oudinBeharyRestoration
  "Oudin Coil 2010; paragraphs beginning 'The definition of Oudin Resonator' and 'The unique thing'"
  beharyRestorationRoot
  Diligence.contextualEvidence
  experimentalMechanismElsewhere
  "class precedent only; picture 1000018569 has pale periodic serpentine bands whose electrical connectivity cannot be read from pixels"

oudinSphereStreamerFamily : ClaimBound
oudinSphereStreamerFamily = mkBound
  "Behary built a high-voltage Oudin/Tesla resonator with a spherical copper topload and reported streamer production in ordinary air"
  oudinBeharySphere
  "Tesla/Oudin Coil with 6-inch Copper Sphere Topload; apparatus description and discharge paragraphs"
  beharyRestorationRoot
  Diligence.implementationEvidence
  experimentalMechanismElsewhere
  "maker-reported input/output details apply to Behary's device only; not to berndnindl, plasma healing, or the claimed floating orb"

oudinUnipolarHistoricalTopology : ClaimBound
oudinUnipolarHistoricalTopology = mkBound
  "A 1906 Oudin medical-electricity circuit diagram specifies one historically described unipolar resonator arrangement; a spherical terminal alone cannot establish a matching primary/secondary electrical topology"
  guilleminotOudinDiagram
  "Wellcome M0015155: catalogued photograph of diagram in Guilleminot, Handbook of electricity in medicine (1906)"
  guilleminotHistoricalManualRoot
  Diligence.contextualEvidence
  externallyDescribedApparatus
  "independent maker schematic and continuity check of 1000018569.png remain absent; historical clinical claims not supported by morphology"

jefimenkoSmallMotorField : ClaimBound
jefimenkoSmallMotorField = mkBound
  "Jefimenko reports powering a small electret motor and corona motor using earth-field antennas; explicitly leaves appreciable power / larger motors dependent on collectors"
  jefimenkoElectrostaticMotors
  "printed pp.114-117, especially Fig.57 and statements on p.117; scan PDF page indices 69-70; visually inspected 2026-10-24"
  jefimenkoAuthorRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "reported primary experiment, not independent exact-measurement receipt; Pignatelli name/creator circuit absent; input/output loading and antenna charging must be measured on that device"

itorusRifeLanguage : ClaimBound
itorusRifeLanguage = mkBound
  "The iTorus app publisher itself lists RIFE frequencies, zero-point access, 5D consciousness, biofield shielding, chakra and pineal activation"
  itorusAppPublisher
  "Google Play com.goodbarber.itorus, About this app, public version updated 13 July 2026"
  itorusAppPublisherRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "marketing vocabulary only; not evidence of waveform reproduction, disease treatment or consciousness effects; product/hardware maker and app publisher must remain distinct parties"

itorusRetailCoverageConflict : ClaimBound
itorusRetailCoverageConflict = mkBound
  "One Revive Pro Tech i9 Heart Stone page gives nominal coverage diameters 55 feet, 30 feet, and 24 feet in three separately labelled sections"
  itorusHeartStoneReseller
  "Hero near heading: 55 ft; Whole-House Recovery text: 30 feet; 360 Field Coverage section: 24 feet; inspected 24 October 2026"
  itorusRetailCopyRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "internal copy discrepancy rather than proof the exact same physical test used comparable threshold or drive; unresolved provenance of each number"

itorusImpedanceVariants : ClaimBound
itorusImpedanceVariants = mkBound
  "iPyramids branded i9 description reports 7.0 ohms/channel while reseller i9 Heart Stone advertises 8.5 ohms/channel"
  itorusHeartStoneReseller
  "Revive Pro Tech Technical Specs 8.5 ohm/channel; compare existing ipyramidsI9 attributed source 7.0 ohm/channel"
  itorusRetailCopyRoot
  Diligence.contextualEvidence
  attributedAuthorReport
  "different variants, production revisions, impedance versus DC resistance, or copy error unresolved; do not posit a single experimentally measured contradiction"

aurumayaSharedVocabulary : ClaimBound
aurumayaSharedVocabulary = mkBound
  "Aurumaya's homepage co-lists Tesla multi-wave oscillator disks, a 369-labelled ritual elixir, 432MHz-labelled tensor jewellery and Succor Punches"
  aurumayaHomeCatalogue
  "AURUMAYA home page: Featured Collection, ELIXIRS, View Our Frequency Jewellery; actual visible page does not list a 333-MHz pendant"
  aurumayaMakerRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "co-marketing cluster, not a same-source technical design genealogy, scalar-energy demonstration or a second independent Aurumaya witness"

jefimenko1971Bibliography : ClaimBound
jefimenko1971Bibliography = mkBound
  "WVU's Jefimenko bibliography records a 1971 American Journal of Physics article on atmospheric electric motor operation"
  jefimenko1971
  "AJP 39 (1971), 776-779; DOI 10.1119/1.1986281"
  jefimenkoAuthorRoot
  Diligence.contextualEvidence
  attributedAuthorReport
  "bibliographic identity and same-author provenance, not a new experimental reproduction; full article extraction and data remain a separate obligation"

aurumayaShop333Catalogue : ClaimBound
aurumayaShop333Catalogue = mkBound
  "Aurumaya shop indexes ACU-VAC pendants advertised with 333Mhz labels alongside 15Hz quartz kit offerings and Tesla multi-wave disks"
  aurumayaShopCatalogue
  "Shop Products, ACU-VAC pendants (333Mhz), QUBIT 15Hz listings and GOLD MULTI-WAVE OSCILLATOR item"
  aurumayaMakerRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "the numeral 333Mhz is a product-label assertion, not a frequency measurement; homepage 369 is a separate URL; same maker, not independent corroboration"

reichSeparation : ClaimBound
reichSeparation = mkBound
  "Museum distinguishes Reich's cloudbuster from later Welz/Croft orgonite, quartz-and-resin devices"
  reichMuseum
  "Mythconceptions section 14, with original cloudbuster construction in section 15"
  reichMuseumRoot
  Diligence.interpretiveEvidence
  institutionalHistoricalInterpretation
  "a direct primary design genealogy demonstrating equivalence is not supplied"

lakhovskyDesign : ClaimBound
lakhovskyDesign = mkBound
  "1934 patent describes concentric insulated open split-rings driven by high-frequency impulses"
  lakhovskyPatent
  "US1962565A description and claims 1-5"
  lakhovskyPatentRoot
  Diligence.primaryProposition
  externallyDescribedApparatus
  "independent efficacy evidence and a specific link to the pictured copper star are absent"

channonProposal : ClaimBound
channonProposal = mkBound
  "Channon proposed a First Earth Battalion concept; reproduced document disclaims official Army policy"
  channonManual
  "Task Force Delta concept paper; disclaimer preceding author's foreword"
  channonConceptRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "programme adoption and successful psychic performance not established"

gatewayProposal : ClaimBound
gatewayProposal = mkBound
  "McDonnell's 1983 Army assessment proposed a consciousness matrix/holographic-frequency interpretation"
  gateway1983
  "9 June 1983 memorandum; section titled The Consciousness Matrix"
  gatewayReportRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "no independent mechanism, operational test or contemporary creator transmission receipt"

airOperationalBoundary : ClaimBound
airOperationalBoundary = mkBound
  "AIR evaluated disputed remote-viewing research separately from operational intelligence usefulness"
  air1995
  "29 September 1995 final report, executive summary and operational assessment"
  airEvaluationRoot
  Diligence.primaryProposition
  institutionalHistoricalInterpretation
  "statistical controversies are not resolved by citation; no Succor Punch physical mechanism follows"

coronaAlternative : ClaimBound
coronaAlternative = mkBound
  "Corona discharge near bent sharp electrodes can create ionic wind and rotate an electric whirl"
  electricWhirl
  "Electric Whirl: Purpose and Demo Apparatus"
  boulderDemonstrationRoot
  Diligence.implementationEvidence
  experimentalMechanismElsewhere
  "actual footage, electrode geometry, power supply, frame-time series and spectroscopy needed to identify video apparatus"

------------------------------------------------------------------------
-- Cross-pollination edges. A documentary source naming BOTH objects
-- licenses only the stated textual co-occurrence, not downstream physics.
------------------------------------------------------------------------

data RelationClass : Set where
  reportedCoUseByActor : RelationClass
  documentaryDistinction : RelationClass
  hardwareAnalogyOnly : RelationClass
  thematicResemblanceOnly : RelationClass
  namedPersonMentionOnly : RelationClass
  explicitlyAttributedReading : RelationClass
  namedSymbolOnly : RelationClass
  namedExemplarsOnly : RelationClass
  contemporarySelfAttribution : RelationClass
  historicalMechanismPrecedentOnly : RelationClass
  commercialSpecificationOnly : RelationClass

record BoundedRelation : Set where
  constructor bounded-relation
  field
    subject : String
    object : String
    relationClass : RelationClass
    sourceClaim : ClaimBound
    newPhysicsEstablished : Bool
    newPhysicsEstablishedIsFalse : newPhysicsEstablished ≡ false
    historicalTransmissionProved : Bool
    historicalTransmissionProvedIsFalse : historicalTransmissionProved ≡ false
open BoundedRelation public

croftCloudbusterRelation : BoundedRelation
croftCloudbusterRelation =
  bounded-relation "Succor Punch prototype" "Croft cloudbuster"
    reportedCoUseByActor croftCoLocatedDevice false refl false refl

reichCroftRelation : BoundedRelation
reichCroftRelation =
  bounded-relation "Reich original cloudbuster" "Welz/Croft modern orgonite"
    documentaryDistinction reichSeparation false refl false refl

lakhovskyCopperRelation : BoundedRelation
lakhovskyCopperRelation =
  bounded-relation "Lakhovsky concentric split-ring oscillator" "Instagram copper star cage"
    hardwareAnalogyOnly lakhovskyDesign false refl false refl

gatewayTimelineRelation : BoundedRelation
gatewayTimelineRelation =
  bounded-relation "Gateway consciousness-matrix wording" "Instagram timeline-shifting claim"
    thematicResemblanceOnly gatewayProposal false refl false refl

croftRemoteViewingPersonMention : BoundedRelation
croftRemoteViewingPersonMention =
  bounded-relation "Don Croft 2002 discourse" "Ed Dames, later public remote-viewing figure"
    namedPersonMentionOnly croftMentionsEdDames false refl false refl

croftNamedBookRelation : BoundedRelation
croftNamedBookRelation =
  bounded-relation "Don Croft's own Reich introduction" "Serge Kahili King, Earth Energies (1992)"
    explicitlyAttributedReading croftNamesKing false refl false refl

croftStarSymbolRelation : BoundedRelation
croftStarSymbolRelation =
  bounded-relation "Croft's star tetrahedron geography passage" "Instagram angular copper weave"
    namedSymbolOnly croftNamesStarTetrahedron false refl false refl

croftNamedHistoricalExemplars : BoundedRelation
croftNamedHistoricalExemplars =
  bounded-relation "Don Croft" "Tesla, Rife, Schauberger and Mesmer name cluster"
    namedExemplarsOnly croftNamesTeslaRife false refl false refl

aurumayaSelfIdentifiesCroft : BoundedRelation
aurumayaSelfIdentifiesCroft = bounded-relation
  "Aurumaya QUBIT Quartz" "Don Croft Succor Punch"
  contemporarySelfAttribution aurumayaCroftClaim false refl false refl

iTorusCommercialSpecOnly : BoundedRelation
iTorusCommercialSpecOnly = bounded-relation
  "iTorus i9 commercial geometry" "room-sized coherent healing field"
  commercialSpecificationOnly itorusSpecBound false refl false refl

berndTowerGeometryAnalogy : BoundedRelation
berndTowerGeometryAnalogy = bounded-relation
  "berndnindl photograph 1000018569" "coarse-wound sphere-topped Oudin/Tesla resonator"
  hardwareAnalogyOnly oudinSpacedWindingFamily false refl false refl

oudinSphereDisplayAnalogy : BoundedRelation
oudinSphereDisplayAnalogy = bounded-relation
  "berndnindl spherical top and purple discharge" "Behary 2008 Oudin sphere topload"
  hardwareAnalogyOnly oudinSphereStreamerFamily false refl false refl

oudinHistoricalPrecedentOnly : BoundedRelation
oudinHistoricalPrecedentOnly = bounded-relation
  "Kassabian 1907 Oudin discharge" "berndnindl Oudin-named footage"
  historicalMechanismPrecedentOnly oudinHighVoltagePrecedent false refl false refl

historicTopologyComparisonOnly : BoundedRelation
historicTopologyComparisonOnly = bounded-relation
  "1906 Guilleminot Oudin circuit" "sphere-topped Bernd tower, 1000018569.png"
  hardwareAnalogyOnly oudinUnipolarHistoricalTopology false refl false refl

jefimenkoMotorClaimOnly : BoundedRelation
jefimenkoMotorClaimOnly = bounded-relation
  "Jefimenko's 1973 atmospheric-field motor report" "Pignatelli-labelled viral motor"
  historicalMechanismPrecedentOnly jefimenkoSmallMotorField false refl false refl

itorusExplicitRifeBridge : BoundedRelation
itorusExplicitRifeBridge = bounded-relation
  "Official iTorus app publisher wording" "Rife-frequency / zero-point / 5D / chakra cluster"
  contemporarySelfAttribution itorusRifeLanguage false refl false refl

itorusRetailClaimsUncalibrated : BoundedRelation
itorusRetailClaimsUncalibrated = bounded-relation
  "Single i9 Heart Stone reseller listing" "55 / 30 / 24 ft advertised coverage"
  commercialSpecificationOnly itorusRetailCoverageConflict false refl false refl

aurumayaCommercialVocabularyBridge : BoundedRelation
aurumayaCommercialVocabularyBridge = bounded-relation
  "Aurumaya house catalogue" "Tesla / 369 / 333 MHz tensor / Succor Punch"
  contemporarySelfAttribution aurumayaSharedVocabulary false refl false refl

aurumayaShopCoMarketing : BoundedRelation
aurumayaShopCoMarketing = bounded-relation
  "Aurumaya shop listings" "15Hz QUBIT / 333Mhz ACU-VAC / Tesla-labelled discs"
  contemporarySelfAttribution aurumayaShop333Catalogue false refl false refl

-- Imported source-attribution laws are used directly; no new source/role
-- ontology is needed. The proof obligations are the existing fields.
allSourcesRemainNonPromoting :
  (s : Source.AttributedSource) →
  Source.citationImportsProof s ≡ false
allSourcesRemainNonPromoting = Source.citationImportsProofIsFalse

allSourcesRemainNonAuthoritative :
  (s : Source.AttributedSource) →
  Source.citationCreatesAuthority s ≡ false
allSourcesRemainNonAuthoritative = Source.citationCreatesAuthorityIsFalse

snowballBoundary : Snowball.AttributionSnowballBoundary
snowballBoundary = Snowball.canonicalAttributionSnowballBoundary

-- WrongType barriers: no constructor can convert design resemblance,
-- documented investigation or source multiplicity into paranormal proof.
data ResemblanceProvesDeviceIdentity : Set where
data PatentProvesClinicalEfficacy : Set where
data ArmyArchiveProvesPsychicMechanism : Set where
data CroftMirrorsAreIndependentReplications : Set where

noVisualIdentityPromotion : ResemblanceProvesDeviceIdentity → ⊥
noVisualIdentityPromotion ()

noPatentClinicalPromotion : PatentProvesClinicalEfficacy → ⊥
noPatentClinicalPromotion ()

noGovernmentAuthorityPromotion : ArmyArchiveProvesPsychicMechanism → ⊥
noGovernmentAuthorityPromotion ()

noMirrorIndependencePromotion : CroftMirrorsAreIndependentReplications → ⊥
noMirrorIndependencePromotion ()
