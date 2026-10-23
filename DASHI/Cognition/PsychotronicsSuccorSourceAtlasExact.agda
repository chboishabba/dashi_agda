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
  "https://ipyramids.store/products/itorus-9-9-5-tachyon-vortex-pemf-4-0"
  Source.practitionerSource
  "manufacturer describes audio/app-driven toroidal coil; 7-ohm-per-channel, 9.5-inch diameter and claimed field dimensions remain manufacturer attestations, not independent B-field mapping or healthcare outcomes"
  Source.publicAttribution

aurumayaQubit : Source.AttributedSource
aurumayaQubit = Source.mkNoDOISource
  "Aurumaya"
  "QUBIT CRYSTAL: Large Pulsed Quartz Succor Punch, 15 Hz Crystal Tech"
  "maker's commercial product listing; inspected 2026-10-24"
  "undated product page"
  "https://www.aurumaya.com.au/product-page/qubit-crystal-large-pulsed-quartz-succor-punch-15hz-crystal-tech"
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
  "MAYU Water"
  "What is Vortexing Water?"
  "company explanation of MAYU Swirl rotating-water carafe"
  "undated web guide; inspected 2026-10-24"
  "https://mayuwater.com/a/resources/structured-water/what-is-vortexing-water"
  Source.practitionerSource
  "rotational water motion and possible ordinary aeration are distinct from claimed stable special hydration structures; brand identification in screenshot is an on-screen label"
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

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas = Source.mkSourceAtlas
  "Psychotronics Succor Punch historical and physical source atlas"
  "DASHI.Cognition.PsychotronicsSuccorSourceAtlasExact"
  (croftMay2002 ∷ croftJuly2002 ∷ croftAdventures ∷ reichMuseum ∷
   lakhovskyPatent ∷ channonManual ∷ gateway1983 ∷ air1995 ∷
   electricWhirl ∷ irvaTimeline ∷ kingEarthEnergies ∷
   ipyramidsI9 ∷ aurumayaQubit ∷ oudinHistoricalDiagram ∷
   mayuVortex ∷ aapStructuredWater ∷ atmosphericFieldMill ∷ [])
  "claim-relative historical sources and technical analogues only; no causal transmission, psychic effect, clinical efficacy, video identification or source-independence promotion"

-- The Croft 2002 pair, retrospective anthology, and reprints are distinct
-- document instances but cannot be counted as independent witnesses.
data LineageRoot : Set where
  croftAuthorRoot reichMuseumRoot lakhovskyPatentRoot : LineageRoot
  channonConceptRoot gatewayReportRoot airEvaluationRoot kingPublicationRoot : LineageRoot
  boulderDemonstrationRoot remoteViewingAssociationRoot : LineageRoot
  iPyramidsManufacturerRoot aurumayaMakerRoot oudinHistoricalRoot : LineageRoot
  mayuManufacturerRoot aapFactCheckRoot atmosphericResearchRoot : LineageRoot

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

oudinHistoricalPrecedentOnly : BoundedRelation
oudinHistoricalPrecedentOnly = bounded-relation
  "Kassabian 1907 Oudin discharge" "berndnindl Oudin-named footage"
  historicalMechanismPrecedentOnly oudinHighVoltagePrecedent false refl false refl

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
