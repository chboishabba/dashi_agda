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

zeroPointStarshipProductIndexed : Source.AttributedSource
zeroPointStarshipProductIndexed = Source.mkNoDOISource
  "Zero Point Tech, matching-handle store crystalpyramids96.com (actual Instagram account ownership unverified)"
  "PEMF Dark knight Protector Starship Harmonic Rife Coil & Amp"
  "public search-index reproduction of commercial product copy; native page returned HTTP 402 when directly opened, 24 October 2026"
  "undated indexed listing"
  "https://crystalpyramids96.com/products/pemf-dark-knight-rife-coil?variant=46117812928698"
  Source.practitionerSource
  "seller describes 24-point starship coil, quartz/iron frame, 50-W amplifier, phone-fed Rife signal and 1.25-inch neodymium sphere intended to 'dance'; a strong multiple-feature match to copper cage and ball, NOT original-video/model identity or measured field/piezoelectric effect"
  Source.publicAttribution

zeroPointMiniProductIndexed : Source.AttributedSource
zeroPointMiniProductIndexed = Source.mkNoDOISource
  "Zero Point Tech, matching-handle store crystalpyramids96.com"
  "PEMF Dark Knight Protector Starship Harmonic Rife Coil Mini"
  "another listed SKU; indexed product copy; direct page returned HTTP 402 in current web environment"
  "undated indexed listing"
  "https://crystalpyramids96.com/products/dark-knight-starship-coil-pemf-rife-machine-aux-to-phone-frequency-powered-vortex-iron-quartz-piezoelectric-magnet-included-upgraded-stronger-coil"
  Source.practitionerSource
  "seller explicitly describes phone-input coil with moveable included neodymium magnet vibrating audibly like speaker around 100-1000 Hz; corroborates intended conventional magnet-vibration principle within maker's OWN catalogue, not field magnitude or photographed device SKU"
  Source.publicAttribution

-- Openable original seller page: DIFFERENT 400-W GoldenEye variant,
-- not the 50-W indexed Dark Knight photographed candidate.
zeroPointGoldeneye24PointLive : Source.AttributedSource
zeroPointGoldeneye24PointLive = Source.mkNoDOISource
  "Zero Point Tech / crystalpyramids96.com"
  "24-point Icositetragram Starship GoldenEye energy-matrix harmonizer"
  "live original seller page with product illustrations and marketing specifications, inspected 25 October 2026"
  "undated versioned listing; live 2026-10-25"
  "https://crystalpyramids96.com/products/energy-matrix-harmonizer-24-point-starship-coil-sedona-red-rock-vortex-edition"
  Source.practitionerSource
  "separate 24-point 7-inch GoldenEye version advertises a 400-W amplifier and up-to-40-foot field; not the indexed 50-W Dark Knight, no physically calibrated output, original screenshot SKU unverified"
  Source.publicAttribution

-- Published patent applicant owns original design text; no mechanical
-- identity or independent effects are imported through citation.
wongStarAmplifierPatent : Source.AttributedSource
wongStarAmplifierPatent = Source.mkNoDOISource
  "Dennis Yat Wong"
  "Electromagnetic resonant frequency coil ion emitter"
  "published US patent application US20190269877A1, filed 2018-03-05 published 2019-09-05; FIG. 1 description explicitly offers 14 radial sleeves; aggregator legal status abandoned, not legal finding"
  "2019"
  "https://patents.google.com/patent/US20190269877A1/en"
  (Source.namedSourceKind "published US patent application")
  "amplified audio drives copper winding on star-like pillars; historical apparatus-family analogy, not 24-point Zero Point Tech inventor lineage, field/ion calibration, or proven therapeutic results"
  Source.publicAttribution

rodinSocialRelay : Source.AttributedSource
rodinSocialRelay = Source.mkNoDOISource
  "Pictame (third-party social-media index; captions attributed to @crystal_pyramids96 and @ipyramids, not independently authenticated)"
  "Rodin Coil Sacred Geometry: indexed creator excerpts"
  "aggregated social post snippets; retrieved 24 October 2026; native reel identity/hash unavailable"
  "undated excerpts in current index"
  "https://pictame.com/en/discover/hashtag/rodin-coil-sacred-geometry"
  Source.communitySource
  "caption attributed to @crystal_pyramids96 calls four builds 'Starship Rodin Coil' including Red Rock and Dark Knight with revised circuitry; separate caption attributed to @ipyramids invokes Marco Rodin and Randy Powell. Both are DERIVATIVE CAPTION copies, not original reel/source custody or independent confirmation"
  Source.publicAttribution

merchantStoreDirectory : Source.AttributedSource
merchantStoreDirectory = Source.mkNoDOISource
  "Merchant Genius (independent store directory)"
  "Zero Point Tech: crystalpyramids96.com Shopify Store Listing"
  "third-party indexed store catalogue; purported registration 3 November 2025; retrieved 24 October 2026"
  "2025 store directory record"
  "https://www.merchantgenius.io/shop/url/crystalpyramids96.com"
  Source.communitySource
  "identifies matching-handle domain as Zero Point Tech and enumerates 24-point Starship/Rodin coil models, amplifiers and sphere magnets; this strengthens matching product-family discovery but does not prove Instagram account ownership or authenticate original video"
  Source.publicAttribution

openhand2026FiveD : Source.AttributedSource
openhand2026FiveD = Source.mkNoDOISource
  "Open (Openhand)"
  "What Does It Actually Mean To Be Creating From 5D Consciousness?"
  "author-published article, 7 September 2026; exact primary page inspected 24 October 2026"
  "2026"
  "https://www.openhandweb.org/what-does-it-actually-mean-be-creating-5d-consciousness"
  Source.practitionerSource
  "explicit claim that 5D consciousness emerges from a torus singularity and Flower of Life; author explicitly distinguishes a unity/love notion as merely 4D. Cosmological belief claim, NOT geometry or EM field measurement"
  Source.publicAttribution

openhand2026RealitySplit : Source.AttributedSource
openhand2026RealitySplit = Source.mkNoDOISource
  "Open (Openhand)"
  "3D/5D Reality Split: A Calling To The Soul - Move Into the 5D Stream"
  "same author's 19 October 2026 public post, inspected 24 October 2026"
  "2026"
  "https://openhandweb.org/3d5d-reality-split-calling-soul-move-5d-stream"
  Source.practitionerSource
  "claim about accelerating planetary toroidal flow, alleged electromagnetic suppression and 3D high-tech simulation; again a metaphysical author statement, not calibrated magnetometry or independent source"
  Source.publicAttribution

hanleyNADA2018 : Source.AttributedSource
hanleyNADA2018 = Source.mkDOISource
  "Adam W. Hanley; Yoshio Nakamura; Eric L. Garland"
  "The Nondual Awareness Dimensional Assessment (NADA): New Tools to Assess Nondual Traits and States of Consciousness"
  "Psychological Assessment 30(12), 1625-1639; original validation, NADA-T and NADA-S"
  "2018"
  "10.1037/pas0000615"
  "https://doi.org/10.1037/pas0000615"
  Source.academicArticleSource
  "validated self-report measures distinguishing nondual awareness as state vs trait in studied populations; NADA-T self-transcendence/bliss dimensions do not prove fifth spacetime dimension or efficacy of a torus device"
  Source.publicAttribution

macleanMEQ2012 : Source.AttributedSource
macleanMEQ2012 = Source.mkDOISource
  "Katherine A. MacLean; Matthew W. Johnson; Robert R. Griffiths"
  "Factor Analysis of the Mystical Experience Questionnaire"
  "Journal for the Scientific Study of Religion 51(4), 721-737; 1602-person exploratory and 440-person confirmation samples, retrospective psilocybin experiences"
  "2012"
  "10.1111/j.1468-5906.2012.01685.x"
  "https://doi.org/10.1111/j.1468-5906.2012.01685.x"
  Source.academicArticleSource
  "30-item self-report with mystical/unity, positive mood, space-time transcendence and ineffability factors; initial validation in psilocybin retrospective accounts is not blanket validation for PEMF devices or metaphysical timeline shifts"
  Source.publicAttribution

nourEDI2016 : Source.AttributedSource
nourEDI2016 = Source.mkDOISource
  "Matthew M. Nour; Lisa Evans; David Nutt; Robin L. Carhart-Harris"
  "Ego-Dissolution and Psychedelics: Validation of the Ego-Dissolution Inventory"
  "Frontiers in Human Neuroscience 10:269; originally validated in reports of psychedelic/drug experiences"
  "2016"
  "10.3389/fnhum.2016.00269"
  "https://doi.org/10.3389/fnhum.2016.00269"
  Source.academicArticleSource
  "eight-item subjective ego-dissolution scale distinguishable from ego-inflation; it cannot establish lasting moral development, material torus field, or a paranormal cause"
  Source.publicAttribution

kervadecFiveDASC2026 : Source.AttributedSource
kervadecFiveDASC2026 = Source.mkDOISource
  "Ewen Kervadec; Pauline Mathieu; Baptiste Fauvel; Lana Strika-Bruneau; collaborators"
  "Psychometric validation of the French version of the five-dimensional altered states of consciousness questionnaire (5D-ASC) and associated 11 OAV subscales"
  "Progress in Neuro-Psychopharmacology and Biological Psychiatry 147:111770; N=777 naturalistic substance-related reports"
  "2026"
  "10.1016/j.pnpbp.2026.111770"
  "https://doi.org/10.1016/j.pnpbp.2026.111770"
  Source.academicArticleSource
  "5D means FIVE PSYCHOMETRIC FACTORS, not 5D spiritual consciousness. Study reports better 11-subscale fit but marginal CFI, alpha reliability and limitations of language/population transport; does not validate a PEMF intervention"
  Source.publicAttribution

stockerASCRevision2026 : Source.AttributedSource
stockerASCRevision2026 = Source.mkDOISource
  "Kurt Stocker; Matthias Hartmann; Yasmin Schmid; Severin B. Vogt; collaborators"
  "The 3D-ASCr scale: A revalidation of core dimensions of the Altered States of Consciousness Rating Scale 5D(11)-ASC"
  "Journal of Psychopharmacology 40(5):850-862; published online 26 December 2025, issue May 2026; 901 questionnaires from 398 participants in 16 psychedelic studies"
  "2026 issue; online 2025"
  "10.1177/02698811251397328"
  "https://doi.org/10.1177/02698811251397328"
  Source.academicArticleSource
  "revisits competing altered-state factor models; proposes positive, distressing, perceptual broad dimensions. This challenges treating scale labels as eternal natural categories and is specific to psychedelic research context"
  Source.publicAttribution

heartmathEnergeticCommunication : Source.AttributedSource
heartmathEnergeticCommunication = Source.mkNoDOISource
  "HeartMath Institute"
  "Energetic Communication"
  "institutional self-description of human heart electric/magnetic field and suggested interpersonal energetic information transfer; undated live page inspected 2026-10-24"
  "undated online article"
  "https://www.heartmath.org/research/science-of-the-heart/energetic-communication/"
  Source.institutionalSource
  "HeartMath is distinct from hoe_math. Heart-generated bioelectromagnetic fields are measurable with appropriate sensors, but the institute's stronger interpersonal information/coherence claims are separate hypotheses and are not established by its narrative"
  Source.publicAttribution

shupakShamClinical2006 : Source.AttributedSource
shupakShamClinical2006 = Source.mkDOISource
  "N. M. Shupak; Julia C. McKay; Warren R. Nielson; Gary B. Rollman; Frank S. Prato; Alex W. Thomas"
  "Exposure to a specific pulsed low-frequency magnetic field: a double-blind placebo-controlled study of effects on pain ratings in rheumatoid arthritis and fibromyalgia patients"
  "Pain Research & Management 11(2), 85-90; N=31 across RA and FM populations; reported blinded low-frequency PEMF sham and active comparison"
  "2006"
  "10.1155/2006/842162"
  "https://pubmed.ncbi.nlm.nih.gov/16770449/"
  Source.academicArticleSource
  "actual double-blind 2006 physical PEMF comparison using silent/no-vibration sham apparatus, not evidence that an audible Starship/Rodin coil could be equivalently masked or that a nondual outcome was tested"
  Source.publicAttribution

duAssessorBlindedProtocol2026 : Source.AttributedSource
duAssessorBlindedProtocol2026 = Source.mkDOISource
  "Tianzhu Du; Xu Hu; Yu Dan; Yu Zhou; Hongyuan Liu; Fei Wang; Jun Tao"
  "Active vs. sham pulsed electromagnetic field therapy added to standardized conservative care for partial-thickness supraspinatus tears: study protocol for a randomized, assessor-blinded, sham-controlled trial"
  "Frontiers in Sports and Active Living 8:1847412, published 15 July 2026; study protocol with planned recruitment, not published trial results"
  "2026"
  "10.3389/fspor.2026.1847412"
  "https://doi.org/10.3389/fspor.2026.1847412"
  Source.academicArticleSource
  "trial protocol explicitly proposes matching active and sham heat/vibration/indicators/interaction and magnetic detector verification, but does not supply completed observations or proof of successful blinding at another manufacturer's device"
  Source.publicAttribution

------------------------------------------------------------------------
-- Original-source Phase-1 critical document joins.
-- The 2013/2024 published numbers and 2024 numbered citations are NOT
-- independently replicated measurements or adjudications of misconduct.
-- Croft's 2002 and 2003 instructions are ONE Croft narrator root.
------------------------------------------------------------------------

croftBigSecret2002 : Source.AttributedSource
croftBigSecret2002 = Source.mkNoDOISource
  "Don Croft"
  "The Big Secret"
  "15 August 2002 dated article; exact original educate-yourself.org URL retained by Ken Adachi and Croft Zappers later reprint"
  "2002"
  "https://www.croftzappers.com/the-don-croft-archives"
  Source.archivalSource
  "author stated he would not publish Mobius construction instructions at that time; NOT proof he contradicted a later different-design public guide or that described paranormal claims occurred"
  Source.publicAttribution

croftPowerWand2003 : Source.AttributedSource
croftPowerWand2003 = Source.mkNoDOISource
  "Don Croft"
  "The PowerWand, Everyman's Weapon Against Tyranny"
  "26 January 2003 byline; original educate-yourself.org/dc/adc52thepowerwand26jan03.shtml; Croft Zappers preserves author text"
  "2003"
  "https://www.croftzappers.com/the-don-croft-archives"
  Source.archivalSource
  "first-person author referral to www.cloud-busters.com for Mobius-wrapping directions; explicitly thanks Ben Morton, Suze Hooten and Bruce Stenulson, mentions Mark Hooten; this is Croft testimony not their original statements or verified claims"
  Source.publicAttribution

saikiaAmyloid2019 : Source.AttributedSource
saikiaAmyloid2019 = Source.mkDOISource
  "Jahnu Saikia; Gaurav Pandey; Sajitha Sasidharan; Ferrin Antony; Harshal B. Nemade; Sachin Kumar; Nitin Chaudhary; Vibin Ramakrishnan"
  "Electric Field Disruption of Amyloid Aggregation: Potential Noninvasive Therapy for Alzheimer's Disease"
  "ACS Chemical Neuroscience 10(5):2250-2262; online 15 February 2019; original ACS publisher metadata and abstract read, full article uninspected"
  "2019"
  "10.1021/acschemneuro.8b00490"
  "https://doi.org/10.1021/acschemneuro.8b00490"
  Source.academicArticleSource
  "authors report external electric/magnetic effects on amyloid peptide aggregation and 15-38 percent reduced toxicity of electric-field-treated peptides in cultured-cell settings; abstract does not itself describe a Rodin-versus-Helmholtz 60 percent comparison"
  Source.publicAttribution

perezRodinRSI2013 : Source.AttributedSource
perezRodinRSI2013 = Source.mkDOISource
  "H. Pérez; T. Cordova-Fraga; S. López-Briones; J. C. Martínez-Espinosa; E. F. Rosas; A. Espinoza; J. C. Villagómez-Castro; M. Sosa; S. Topsu; J. J. Bernal-Alvarado"
  "Portable device for magnetic stimulation: Assessment survival and proliferation in human lymphocytes"
  "Review of Scientific Instruments 84, 094701; online 9 September 2013; original publisher pages read in rehosted author manuscript"
  "2013"
  "10.1063/1.4819796"
  "https://doi.org/10.1063/1.4819796"
  Source.academicArticleSource
  "Table I measured magnetic field at 1.60A=4.13mT, 1.25A=3.05mT, 0.60A=1.16mT; gadolinium-containing cultured lymphocyte exposures; no independent later source-stream date or clinical effect"
  Source.publicAttribution

ramirezRodinRMF2024 : Source.AttributedSource
ramirezRodinRMF2024 = Source.mkDOISource
  "A. D. Ramírez-Galindo; H. A. Pérez-Olivas; G. Basurto-Islas; A. Hernández-Rayas; F. González López; T. Cordova-Fraga"
  "Vortex magnetic induction: Mathematical, geometric and experimental characterization"
  "Revista Mexicana de Física 70(3):030901, May-June 2024 issue; original PDF read, SciELO electronic edition 22 September 2025 SAME work"
  "2024"
  "10.31349/RevMexFis.70.030901"
  "https://doi.org/10.31349/RevMexFis.70.030901"
  Source.academicArticleSource
  "Table II repeats three current and measured-field pairs from 2013; original discussion cites ref24 Saikia 2019 for purported Rodin/Helmholtz 60 percent effect; ref12 names F. P. Perez 2008 not H. Perez 2013; no source-level evidence of two independent sets"
  Source.publicAttribution

perezHeatShock2008 : Source.AttributedSource
perezHeatShock2008 = Source.mkDOISource
  "Felipe P. Perez; Ximing Zhou; Jorge Morisaki; Donald A. Jurivich"
  "Electromagnetic field therapy delays cellular senescence and death by enhancement of the heat shock response"
  "Experimental Gerontology 43(4), 307-316; e-published 29 January 2008; original publisher and PubMed PMID 18325704 abstracts inspected, full article not page-inspected"
  "2008"
  "10.1016/j.exger.2008.01.004"
  "https://doi.org/10.1016/j.exger.2008.01.004"
  Source.academicArticleSource
  "2008 uses 50 MHz 0.5 W repeated EM-field shock in primary human T lymphocytes AND fibroblast lines, thus not irrelevant to lymphocyte biology; nevertheless different field and heat-shock/senescence endpoint from H. Perez et al 2013 100-2500 Hz Rodin-coil protocol; named as 2024 RMF reference 12"
  Source.publicAttribution

------------------------------------------------------------------------
-- Literature-first cloudbusting recovery: unlike traditions, original
-- author roots, separate publisher/museum custody and 1953 event records.
-- All citations remain source claims, not experiments on cloud causation.
------------------------------------------------------------------------

reichCoreEllsworth1954 : Source.AttributedSource
reichCoreEllsworth1954 = Source.mkNoDOISource
  "Wilhelm Reich"
  "Cosmic Orgone Engineering (CORE), vol VI nos 1-4, OROP Ellsworth"
  "July 1954 author publication reproducing 8 July 1953 protocol; 92-page later transcription PDF pages 57 and 59 inspected"
  "1954"
  "https://www.quebecorgone.com/wilhelm_reich_books/Wilhelm-Reich_-_Cosmic-Orgone-Engineering-1954.pdf"
  Source.archivalSource
  "claims 5 and 6 July 1953 preparations, 6 July 10:45-11:52 ten-tube water-cable use, rain about 22:00, and an incoming western weather front, then conjectures causal atmospheric orgone response; protocol not controlled weather-causation proof"
  Source.publicAttribution

reichCloudArchiveIndex : Source.AttributedSource
reichCloudArchiveIndex = Source.mkNoDOISource
  "Wilhelm Reich Infant Trust"
  "Index of the Wilhelm Reich Archives, Orgone Institute Boxes 24 and 25"
  "Original archival finding aid hosted by Wilhelm Reich Museum; PDF pages 85 and 86 inspected, individual listed items not obtained"
  "2011"
  "https://wilhelmreichmuseum.org/wp-content/uploads/2023/03/Index-of-the-Wilhelm-Reich-Archives.pdf"
  Source.archivalSource
  "lists Reich apparatus and rules, William Moise original operations records, Ellsworth 1953 files, Southworth construction correspondence and 24 July 1953 Bangor Daily News clipping; catalogue confirms custody rather than rain causality"
  Source.publicAttribution

hamblingWeatherwatch2011 : Source.AttributedSource
hamblingWeatherwatch2011 = Source.mkNoDOISource
  "David Hambling"
  "Weatherwatch: Wilhelm Reich's cloudbuster"
  "The Guardian, 6 July 2011 EDT / 7 July 2011 AEST; photo separately credited Robert F. Bukaty / AP"
  "2011"
  "https://www.theguardian.com/news/2011/jul/06/weatherwatch-cloudbuster"
  Source.archivalSource
  "2011 secondary journalism repeats 1953 Maine story and contrasts Reich water tubes with generic modern resin-quartz copper-pipe bucket, but no independent measurement or verified maker source"
  Source.publicAttribution

kiddexRedditMind2023 : Source.AttributedSource
kiddexRedditMind2023 = Source.mkNoDOISource
  "u/Kiddex77 and separately attributed r/energy_work commenters"
  "Anybody heard of Cloudbusting?"
  "Original Reddit discussion 2023 with later comments/edits; entire user-supplied Pasted text.txt and live public thread examined"
  "2023"
  "https://www.reddit.com/r/energy_work/comments/15v97ae/anybody_heard_of_cloudbusting/"
  Source.practitionerSource
  "OP describes purely mental intentional cloud-dissipation practice, with distinct commenters crediting Richard Bach, Trevor Constable and Neil Slade; testimonials are not independent meteorological evidence"
  Source.publicAttribution

bachIllusions1977 : Source.AttributedSource
bachIllusions1977 = Source.mkNoDOISource
  "Richard Bach"
  "Illusions: The Adventures of a Reluctant Messiah"
  "1977 original fiction; publisher later ebook identifies original copyright, user Reddit readers explicitly name its cloud-vaporising episode"
  "1977"
  "https://www.everand.com/book/769548154/Illusions-The-Adventures-of-a-Reluctant-Messiah"
  Source.archivalSource
  "fictional mentor/student mental cloud-dissipation episode in a novel, NOT a real cloud experiment or a claim of a verified nonlocal effect"
  Source.publicAttribution

constableCosmicPulse1976 : Source.AttributedSource
constableCosmicPulse1976 = Source.mkNoDOISource
  "Trevor James Constable"
  "The Cosmic Pulse of Life"
  "Original USA 1976 Merlin Press / UK 1977 edition National Library of New Zealand catalogue, original full book uninspected"
  "1976"
  "https://natlib.govt.nz/records/21985756"
  Source.archivalSource
  "book is an original named influence in later Reddit testimony; 1977 reviewer links some Reich cloudbuster and speculative UFO traditions; book's specific mental technique pages unread"
  Source.publicAttribution

sladeMindCloud1998 : Source.AttributedSource
sladeMindCloud1998 = Source.mkNoDOISource
  "Neil Slade"
  "Cloudbusting and claimed brain self-control"
  "author-maintained webpage claims first publication 7 June 1998 and retains 2007 reader reports, edits and advertising"
  "1998"
  "https://www.neilslade.com/cloud.html"
  Source.practitionerSource
  "original practitioner describes visualisation without tubes and supposed amygdala/brain-mediated cloud dissolution; reader testimonials do not validate selective weather effects or clinical neuroscience"
  Source.publicAttribution

croftMoonbustingEarly2002 : Source.AttributedSource
croftMoonbustingEarly2002 = Source.mkNoDOISource
  "Don Croft"
  "Moonbusting Part 2"
  "original named Croft article preserved by educate-yourself.org, internal as-of-March-2002 claim, full original HTML opening failed"
  "2002"
  "https://educate-yourself.org/dc/adcmoonbustingpt2.shtml"
  Source.practitionerSource
  "author compares water-grounded original Reich tubes with resin-base portable modern Chembuster and asserts far-reaching cloud/chemtrail action; date and claimed physical efficacy unpaid"
  Source.publicAttribution

adachiEditedChembusterIndex : Source.AttributedSource
adachiEditedChembusterIndex = Source.mkNoDOISource
  "Ken Adachi"
  "Orgone Generators: Chembusters, Powerwands, Pyramids, Domes, Ground Cones and Tower Busters"
  "publisher and seller index since Jan 2002 with explicit subsequent content and prices edited at least through April 2011; separate Don Croft named original maker"
  "2011"
  "https://educate-yourself.org/dc/orgonegenindex.shtml"
  Source.practitionerSource
  "author describes six copper or iron pipes, quartz crystals and resin-metal bucket device, attributed to Croft, and asserts cloud control; these are later maker/publisher assertions not weather efficacy data"
  Source.publicAttribution

wmoWeatherModification2025 : Source.AttributedSource
wmoWeatherModification2025 = Source.mkNoDOISource
  "World Meteorological Organization"
  "WMO Statement on Weather Modification"
  "14 June 2025 institutional statement specifying evidence review through June 2024, first-party original read"
  "2025"
  "https://public.wmo.int/content/wmo-statement-weather-modification"
  Source.academicArticleSource
  "limits evidence to specific weather modification interventions including glaciogenic seeding; warns enormous weather energy excludes casual creation or redirection of large weather systems; not a direct test of Reich, Croft, or mind-only clouds"
  Source.publicAttribution

peterReichDreams1973 : Source.AttributedSource
peterReichDreams1973 = Source.mkNoDOISource
  "Peter Reich"
  "A Book of Dreams"
  "Harper and Row release 25 April 1973 per contemporary Kirkus review; memoir full text uninspected"
  "1973"
  "https://www.kirkusreviews.com/book-reviews/a/peter-reich-2/a-book-of-dreams/"
  Source.archivalSource
  "son's memory and historical depiction of his father Wilhelm's rainmaker apparatus, later directly credited as inspiration by Kate Bush, not proof clouds were caused"
  Source.publicAttribution

bushCloudbusting1985 : Source.AttributedSource
bushCloudbusting1985 = Source.mkNoDOISource
  "Kate Bush"
  "Cloudbusting, original author credit to Peter Reich's A Book of Dreams"
  "1985 Kate Bush Club first-person source quoted by 2015 Dazed original-participant article; newsletter actual issue not inspected"
  "1985"
  "https://dev2.dazeddigital.com/music/article/27217/1/the-story-behind-kate-bush-s-cloudbusting-video"
  Source.archivalSource
  "musician acknowledges direct creative influence from Peter Reich memoir for a song/video, independent cultural authorship but not meteorological demonstration"
  Source.publicAttribution

------------------------------------------------------------------------
-- First-party original regional weather observations and exact place join
-- (historical Maine rainfall is independently recorded, not rainmaking).
------------------------------------------------------------------------

noaaBangorGHCN1953 : Source.AttributedSource
noaaBangorGHCN1953 = Source.mkNoDOISource
  "NOAA National Centers for Environmental Information (GHCN-Daily station observations)"
  "Bangor Maine USW00014606 original daily PRCP July 1953"
  "original NCEI .dly weather-station fixed-width line USW00014606195307PRCP, source retrieved 25 October 2026"
  "1953"
  "https://www.ncei.noaa.gov/pub/data/ghcn/daily/all/USW00014606.dly"
  Source.archivalSource
  "Original station counts in tenths mm: 5 July 0, 6 July 66, 7 July 193, 8 July 46, 9 July 74. Independently establishes recorded regional Bangor rain, not Ellsworth onset or causal device effect."
  Source.publicAttribution

-- Two station streams under the same NOAA GHCN custodial family are NOT
-- two independent publishers or two rainmaking experiments.
noaaBarHarborGHCN1953 : Source.AttributedSource
noaaBarHarborGHCN1953 = Source.mkNoDOISource
  "NOAA NCEI GHCN-Daily; historical Bar Harbor 3 NW Maine station observers"
  "Bar Harbor 3 NW Maine USC00170371 original daily PRCP July 1953"
  "official NOAA browser-read 269-column July row USC00170371195307PRCP on 26 October 2026; complete original publisher file bytes not downloaded"
  "1953"
  "https://www.ncei.noaa.gov/pub/data/ghcn/daily/all/USC00170371.dly"
  Source.archivalSource
  "July 5=0, 6=0, 7=130, 8=0, 9=10 tenths-mm; 6–8 = 13.0 mm; original hourly gauge cutoff and Reich local onset not established"
  Source.publicAttribution

noaaBarHarborStationMetadata : Source.AttributedSource
noaaBarHarborStationMetadata = Source.mkNoDOISource
  "NOAA NCEI Climate Data Online (same GHCN custodian as station rows)"
  "BAR HARBOR 3 NW Maine USC00170371 original station identity"
  "official original metadata: 44.41667 north, 68.25 west, 34.1m, 1893-01-01 through 1982-08-31; inspected 26 October 2026"
  "1953"
  "https://www.ncdc.noaa.gov/cdo-web/datasets/GHCND/stations/GHCND%3AUSC00170371/detail"
  Source.archivalSource
  "Identifies historical Maine observation station, not Bar Harbor airport beginning 2005 or the Ellsworth experiment gauge"
  Source.publicAttribution

noaaBangorStationMetadata : Source.AttributedSource
noaaBangorStationMetadata = Source.mkNoDOISource
  "NOAA NCEI Climate Data Online (same institutional root as raw station)"
  "Bangor International Airport Maine GHCND USW00014606 station metadata"
  "original NOAA network ID and coordinates 44.79791 N, 68.81852 W; period of record starts 1953-01-01"
  "1953"
  "https://www.ncdc.noaa.gov/cdo-web/datasets/GHCND/stations/GHCND%3AUSW00014606/detail"
  Source.archivalSource
  "Anchors exact raw .dly station and region; not another instrument stream or measurement in Ellsworth."
  Source.publicAttribution

ellsworthAmericanJuly1953 : Source.AttributedSource
ellsworthAmericanJuly1953 = Source.mkNoDOISource
  "The Ellsworth American (1953 newspaper publisher; item author unidentified)"
  "Rain Monday Night Caused By Rainmakers"
  "8 July 1953 article; searchable clipping reproduction in later Reich CORE printed documentary section, not original paper issue inspected"
  "1953"
  "https://rexresearch1.com/ReichOrgoneLibrary/ReichCORE.pdf"
  Source.archivalSource
  "Earlier press account of 6 July Reich/Orgone Institute cloudbuster demonstration and rain around 22:00; content may derive from institute press release, no independent observation proven"
  Source.publicAttribution

bangorLibraryNewspaperArchives : Source.AttributedSource
bangorLibraryNewspaperArchives = Source.mkNoDOISource
  "Bangor Public Library"
  "Bangor Daily News newspaper archive 1832 to 2011 access route"
  "current original archive-provider website; authenticated July 24 1953 Anthony R Shannon original newsprint has not been read"
  "2026"
  "https://bangorpubliclibrary.org/digital-content/newspapers-magazines/"
  Source.archivalSource
  "institutional route to original contemporary newspaper page, not newspaper body text or weather effect verification"
  Source.publicAttribution

ellsworthKansasFalseWeatherJoin : Source.AttributedSource
ellsworthKansasFalseWeatherJoin = Source.mkNoDOISource
  "ExtremeWeatherWatch (secondary NOAA-derived source for Ellsworth Kansas)"
  "Ellsworth Kansas weather in 1953 — geographically inapplicable to Reich Maine"
  "webpage headline merely Ellsworth; first line explicitly states Ellsworth Kansas; 25 Oct 2026 retrieval"
  "2026"
  "https://www.extremeweatherwatch.com/cities/ellsworth/year-1953"
  Source.archivalSource
  "same city spelling but Kansas location; July 1953 weather on that page cannot be assigned to Ellsworth Maine"
  Source.publicAttribution

-- 2003 primary EVENT organiser and later SAME-ORGANISER video page are
-- separate source carriers, not two independent historical witnesses.
-- Croft and RVML remain different root speakers/custodians. Neither RVML
-- carrier independently attests a 1999 Flanagan-to-Gentry-to-Croft plan.
rvmlGentry2003Programme : Source.AttributedSource
rvmlGentry2003Programme = Source.mkNoDOISource
  "Rogue Valley Metaphysical Library and Event Center (organiser)"
  "Secrets of Electronic Medicine by Gentry Smith: 4 November 2003 RVML event"
  "original RVML 2003 November dated calendar; directly opening archive now 403 but indexed original host programme independently inspected"
  "2003"
  "https://rvml.org/calendar/wc112003s.htm"
  Source.communitySource
  "organiser lists Gentry Smith as 4 November 2003 lecture speaker; no published coil directions, independently identified Croft handoff, verified employment or medical results"
  Source.publicAttribution

rvmlGentryVideoMetadata : Source.AttributedSource
rvmlGentryVideoMetadata = Source.mkNoDOISource
  "RVML Community Resource Center (uploader; claimed speaker Gentry Smith)"
  "Gentry Smith - Secrets of Electronic Medicine, Vimeo 92437258"
  "original organiser-uploader page indexed; playback/film date/transcript not inspected; same title/speaker/institution as 2003 event"
  "upload date unknown; linked 2003 event unconfirmed footage identity"
  "https://vimeo.com/92437258"
  Source.communitySource
  "promotional metadata lists Pat Flanagan electronic device and says Gentry constructed Reich Cloudbusters; both are uploader biographical/topic statements, not authenticated first-person speech, blueprints, military personnel records, shared coil transmission or medical/meteorological performance"
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
   aurumayaHomeCatalogue ∷ aurumayaShopCatalogue ∷ jefimenko1971 ∷
   zeroPointStarshipProductIndexed ∷ zeroPointMiniProductIndexed ∷
   zeroPointGoldeneye24PointLive ∷ wongStarAmplifierPatent ∷
   rodinSocialRelay ∷ merchantStoreDirectory ∷
   openhand2026FiveD ∷ openhand2026RealitySplit ∷
   hanleyNADA2018 ∷ macleanMEQ2012 ∷ nourEDI2016 ∷
   kervadecFiveDASC2026 ∷ stockerASCRevision2026 ∷
   heartmathEnergeticCommunication ∷
   shupakShamClinical2006 ∷ duAssessorBlindedProtocol2026 ∷
   croftBigSecret2002 ∷ croftPowerWand2003 ∷ saikiaAmyloid2019 ∷
   perezRodinRSI2013 ∷ ramirezRodinRMF2024 ∷ perezHeatShock2008 ∷
   reichCoreEllsworth1954 ∷ reichCloudArchiveIndex ∷
   hamblingWeatherwatch2011 ∷ kiddexRedditMind2023 ∷
   bachIllusions1977 ∷ constableCosmicPulse1976 ∷ sladeMindCloud1998 ∷
   croftMoonbustingEarly2002 ∷ adachiEditedChembusterIndex ∷
   wmoWeatherModification2025 ∷ peterReichDreams1973 ∷
   bushCloudbusting1985 ∷ noaaBangorGHCN1953 ∷
   noaaBangorStationMetadata ∷ noaaBarHarborGHCN1953 ∷
   noaaBarHarborStationMetadata ∷ ellsworthAmericanJuly1953 ∷
   bangorLibraryNewspaperArchives ∷ ellsworthKansasFalseWeatherJoin ∷
   rvmlGentry2003Programme ∷ rvmlGentryVideoMetadata ∷ [])
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
  zeroPointCommercialRoot rodinSocialMirrorRoot merchantDirectoryRoot : LineageRoot
  wongPublishedPatentRoot : LineageRoot
  openhandAuthorRoot : LineageRoot
  hanleyPsychometricsRoot macleanPsychometricsRoot nourPsychometricsRoot : LineageRoot
  kervadecAscValidationRoot stockerAscRevisionRoot : LineageRoot
  heartmathInstituteRoot : LineageRoot
  shupakClinicalAuthorRoot duProtocolAuthorRoot : LineageRoot
  saikia2019ResearchRoot guanajuatoRodinResearchRoot perez2008HeatShockRoot : LineageRoot
  reichOriginalAuthorRoot guardianHamblingRoot redditKiddexForumRoot : LineageRoot
  bachFictionRoot constableBookRoot sladePractitionerRoot adachiPublisherRoot : LineageRoot
  wmoInstitutionRoot peterReichMemoirRoot kateBushArtistRoot : LineageRoot
  noaaBangorWeatherRoot ellsworthAmericanPressRoot bangorLibraryRoot : LineageRoot
  kansasWeatherPortalRoot : LineageRoot
  rvmlOrganizerPublicationRoot : LineageRoot

data EvidenceCeiling : Set where
  attributedAuthorReport : EvidenceCeiling
  externallyDescribedApparatus : EvidenceCeiling
  institutionalHistoricalInterpretation : EvidenceCeiling
  experimentalMechanismElsewhere : EvidenceCeiling
  scopedValidatedSelfReport : EvidenceCeiling
  modernVisualIdentificationUnpaid : EvidenceCeiling
  originalRegionalWeatherMeasurement : EvidenceCeiling

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

-- Two publisher/document carriers; same RVML provenance root. The Gentry
-- speaker/topic is NOT the 1999 person-to-person instruction transfer.
rvmlGentryNamedEvent : ClaimBound
rvmlGentryNamedEvent = mkBound
  "RVML original November 2003 calendar publicly names Gentry Smith as speaker on electronic-medicine topics"
  rvmlGentry2003Programme
  "RVML November 2003 archived calendar, Tuesday 4 November"
  rvmlOrganizerPublicationRoot
  Diligence.contextualEvidence
  institutionalHistoricalInterpretation
  "named contemporary speaker and scheduled event only; identity with Croft's Gentry and 1999 instruction handoff unverified"

rvmlGentryFlanaganAdvertisedTopic : ClaimBound
rvmlGentryFlanaganAdvertisedTopic = mkBound
  "RVML uploader's description advertises a Pat Flanagan electronic device among purported Gentry Smith lecture topics"
  rvmlGentryVideoMetadata
  "Vimeo 92437258 original RVML uploader description; audio not inspected"
  rvmlOrganizerPublicationRoot
  Diligence.contextualEvidence
  institutionalHistoricalInterpretation
  "independent of Croft publisher but only same-organiser topic adjacency; speech, professional assistant relationship and handwritten winding provenance unpaid"

rvmlGentryReichCloudbusterPublicity : ClaimBound
rvmlGentryReichCloudbusterPublicity = mkBound
  "RVML original Vimeo publisher-description says Gentry Smith had designed and constructed Reich Cloudbusters and advertises Pat Flanagan's electronic device"
  rvmlGentryVideoMetadata
  "Vimeo 92437258 RVML Community Resource Center promotional description paragraphs"
  rvmlOrganizerPublicationRoot
  Diligence.contextualEvidence
  attributedAuthorReport
  "no original Gentry coil drawings or contemporaneous build receipt, independent Navy/personnel documentation, spoken recording verification, meteorological measurement or 1999 Flanagan-to-Croft instruction handoff"

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

zeroPointStarshipSphereClaim : ClaimBound
zeroPointStarshipSphereClaim = mkBound
  "Indexed seller copy describes 24-point Starship coil with 50-W amplifier and 1.25-inch neodymium sphere magnet that is designed to move when an input waveform drives the coil"
  zeroPointStarshipProductIndexed
  "Product description, paragraphs beginning 'Description: This 24-pointed starship coil' and 'The included 1.25-inch neodymium sphere magnet'"
  zeroPointCommercialRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "SEARCH INDEX ONLY, native page HTTP402; named Instagram actor matching domain not independently verified, exact physical pictured SKU and sphere motion not directly instrumented"

zeroPointMiniMagnetResponse : ClaimBound
zeroPointMiniMagnetResponse = mkBound
  "Seller's separate Dark Knight Mini listing describes an included neodymium magnet that vibrates audibly at higher audio drive as if a small speaker"
  zeroPointMiniProductIndexed
  "Product description, section 'Important - How to Know It's Working'"
  zeroPointCommercialRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "not the exact 24-point product, no external field magnitude measurement, induction/vibration possible without special crystal energy"

zeroPointGoldeneyeMakerClaim : ClaimBound
zeroPointGoldeneyeMakerClaim = mkBound
  "Illustrated 24-point GoldenEye Starship manufacturer listing names a 400-W amplifier and up-to-40-ft field, but neither the original screenshot variant nor calibrated physical power and fields"
  zeroPointGoldeneye24PointLive
  "GoldenEye 7-inch specification, WHAT YOU'RE ACTUALLY BUYING and HOW IT WORKS sections"
  zeroPointCommercialRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "native reel/SKU, exact winding, field-versus-distance threshold, source current and independent laboratory measurements unpaid"

zeroPointWebsiteLinksOriginalHandle : ClaimBound
zeroPointWebsiteLinksOriginalHandle = mkBound
  "The Zero Point Tech manufacturer's own illustrated GoldenEye shop page has an Instagram footer link directly to instagram.com/crystal_pyramids96, the user-screenshot posting handle"
  zeroPointGoldeneye24PointLive
  "Footer Instagram social navigation anchor resolved directly to https://www.instagram.com/crystal_pyramids96, 25 October 2026"
  zeroPointCommercialRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "direct first-party shop-to-handle declared channel link is paid; platform account/session original Instagram reel is throttled and photographed SKU/serial, independent legal ownership and creator-to-product correspondence remain unpaid"

wongPatentStarDesignClaim : ClaimBound
wongPatentStarDesignClaim = mkBound
  "Wong 2019 published application describes audio-driven star-like copper winding with one 14-point implementation, not identical to marketed 24-point Starship"
  wongStarAmplifierPatent
  "US20190269877A1 detailed description FIG. 1 with 14 radial sleeves and FIG. 5 amplifier"
  wongPublishedPatentRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "specific lineage/licence, original design equivalence, patented ion assertions and medical effects unverified"

rodinAttributedSocialCaption : ClaimBound
rodinAttributedSocialCaption = mkBound
  "Pictame reports a @crystal_pyramids96 post explicitly saying 'DIY Starship Rodin Coil', naming Red Rock and Dark Knight variants and a build course"
  rodinSocialRelay
  "Rodin Coil Sacred Geometry discovery, @crystal_pyramids96 preview"
  rodinSocialMirrorRoot
  Diligence.contextualEvidence
  attributedAuthorReport
  "aggregator copy not original native reel; exact creator account-to-domain owner relationship and transcript/version unresolved"

itorusRodinSocialCaption : ClaimBound
itorusRodinSocialCaption = mkBound
  "Same social index attributes to @ipyramids an explanation that identifies Marco Rodin and Randy Powell in the Rodin/Vortex Based Mathematics lineage"
  rodinSocialRelay
  "Rodin Coil Sacred Geometry discovery, @ipyramids preview"
  rodinSocialMirrorRoot
  Diligence.contextualEvidence
  attributedAuthorReport
  "third-party excerpt only, not independently inspected original attributed creator caption or validation of described mathematical energy theory"

zeroPointDirectoryName : ClaimBound
zeroPointDirectoryName = mkBound
  "Store directory associates crystalpyramids96.com with Zero Point Tech and enumerates 24-point Starship/Rodin products"
  merchantStoreDirectory
  "Zero Point Tech store listing, General Information and Products for Sale"
  merchantDirectoryRoot
  Diligence.contextualEvidence
  attributedAuthorReport
  "identity of Shopify store is independently listed; same-name Instagram owner and product-to-screenshot identity need actual outbound link, purchase SKU or creator confirmation"

openhandFiveDTorusSource : ClaimBound
openhandFiveDTorusSource = mkBound
  "Openhand (7 September 2026) defines 5D creation through a Torus/Flower of Life 'singularity' and explicitly says mere oneness/love may be 4D, not 5D"
  openhand2026FiveD
  "What Does It Actually Mean To Be Creating From 5D Consciousness? sections Moving Beyond Relativity, Multidimensional Flow"
  openhandAuthorRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "spiritual definition by a specific author only; no agreed operational scale, no field frequency, and no identity with hoe_math stage 5 or physics spatial dimension"

openhandRealitySplitClaim : ClaimBound
openhandRealitySplitClaim = mkBound
  "Openhand (19 October 2026) claims a planetary 3D/5D reality split and accelerating toroidal energies involving alleged electromagnetic suppression"
  openhand2026RealitySplit
  "3D/5D Reality Split post dated 19 October 2026, body and 19/10 shift update"
  openhandAuthorRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "same Openhand authorial origin, not independently verified geology, magnetometry, extraterrestrial intervention or physically shifting reality"

nondualStateTraitMeasurement : ClaimBound
nondualStateTraitMeasurement = mkBound
  "Hanley, Nakamura and Garland distinguish self-reported nondual *state* and *trait* questionnaires"
  hanleyNADA2018
  "Psychological Assessment 2018 abstract and methods; NADA-S and NADA-T validation"
  hanleyPsychometricsRoot
  Diligence.primaryProposition
  scopedValidatedSelfReport
  "scope-valid administration, longitudinal and condition-specific validation before a torus-device experiment; self-report alone never establishes a new physical dimension"

mysticalFourFactorReport : ClaimBound
mysticalFourFactorReport = mkBound
  "MacLean et al. describe mystical unity, positive mood, transcendence of time/space and ineffability as four self-report factors of MEQ30"
  macleanMEQ2012
  "2012 original abstract/results; 1602 exploratory plus 440 confirmatory samples"
  macleanPsychometricsRoot
  Diligence.primaryProposition
  scopedValidatedSelfReport
  "originally retrospective psilocybin reports; measurement invariance in meditation/non-drug/PEMF contexts unestablished"

egoDissolutionExperienceReport : ClaimBound
egoDissolutionExperienceReport = mkBound
  "Nour et al. present an 8-item report instrument for ego-dissolution separable from ego-inflation"
  nourEDI2016
  "Frontiers in Human Neuroscience 2016 article, abstract and factor-analysis table"
  nourPsychometricsRoot
  Diligence.primaryProposition
  scopedValidatedSelfReport
  "does not establish lasting trait, paranormal causal mechanism or clinical outcome"

psychometricFiveDNotSpiritualFiveD : ClaimBound
psychometricFiveDNotSpiritualFiveD = mkBound
  "5D-ASC's five factor coordinates include oceanic boundlessness, anxious ego dissolution, visionary restructuring, auditory alterations and reduced vigilance"
  kervadecFiveDASC2026
  "2026 French 5D-ASC validation introduction and abstract, 777 naturalistic retrospective respondents"
  kervadecAscValidationRoot
  Diligence.primaryProposition
  scopedValidatedSelfReport
  "5D names scale structure only; 11-subscale fit slightly below standard CFI cutoffs; cannot transfer to spiritual five-dimensional reality or electrotherapy efficacy"

ascModelRevision : ClaimBound
ascModelRevision = mkBound
  "Stocker et al. reconsider 5D-ASC and 11-ASC dimensional structure, proposing a revised three-domain positive/distressing/perceptual model"
  stockerASCRevision2026
  "Journal of Psychopharmacology 2026, abstract and methods: 901 questionnaires, 398 people, 16 trials"
  stockerAscRevisionRoot
  Diligence.primaryProposition
  scopedValidatedSelfReport
  "different research group and independent dataset, but same measure family; not proof that any psychometric factor is a fundamental dimension of space"

heartmathDistinguishedFromHoeMath : ClaimBound
heartmathDistinguishedFromHoeMath = mkBound
  "HeartMath Institute's web page discusses physical heart fields and speculative interpersonal energetic communication, separate from hoe_math's developmental Levels teaching"
  heartmathEnergeticCommunication
  "Energetic Communication webpage, electric/magnetic fields and energetic communication sections"
  heartmathInstituteRoot
  Diligence.contextualEvidence
  attributedAuthorReport
  "physiological field instrumentation and actual interpersonal causal effect require independent controls; this does not validate 5D or stage labels"

shupakShamScope : ClaimBound
shupakShamScope = mkBound
  "Shupak et al. report a randomized, double-blind clinical PEMF comparison using a physically silent/no-vibration device and sham"
  shupakShamClinical2006
  "2006 publication Methods, active/sham controls; PubMed 16770449"
  shupakClinicalAuthorRoot
  Diligence.primaryProposition
  externallyDescribedApparatus
  "apparatus-specific masking precedent, not a demonstrated sham for a loud vibration-producing Starship coil; pain/anxiety in limited clinical populations cannot become validated 5D-consciousness efficacy"

duShamDesignProposal : ClaimBound
duShamDesignProposal = mkBound
  "Du et al. propose that their sham PEMF device match active heat, vibration, light and interaction while differing in actual EM exposure"
  duAssessorBlindedProtocol2026
  "2026 study protocol Methods and Abstract, active versus sham handling and detector audit"
  duProtocolAuthorRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "PROTOCOL ONLY, no completed outcome; no causal efficacy or successfully masked experiment has been established by this paper"

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
-- The exact 2024 numbered references and current-field triplet are
-- publication statements, not independent data-custody evidence.
------------------------------------------------------------------------

croftOriginalGuide2003Claim : ClaimBound
croftOriginalGuide2003Claim = mkBound
  "On 26 January 2003 Don Croft referred readers to cloud-busters.com for Mobius winding instructions, and named multiple contemporary builder contributors"
  croftPowerWand2003
  "The PowerWand, January 26 2003: item 4 Mobius Coil, introductory thanks, paragraph naming Mark Hooten"
  croftAuthorRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "archived original guide version and author, original Gentry Smith and Patrick Flanagan authored instruction relationship unverified"

croftAugustNoPublishedGuideClaim : ClaimBound
croftAugustNoPublishedGuideClaim = mkBound
  "Don Croft's 15 August 2002 article says Mobius winding instructions would not be made public, before his dated January 2003 external guide referral"
  croftBigSecret2002
  "The Big Secret, August 15 2002, opening paragraph on withholding coil plans"
  croftAuthorRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "same winding instructions, original disclosure circumstances, contemporaneous native-host versions unavailable"

saikiaStudySpecificClaim : ClaimBound
saikiaStudySpecificClaim = mkBound
  "Original Saikia et al 2019 ACS abstract reports electric/magnetic fields on amyloid peptide and electric-field-treated in vitro toxicity, not an identified Rodin versus Helmholtz 60 percent test"
  saikiaAmyloid2019
  "Original ACS publisher abstract, DOI 10.1021/acschemneuro.8b00490"
  saikia2019ResearchRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "full paywalled article and exact specific coil comparator remain uninspected; cannot universally exclude a full-text comparison"

perez2013TableClaim : ClaimBound
perez2013TableClaim = mkBound
  "Pérez et al 2013 original Table I records three exact current/magnetic-field pairs also present in 2024 Table II"
  perezRodinRSI2013
  "Review of Scientific Instruments 094701-2 Table I at 1.60, 1.25 and 0.60 A"
  guanajuatoRodinResearchRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "source timestamps, original sensor logs and cross-paper reuse provenance unavailable"

ramirez2024ReusedNumbersQuestion : ClaimBound
ramirez2024ReusedNumbersQuestion = mkBound
  "2024 Ramirez-Galindo Table II repeats 2013 experimental B values 4.13, 3.05, 1.16 mT at currents 1.60, 1.25, 0.60 A despite different theoretical values"
  ramirezRodinRMF2024
  "Original published journal PDF p5 Table II, compared with Pérez et al 2013 p094701-2 Table I"
  guanajuatoRodinResearchRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "shared data or independently reacquired unknown; repeated rounded numbers do not establish improper publication conduct"

ramirez2024Ref24Claim : ClaimBound
ramirez2024Ref24Claim = mkBound
  "2024 Rodin paper Discussion attributes a claimed up-to-60-percent Rodin/Helmholtz advantage to numbered reference 24, actually Saikia et al 2019 ACS electric-field amyloid study"
  ramirezRodinRMF2024
  "Published PDF p5 Discussion and p7 reference 24; Saikia original ACS abstract"
  guanajuatoRodinResearchRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "full Saikia original article/any matched comparator and 60-percent source not identified; no inference of intentional miscitation"

ramirez2024Ref12Claim : ClaimBound
ramirez2024Ref12Claim = mkBound
  "2024 paper intro invokes human lymphocyte claim as numbered reference 12, but bibliography 12 is F. P. Perez 2008 heat-shock paper not H. Pérez 2013 RSI Rodin lymphocyte source"
  ramirezRodinRMF2024
  "Original journal PDF p1 Introduction and p6 numbered reference 12, independently checked original 2013 and 2008 article identifiers"
  guanajuatoRodinResearchRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "true author intent and original 2008 full method details not verified; do not infer deliberate omission"

-- Published rounded field values are a lossy observation of raw values.
-- Identical tables cannot select same versus different measurement sessions.
-- This is a source-specific carrier-boundary, not a new experimental result.
rodinRoundedTableDoesNotProveRawIdentity : ClaimBound
rodinRoundedTableDoesNotProveRawIdentity = mkBound
  "2013 Perez Table I and 2024 Ramirez-Galindo Table II agree on three printed two-decimal B values; distinct latent measurement histories can round to those same fields"
  ramirezRodinRMF2024
  "2024 printed Table II three experimental current-field rows; 2013 original Table I; exact rational synthetic collision under stipulated rounding in existing check_rodin_citation_independence_cut.py"
  guanajuatoRodinResearchRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "original unrounded data, coil and sensor serials, instrument calibration, session timestamps, raw files and acquisition frequency of 2024 Table II are not source-joined"

------------------------------------------------------------------------
-- Cloudbusting source-specific propositions. These are original authors'
-- declarations or custody/critical-source observations, never causal proofs.
------------------------------------------------------------------------

reich1953EventProtocolClaim : ClaimBound
reich1953EventProtocolClaim = mkBound
  "Reich says 6 July 1953 ten-tube water-cable drawing ended 11:52 and rain started about 22:00, explicitly with a west-origin weather front"
  reichCoreEllsworth1954
  "CORE OROP Ellsworth digital PDF p57 and p59 (images inspected), protocol reportedly written 8 July 1953"
  reichOriginalAuthorRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "source-independent contemporaneous rainfall map and counterfactual device-caused-front mechanism absent"

reichCloudArchiveCustodyClaim : ClaimBound
reichCloudArchiveCustodyClaim = mkBound
  "Reich Infant Trust Box 24/25 original finding aid lists original cloudbuster instructions, 1953 OROP Ellsworth and 1953 Bangor Daily News clipping"
  reichCloudArchiveIndex
  "Index of Wilhelm Reich Archives original PDF pp85-86; listed item pages NOT read"
  reichMuseumRoot
  Diligence.primaryProposition
  institutionalHistoricalInterpretation
  "catalogue listing is not the item contents or independent meteorological certification"

hamblingModernObjectClaim : ClaimBound
hamblingModernObjectClaim = mkBound
  "David Hambling 2011 reports old Reich water pipes and a later six-pipe-like quartz bucket device claimed to operate without a human"
  hamblingWeatherwatch2011
  "Guardian Weatherwatch 6 July EDT / 7 July AEST 2011 paragraphs on original and later apparatus"
  guardianHamblingRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "actual maker/source of modern generic device, safety comparison and weather causal demonstration missing"

redditMindCloudIntentionClaim : ClaimBound
redditMindCloudIntentionClaim = mkBound
  "2023 Reddit original OP describes mentally focusing on a cloud; diverse commenters credit 1977 Bach, 1976 Constable and 1998 Slade"
  kiddexRedditMind2023
  "u/Kiddex77 original OP and separate named Reddit users in user-supplied full thread"
  redditKiddexForumRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "no independent physical cloud effect, no controlled causal demonstration or direct person-to-person inventorship"

bachOriginalFictionCloudClaim : ClaimBound
bachOriginalFictionCloudClaim = mkBound
  "Bach 1977 Illusions is fiction with a mental cloud-vaporising teacher/student narrative cited by later Reddit readers"
  bachIllusions1977
  "Original 1977 book copyright and later edition summary; specific teacher/student episode described by Reddit readers"
  bachFictionRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "fiction is not laboratory evidence or direct Slade original author copying"

constableBookClaim : ClaimBound
constableBookClaim = mkBound
  "Original 1976 Constable Cosmic Pulse of Life book is a named Reddit reading influence and is discussed by contemporary 1977 reviewer in relation to Reich"
  constableCosmicPulse1976
  "National Library of New Zealand original bibliographic catalogue 1976/77; book content unread"
  constableBookRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "specific original page of mental-vaporisation method and genuine weather effects not verified"

sladeMindVisualisationClaim : ClaimBound
sladeMindVisualisationClaim = mkBound
  "Neil Slade first-person site self-dates 1998 and teaches no-apparatus mental cloud visualisation while asserting dormant brain/amygdala powers"
  sladeMindCloud1998
  "Original neilslade.com/cloud.html main article and later 2007 self-reported reader testimonies"
  sladePractitionerRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "neural mediation and anomalous meteorological causality wholly unverified"

croftModernPipeSelfAttributionClaim : ClaimBound
croftModernPipeSelfAttributionClaim = mkBound
  "Croft original claimed modern Chembuster is resin-based portable variant of Reich water-tube historical cloudbuster"
  croftMoonbustingEarly2002
  "Don Croft Moonbusting Part 2 indexed original-attributed text, date of entire page and full HTML unpaid"
  croftAuthorRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "actual inherited engineering pathway and 150-mile atmospheric effect not demonstrated"

adachiCommercialChembusterClaim : ClaimBound
adachiCommercialChembusterClaim = mkBound
  "Adachi continuously updated product index describes Croft-associated six-pipe metal-resin-crystal Chembuster and weather marketing"
  adachiEditedChembusterIndex
  "Orgone generator index, editor and seller 2002-2011 page, specific 2011 changed prices"
  adachiPublisherRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "any claimed physical benefit or exact 2002 invention date cannot follow from a revised 2011 sales page"

wmoCausalLimitsClaim : ClaimBound
wmoCausalLimitsClaim = mkBound
  "2025 WMO statement limits evidence to some specified physical seeding regimes and cautions against claims of large-scale weather creation"
  wmoWeatherModification2025
  "WMO institutional weather modification fact sheet 14 June 2025, source scope through June 2024"
  wmoInstitutionRoot
  Diligence.primaryProposition
  experimentalMechanismElsewhere
  "statement not a direct instrument-specific trial disproving or proving 1953 Reich cloudbuster or mind-only cloud influence"

bushPeterOriginalReadingClaim : ClaimBound
bushPeterOriginalReadingClaim = mkBound
  "Kate Bush 1985 original artist account explicitly credits Peter Reich's 1973 memoir A Book of Dreams as creative source for Cloudbusting"
  bushCloudbusting1985
  "Kate Bush Club 1985 first-person words as quoted by Dazed 2015, original issue uninspected"
  kateBushArtistRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "creative source attribution cannot certify Reich meteorology or song/movie events"

------------------------------------------------------------------------
-- First-party weather readings independent of Reich's weather story:
-- a small exact fixture for the *published historical dataset only*.
------------------------------------------------------------------------

record HistoricStationPrecipitation : Set where
  constructor station-precipitation
  field
    evidenceSource : Source.AttributedSource
    stationId : String
    observedYear observedMonth observedDay : ℕ
    tenthsMillimetre : ℕ
open HistoricStationPrecipitation public

bangorJuly5 : HistoricStationPrecipitation
bangorJuly5 = station-precipitation noaaBangorGHCN1953 "USW00014606" 1953 7 5 0

bangorJuly6 : HistoricStationPrecipitation
bangorJuly6 = station-precipitation noaaBangorGHCN1953 "USW00014606" 1953 7 6 66

bangorJuly7 : HistoricStationPrecipitation
bangorJuly7 = station-precipitation noaaBangorGHCN1953 "USW00014606" 1953 7 7 193

bangorJuly8 : HistoricStationPrecipitation
bangorJuly8 = station-precipitation noaaBangorGHCN1953 "USW00014606" 1953 7 8 46

bangorJuly9 : HistoricStationPrecipitation
bangorJuly9 = station-precipitation noaaBangorGHCN1953 "USW00014606" 1953 7 9 74

-- Exact 1953 published station-month arithmetic, not a statement about
-- 1953 gauge observation-day cutoff or rainfall at Reich's apparatus.
barHarborJuly5 : HistoricStationPrecipitation
barHarborJuly5 = station-precipitation noaaBarHarborGHCN1953 "USC00170371" 1953 7 5 0

barHarborJuly6 : HistoricStationPrecipitation
barHarborJuly6 = station-precipitation noaaBarHarborGHCN1953 "USC00170371" 1953 7 6 0

barHarborJuly7 : HistoricStationPrecipitation
barHarborJuly7 = station-precipitation noaaBarHarborGHCN1953 "USC00170371" 1953 7 7 130

barHarborJuly8 : HistoricStationPrecipitation
barHarborJuly8 = station-precipitation noaaBarHarborGHCN1953 "USC00170371" 1953 7 8 0

barHarborJuly9 : HistoricStationPrecipitation
barHarborJuly9 = station-precipitation noaaBarHarborGHCN1953 "USC00170371" 1953 7 9 10

barHarborJuly6Through8TotalTenthsMm :
  tenthsMillimetre barHarborJuly6 +
  tenthsMillimetre barHarborJuly7 +
  tenthsMillimetre barHarborJuly8 ≡ 130
barHarborJuly6Through8TotalTenthsMm = refl

bangorJuly6Through8TotalTenthsMm :
  tenthsMillimetre bangorJuly6 +
  tenthsMillimetre bangorJuly7 +
  tenthsMillimetre bangorJuly8 ≡ 305
bangorJuly6Through8TotalTenthsMm = refl

noaaBangorRainSourceClaim : ClaimBound
noaaBangorRainSourceClaim = mkBound
  "Original NOAA daily Bangor Maine station says July 6 PRCP 66, July 7 PRCP 193, July 8 PRCP 46 tenths-mm"
  noaaBangorGHCN1953
  "USW00014606195307PRCP line, days 6, 7 and 8, values from fixed-width 8-char GHCN fields"
  noaaBangorWeatherRoot
  Diligence.primaryProposition
  originalRegionalWeatherMeasurement
  "no station gauge at the claimed Graham Lake Dam draw point, no hourly Ellsworth rain onset or force/causal comparison"

noaaBangorStationIdentityClaim : ClaimBound
noaaBangorStationIdentityClaim = mkBound
  "NOAA GHCND USW00014606 is Bangor International Airport Maine, not Ellsworth Kansas"
  noaaBangorStationMetadata
  "NCEI station details: Bangor Maine, 44.79791 north 68.81852 west, daily record starts Jan 1953"
  noaaBangorWeatherRoot
  Diligence.primaryProposition
  institutionalHistoricalInterpretation
  "same-agency metadata does not count as second original independent gauge"

-- The root below tracks original GHCN custodial provenance; the
-- stations are distinct measurement units, as their exact IDs show.
noaaBarHarborRainSourceClaim : ClaimBound
noaaBarHarborRainSourceClaim = mkBound
  "Original NOAA Bar Harbor 3 NW Maine station says 6 July 0, 7 July 130, 8 July 0 tenths-mm"
  noaaBarHarborGHCN1953
  "USC00170371195307PRCP 269-column web-readable original record; 26 October 2026 transcript"
  noaaBangorWeatherRoot
  Diligence.primaryProposition
  originalRegionalWeatherMeasurement
  "different station, no exact Ellsworth 22h reading, historical daily gauge cutoff or rainfall-causation evidence"

noaaBarHarborStationIdentityClaim : ClaimBound
noaaBarHarborStationIdentityClaim = mkBound
  "USC00170371 is Bar Harbor 3 NW Maine with 1893–1982 observation period"
  noaaBarHarborStationMetadata
  "NCEI station identity 44.41667 north, 68.25 west, 34.1m, 1953 covered"
  noaaBangorWeatherRoot
  Diligence.primaryProposition
  institutionalHistoricalInterpretation
  "shared NOAA origin and station location metadata do not prove historical local 22:00 rain or non-Maxwell effects"

ellsworthJuly8PressClaim : ClaimBound
ellsworthJuly8PressClaim = mkBound
  "Earlier 8 July Ellsworth American anonymous rainmaker headline recounts the July 6 Orgone Institute intervention"
  ellsworthAmericanJuly1953
  "Clipping reproduced in Reich 1954 CORE documentary record; exact newspaper original issue not obtained"
  ellsworthAmericanPressRoot
  Diligence.primaryProposition
  attributedAuthorReport
  "anonymous reporter source independence from Orgone Institute and objective rain causation both unresolved"

kansasEllsworthMisidentityClaim : ClaimBound
kansasEllsworthMisidentityClaim = mkBound
  "The historical 1953 weather page with URL slug cities/ellsworth is explicitly for Ellsworth Kansas, not Maine"
  ellsworthKansasFalseWeatherJoin
  "ExtremeWeatherWatch page opening location designation Ellsworth Kansas"
  kansasWeatherPortalRoot
  Diligence.primaryProposition
  institutionalHistoricalInterpretation
  "no geographic validity as evidence for original 1953 Maine operation"

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
  multiFeatureCatalogueMatchUnconfirmed : RelationClass

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

------------------------------------------------------------------------
-- Phase-1 source-critical joins: every relation is non-promoting.
------------------------------------------------------------------------

croftJanGuideNotGentryProof : BoundedRelation
croftJanGuideNotGentryProof = bounded-relation
  "Croft January 2003 original named website guide"
  "Gentry Smith / Patrick Flanagan alleged earlier original winding plan"
  contemporarySelfAttribution croftOriginalGuide2003Claim false refl false refl

croftInstructionPublicationDatesDistinct : BoundedRelation
croftInstructionPublicationDatesDistinct = bounded-relation
  "Croft August 2002 no-guide publication claim"
  "Croft January 2003 external winding-guide citation"
  documentaryDistinction croftAugustNoPublishedGuideClaim false refl false refl

ramirezRef24NotValidatedCoilComparison : BoundedRelation
ramirezRef24NotValidatedCoilComparison = bounded-relation
  "Ramírez-Galindo et al 2024 claimed Rodin-vs-Helmholtz 60-percent effect with ref24"
  "Saikia et al 2019 in vitro electric-field amyloid study, full text uninspected"
  documentaryDistinction ramirez2024Ref24Claim false refl false refl

ramirezRef12NotPerez2013 : BoundedRelation
ramirezRef12NotPerez2013 = bounded-relation
  "2024 Introduction human lymphocyte claim referenced as 12"
  "Bibliography 12 F. P. Perez 2008 not 2013 H. Pérez Rodin paper"
  documentaryDistinction ramirez2024Ref12Claim false refl false refl

perezRamirezTableOverlapUnresolved : BoundedRelation
perezRamirezTableOverlapUnresolved = bounded-relation
  "2013 Pérez RSI measured current-to-field three-point source table"
  "2024 Ramírez-Galindo RMF same three rounded measured values"
  documentaryDistinction ramirez2024ReusedNumbersQuestion false refl false refl

------------------------------------------------------------------------
-- Original cloudbusting term has three unlike methods. Source link/credit
-- is not apparatus equivalence or physical effect; each pair remains bounded.
------------------------------------------------------------------------

reichReportHasNaturalWeatherFront : BoundedRelation
reichReportHasNaturalWeatherFront = bounded-relation
  "Reich 1953 reported cloudbuster use and subsequent rain"
  "Reich's same report explicitly records a western weather front"
  documentaryDistinction reich1953EventProtocolClaim false refl false refl

reichArchiveCatalogDoesNotProveRain : BoundedRelation
reichArchiveCatalogDoesNotProveRain = bounded-relation
  "Reich Museum Box 24/25 source catalogue"
  "Reich device-to-weather-effect hypothesis"
  documentaryDistinction reichCloudArchiveCustodyClaim false refl false refl

guardianRetellingNotSecond1953Trial : BoundedRelation
guardianRetellingNotSecond1953Trial = bounded-relation
  "David Hambling 2011 original journalist story"
  "Wilhelm Reich original 1953 Ellsworth account"
  documentaryDistinction hamblingModernObjectClaim false refl false refl

guardianModernBucketNotReichSameApparatus : BoundedRelation
guardianModernBucketNotReichSameApparatus = bounded-relation
  "2011 reported resin-and-crystal modern Chembuster"
  "1953 original Reich hollow-tubes-and-water apparatus"
  documentaryDistinction hamblingModernObjectClaim false refl false refl

croftModernChembusterNotReichMethod : BoundedRelation
croftModernChembusterNotReichMethod = bounded-relation
  "Croft resin modern Chembuster"
  "Reich original water-connected cloudbuster"
  documentaryDistinction croftModernPipeSelfAttributionClaim false refl false refl

adachiSellerNotIndependentWeatherObservation : BoundedRelation
adachiSellerNotIndependentWeatherObservation = bounded-relation
  "Ken Adachi product catalogue and descriptions"
  "Don Croft original practitioner claimed Chembuster effect"
  commercialSpecificationOnly adachiCommercialChembusterClaim false refl false refl

redditMindCloudNotReichPipeMachine : BoundedRelation
redditMindCloudNotReichPipeMachine = bounded-relation
  "Mental cloud visualisation in u/Kiddex77 post"
  "Physical tube-and-water Reich 1953 device"
  documentaryDistinction redditMindCloudIntentionClaim false refl false refl

redditBachReadingNotWeatherProof : BoundedRelation
redditBachReadingNotWeatherProof = bounded-relation
  "Reddit users' direct credits to Bach 1977 novel"
  "Bach fictional cloud-vaporising lesson"
  explicitlyAttributedReading redditMindCloudIntentionClaim false refl false refl

redditConstableReadingNotWeatherProof : BoundedRelation
redditConstableReadingNotWeatherProof = bounded-relation
  "Reddit user credits Trevor James Constable 1976 original"
  "Constable original speculative book, full text unread"
  explicitlyAttributedReading redditMindCloudIntentionClaim false refl false refl

redditSladeReadingNotWeatherProof : BoundedRelation
redditSladeReadingNotWeatherProof = bounded-relation
  "Reddit user credits Neil Slade mental cloud technique"
  "Neil Slade 1998 original practitioner claim"
  explicitlyAttributedReading redditMindCloudIntentionClaim false refl false refl

bachAndSladeNotDirectInventionChain : BoundedRelation
bachAndSladeNotDirectInventionChain = bounded-relation
  "Bach 1977 fictional no-apparatus cloud method"
  "Slade 1998 practitioner no-apparatus method"
  thematicResemblanceOnly bachOriginalFictionCloudClaim false refl false refl

bushOriginalPeterMemoirAttribution : BoundedRelation
bushOriginalPeterMemoirAttribution = bounded-relation
  "Kate Bush 1985 Cloudbusting source statement"
  "Peter Reich 1973 A Book of Dreams"
  explicitlyAttributedReading bushPeterOriginalReadingClaim false refl false refl

wmoStatementCannotProveReichMechanism : BoundedRelation
wmoStatementCannotProveReichMechanism = bounded-relation
  "WMO 2025 source-specific real weather-modification methods"
  "Reich 1953 original orgone-rain causality claim"
  documentaryDistinction wmoCausalLimitsClaim false refl false refl

rvmlPromotionalReichBuildNotVerifiedMechanism : BoundedRelation
rvmlPromotionalReichBuildNotVerifiedMechanism = bounded-relation
  "RVML publicity naming Gentry Smith as a Reich Cloudbuster builder"
  "Reich 1953 original water-connected apparatus and claimed rainmaking"
  documentaryDistinction rvmlGentryReichCloudbusterPublicity false refl false refl

rvmlFlanaganNamedTopicNotOriginalCoilHandoff : BoundedRelation
rvmlFlanaganNamedTopicNotOriginalCoilHandoff = bounded-relation
  "RVML advertised Pat Flanagan's Electronic Bliss Device talk topic"
  "Croft first-person 1999 Gentry/Flanagan Mobius instructions claim"
  documentaryDistinction rvmlGentryFlanaganAdvertisedTopic false refl false refl

windingGuideDomainNotRainMachineProof : BoundedRelation
windingGuideDomainNotRainMachineProof = bounded-relation
  "Croft 2003 cloud-busters.com Mobius-winding referral"
  "Reich 1953 cloudbuster or modern Chembuster sky effect"
  documentaryDistinction croftOriginalGuide2003Claim false refl false refl

------------------------------------------------------------------------
-- Original atmospheric-data joins remain *observation only*; place and
-- publication dependency are required for a legitimate case comparison.
------------------------------------------------------------------------

bangorOriginalObservedRainNotRainmakingProof : BoundedRelation
bangorOriginalObservedRainNotRainmakingProof = bounded-relation
  "NOAA original Bangor daily precipitation July 1953"
  "Reich claimed 6 July 1953 Ellsworth device-caused rain"
  documentaryDistinction noaaBangorRainSourceClaim false refl false refl

noaaStationIdentityNotTwoWeatherExperiments : BoundedRelation
noaaStationIdentityNotTwoWeatherExperiments = bounded-relation
  "NOAA Bangor GHCN daily rain source"
  "NOAA metadata for the same Bangor station USW00014606"
  documentaryDistinction noaaBangorStationIdentityClaim false refl false refl

ellsworthAmericanEarlierButNotIndependentWeatherTrial : BoundedRelation
ellsworthAmericanEarlierButNotIndependentWeatherTrial = bounded-relation
  "8 July Ellsworth American newspaper report, unnamed writer"
  "24 July Bangor Daily News rainmaker report / Reich 1953 event"
  documentaryDistinction ellsworthJuly8PressClaim false refl false refl

kansasWeatherIsNotMaineReichEvent : BoundedRelation
kansasWeatherIsNotMaineReichEvent = bounded-relation
  "Ellsworth Kansas third-party 1953 weather"
  "Ellsworth Maine 1953 cloudbuster operation"
  documentaryDistinction kansasEllsworthMisidentityClaim false refl false refl

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

candidateCopperStarIdentification : BoundedRelation
candidateCopperStarIdentification = bounded-relation
  "Instagram @crystal_pyramids96 copper-star and centre-ball screenshots 1000018562-8564"
  "Zero Point Tech indexed 24-point Starship Rodin/Dark Knight coil with dancing neodymium sphere"
  multiFeatureCatalogueMatchUnconfirmed zeroPointStarshipSphereClaim false refl false refl

zeroPointMakerVersionsAreDistinct : BoundedRelation
zeroPointMakerVersionsAreDistinct = bounded-relation
  "Zero Point Tech indexed Dark Knight 24-point 50-W/sphere variant"
  "Zero Point Tech live GoldenEye 24-point 400-W advertised variant"
  documentaryDistinction zeroPointGoldeneyeMakerClaim false refl false refl

zeroPointSiteExplicitlyLinksAccount : BoundedRelation
zeroPointSiteExplicitlyLinksAccount = bounded-relation
  "Zero Point Tech original illustrated product webpage"
  "Instagram @crystal_pyramids96 original screenshot posting account"
  contemporarySelfAttribution zeroPointWebsiteLinksOriginalHandle false refl false refl

wongPatentIsNotStarshipInheritance : BoundedRelation
wongPatentIsNotStarshipInheritance = bounded-relation
  "Dennis Yat Wong 2019 14-point star coil audio-amplifier application"
  "Zero Point Tech 24-point Starship product family"
  hardwareAnalogyOnly wongPatentStarDesignClaim false refl false refl

rodinNamedBySocialRelay : BoundedRelation
rodinNamedBySocialRelay = bounded-relation
  "indexed @crystal_pyramids96 caption" "DIY Starship Rodin Coil / Dark Knight / Red Rock"
  namedSymbolOnly rodinAttributedSocialCaption false refl false refl

zeroPointSameMakerMiniComparator : BoundedRelation
zeroPointSameMakerMiniComparator = bounded-relation
  "Zero Point Tech 24-point Starship seller listing" "Zero Point Tech Mini moving magnet explanation"
  hardwareAnalogyOnly zeroPointMiniMagnetResponse false refl false refl

openhandTorusFiveDIsSpecificBeliefSource : BoundedRelation
openhandTorusFiveDIsSpecificBeliefSource = bounded-relation
  "Openhand 2026 spiritual 5D / torus singularity" "iTorus app marketing of 5D consciousness"
  thematicResemblanceOnly openhandFiveDTorusSource false refl false refl

openhandClaimOfRealitySplit : BoundedRelation
openhandClaimOfRealitySplit = bounded-relation
  "Openhand 2026 toroidal planetary flow report" "physical geomagnetic/clinical proposition"
  thematicResemblanceOnly openhandRealitySplitClaim false refl false refl

psychometricsNotSpiritualDimension : BoundedRelation
psychometricsNotSpiritualDimension = bounded-relation
  "5D-ASC psychometric five-factor name" "Openhand five-dimensional spiritual consciousness"
  documentaryDistinction psychometricFiveDNotSpiritualFiveD false refl false refl

nondualIsReportNotAppEffect : BoundedRelation
nondualIsReportNotAppEffect = bounded-relation
  "NADA-S or NADA-T reported experience" "iTorus 5D consciousness marketing"
  hardwareAnalogyOnly nondualStateTraitMeasurement false refl false refl

heartmathIsNotHoeMath : BoundedRelation
heartmathIsNotHoeMath = bounded-relation
  "HeartMath Institute claimed interpersonal heart fields" "hoe_math developmental Levels presentation"
  documentaryDistinction heartmathDistinguishedFromHoeMath false refl false refl

silentShamDoesNotCertifyLoudCoil : BoundedRelation
silentShamDoesNotCertifyLoudCoil = bounded-relation
  "2006 silent PEMF double-blind device precedent" "audibly vibrating Starship/Rodin coil"
  historicalMechanismPrecedentOnly shupakShamScope false refl false refl

futureShamProposalDoesNotGiveObservedTrial : BoundedRelation
futureShamProposalDoesNotGiveObservedTrial = bounded-relation
  "Du et al. 2026 planned matched PEMF sham" "completed iTorus sham-validated study"
  thematicResemblanceOnly duShamDesignProposal false refl false refl

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
