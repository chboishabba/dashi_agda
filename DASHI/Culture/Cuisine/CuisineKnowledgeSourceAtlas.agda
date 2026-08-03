module DASHI.Culture.Cuisine.CuisineKnowledgeSourceAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Attributed source atlas for situated cuisine, mole, controlled success,
-- and preservation/publication boundaries.
--
-- Exact titles, authors or institutional authors, publication contexts, DOI
-- states and URLs are retained.  Each relationship statement is deliberately
-- narrower than the source itself and imports no theorem or cultural authority.
------------------------------------------------------------------------

wovenPalateArchitectureOfAsh : Source.AttributedSource
wovenPalateArchitectureOfAsh =
  Source.mkNoDOISource
    "Eric Phanngavong"
    "Chile and Spice: Pain and Pleasure, Volume 1, Chapter 5: The Architecture of Ash"
    "The Woven Palate"
    "2026"
    "https://thewovenpalate.substack.com/p/volume-1-chapter-5-the-architecture"
    Source.practitionerSource
    "practitioner narrative and candidate process account for mole, ash, grinding, embodied control, regional variation, and sensory transformation"
    Source.publicAttribution

castilloCisnerosEnMiMeroMole : Source.AttributedSource
castilloCisnerosEnMiMeroMole =
  Source.mkDOISource
    "Maria del Carmen Castillo Cisneros"
    "En mi mero mole: una lectura antropologica de Mole en Chapters of Food"
    "EntreDiversidades 8(1), 164-185"
    "2021"
    "10.31644/ED.V8.N1.2021.A07"
    "https://doi.org/10.31644/ED.V8.N1.2021.A07"
    Source.academicArticleSource
    "ethnographic corrective for ingredient persistence, commensality, textiles, Indigenous life, local history, and anti-fetishisation"
    Source.publicAttribution

hryciukAlquimistaSabores : Source.AttributedSource
hryciukAlquimistaSabores =
  Source.mkDOISource
    "Renata E. Hryciuk"
    "Alquimista de los Sabores: Gastronomic Heritage, Gender, and the Tourist Imaginary in Mexico"
    "Revista del CESLA, International Latin American Studies Review 24, 75-100"
    "2019"
    "10.36551/2081-1160.2019.24.75-100"
    "https://doi.org/10.36551/2081-1160.2019.24.75-100"
    Source.academicArticleSource
    "multi-sited analysis of Abigail Mendoza, gendered culinary celebrity, heritage politics, representation, class conflict, and tourism value capture"
    Source.publicAttribution

hernandezAlbarranCulturaAlimentaria : Source.AttributedSource
hernandezAlbarranCulturaAlimentaria =
  Source.mkNoDOISource
    "Lilia Hernandez Albarran"
    "De cultura alimentaria, cocina tradicional y gastronomia mexicana: Algunas reflexiones"
    "Diario de Campo, cuarta epoca 4, 15-27"
    "2018"
    "https://revistas.inah.gob.mx/index.php/diariodecampo/article/view/13335"
    Source.academicArticleSource
    "critical heritage and biocultural-memory source, including the ethnophagy question"
    Source.publicAttribution

buenahoraExperienciasSilenciadas : Source.AttributedSource
buenahoraExperienciasSilenciadas =
  Source.mkNoDOISource
    "Giobanna Buenahora"
    "Experiencias silenciadas: Breves apuntes sobre la cocina afromexicana"
    "Diario de Campo 4, 74-85"
    "2018"
    "https://revistas.inah.gob.mx/index.php/diariodecampo/article/view/13339"
    Source.academicArticleSource
    "Afro-Mexican women's culinary memory, identity, resistance, and silencing within national gastronomic heritage"
    Source.publicAttribution

pilcherMoleDigitalHistory : Source.AttributedSource
pilcherMoleDigitalHistory =
  Source.mkDOISource
    "Jeffrey M. Pilcher"
    "Mole Poblano: Profile of Taste and Culture in Mexico Through Digital History Analysis"
    "From Garum to Mole: Sauces and Identity in the Western World, chapter 14, pages 251-274"
    "2026"
    "10.1093/9780190622138.003.0014"
    "https://doi.org/10.1093/9780190622138.003.0014"
    Source.academicChapterSource
    "digital historical analysis of changing mole ingredient networks, naming, nationalism, local celebration, and culinary tourism"
    Source.publicAttribution

bakGellerCuevasFoodSovereignty : Source.AttributedSource
bakGellerCuevasFoodSovereignty =
  Source.mkNoDOISource
    "Sarah Bak-Geller and Grecia Cuevas"
    "Manual practico para la soberania alimentaria: Gastronomia, comunidad y resistencia desde Cosoltepec para el mundo"
    "Universidad Nacional Autonoma de Mexico, Instituto de Investigaciones Antropologicas; ISBN 978-607-30-8922-7"
    "2024"
    "https://editorialiia.unam.mx/omp/index.php/publicaciones/catalog/book/manual_soberania_alimentaria"
    Source.academicBookSource
    "community autonomy, reciprocity, collective kitchen labour, justice, and resistance to extractive food systems"
    Source.publicAttribution

kimmererBraidingSweetgrass : Source.AttributedSource
kimmererBraidingSweetgrass =
  Source.mkNoDOISource
    "Robin Wall Kimmerer"
    "Braiding Sweetgrass: Indigenous Wisdom, Scientific Knowledge and the Teachings of Plants"
    "Milkweed Editions"
    "2013"
    "https://milkweed.org/book/braiding-sweetgrass"
    Source.academicBookSource
    "attributed reciprocity and braid/fabric source already represented by DASHI.Interop.SweetgrassCarrierSpine"
    Source.publicAttribution

yunkaportaSandTalk : Source.AttributedSource
yunkaportaSandTalk =
  Source.mkNoDOISource
    "Tyson Yunkaporta"
    "Sand Talk: How Indigenous Thinking Can Save the World"
    "Text Publishing"
    "2019"
    "https://www.textpublishing.com.au/books/sand-talk"
    Source.academicBookSource
    "historical entry point for PatternMind as a situated comparison lens, not a universal Indigenous ontology"
    Source.publicAttribution

unescoTraditionalMexicanCuisine : Source.AttributedSource
unescoTraditionalMexicanCuisine =
  Source.mkNoDOISource
    "UNESCO Intergovernmental Committee for the Safeguarding of the Intangible Cultural Heritage"
    "Traditional Mexican cuisine - ancestral, ongoing community culture, the Michoacan paradigm"
    "Representative List of the Intangible Cultural Heritage of Humanity, element 00400"
    "2010"
    "https://ich.unesco.org/en/RL/00400"
    Source.institutionalSource
    "institutional food-system framing spanning agriculture, processing, utensils, ritual, collective cooking, eating, identity, and transmission"
    Source.publicAttribution

rubinTraditionalCuisineTenYears : Source.AttributedSource
rubinTraditionalCuisineTenYears =
  Source.mkNoDOISource
    "Sol Rubin de la Borbolla"
    "La cocina tradicional de Mexico en la Lista Representativa del Patrimonio Cultural Inmaterial de la Humanidad, 10 anos despues"
    "Hereditas 31, 4-15"
    "2021"
    "https://revistas.inah.gob.mx/index.php/hereditas/article/view/17196"
    Source.academicArticleSource
    "institutional retrospective on inscription, safeguarding, representation, and governance"
    Source.publicAttribution

conabioSIAgroBD : Source.AttributedSource
conabioSIAgroBD =
  Source.mkNoDOISource
    "Comision Nacional para el Conocimiento y Uso de la Biodiversidad"
    "Sistema de Informacion sobre Agrobiodiversidad"
    "CONABIO SIAgroBD"
    "ongoing"
    "https://siagro.conabio.gob.mx/"
    Source.governmentSource
    "agrobiodiversity, milpa, native crops, seed lineages, regional food practices, and cuisine-ecology relationships"
    Source.publicAttribution

mathijssenCulinaryFluidMechanics : Source.AttributedSource
mathijssenCulinaryFluidMechanics =
  Source.mkDOISource
    "Arnold J. T. M. Mathijssen, Maciej Lisicki, Vivek N. Prakash, and Endre J. L. Mossige"
    "Culinary fluid mechanics and other currents in food science"
    "Reviews of Modern Physics 95, 025004"
    "2023"
    "10.1103/RevModPhys.95.025004"
    "https://doi.org/10.1103/RevModPhys.95.025004"
    Source.academicArticleSource
    "multiphase-flow and complex-fluid reference for candidate mole rheology and service stability"
    Source.publicAttribution

guyHardParticleSuspensions : Source.AttributedSource
guyHardParticleSuspensions =
  Source.mkDOISource
    "B. M. Guy, M. Hermes, and W. C. K. Poon"
    "Towards a Unified Description of the Rheology of Hard-Particle Suspensions"
    "Physical Review Letters 115, 088304"
    "2015"
    "10.1103/PhysRevLett.115.088304"
    "https://doi.org/10.1103/PhysRevLett.115.088304"
    Source.academicArticleSource
    "hard-particle suspension reference; it does not establish a measured mole constitutive law"
    Source.publicAttribution

ragouilliauxThixotropicTransition : Source.AttributedSource
ragouilliauxThixotropicTransition =
  Source.mkDOISource
    "A. Ragouilliaux, G. Ovarlez, N. Shahidzadeh-Bonn, B. Herzhaft, T. Palermo, and P. Coussot"
    "Transition from a simple yield-stress fluid to a thixotropic material"
    "Physical Review E 76, 051408"
    "2007"
    "10.1103/PhysRevE.76.051408"
    "https://doi.org/10.1103/PhysRevE.76.051408"
    Source.academicArticleSource
    "particle-loaded emulsion and thixotropy reference; it calibrates vocabulary rather than proving mole stability"
    Source.publicAttribution

dawBatchArrivals : Source.AttributedSource
dawBatchArrivals =
  Source.mkNoDOISource
    "Andrew Daw, Robert C. Hampshire, and Jamol Pender"
    "How to Staff When Customers Arrive in Batches"
    "arXiv:1907.12650"
    "2019"
    "https://arxiv.org/abs/1907.12650"
    Source.academicArticleSource
    "queueing reference for burst demand, staffing pressure, and the bakery controlled-success analogy"
    Source.publicAttribution

euGeographicalIndications : Source.AttributedSource
euGeographicalIndications =
  Source.mkNoDOISource
    "European Commission"
    "Protection of geographical indications in the EU"
    "Your Europe business guidance"
    "ongoing"
    "https://europa.eu/youreurope/business/growing/protecting-intellectual-property/geographical-indications/index_en.htm"
    Source.institutionalSource
    "PDO and PGI designation precedent for name, place, specification, producer class, and conformity control"
    Source.publicAttribution

comiteChampagneGovernance : Source.AttributedSource
comiteChampagneGovernance =
  Source.mkNoDOISource
    "Comite Champagne"
    "The Comite Champagne"
    "Champagne interprofessional governance documentation"
    "ongoing"
    "https://www.champagne.fr/en/find-out-more/champagne-industry/comite-champagne"
    Source.institutionalSource
    "collective governance, traceability, supply coordination, reserves, staged release, and appellation protection precedent"
    Source.publicAttribution

galapagosVisitorSites : Source.AttributedSource
galapagosVisitorSites =
  Source.mkNoDOISource
    "Direccion del Parque Nacional Galapagos"
    "Sitios de Visita"
    "Galapagos National Park visitor-site management"
    "ongoing"
    "https://galapagos.gob.ec/sitios-de-visita/"
    Source.governmentSource
    "authorised visitor sites, permitted activities, reservation, monitoring, and carrying-capacity precedent"
    Source.publicAttribution

antarcticVisitorGuidelines : Source.AttributedSource
antarcticVisitorGuidelines =
  Source.mkNoDOISource
    "Antarctic Treaty Secretariat"
    "General Guidelines for Visitors to the Antarctic"
    "Antarctic Treaty System visitor guidance"
    "ongoing"
    "https://www.ats.aq/e/visitors.html"
    Source.institutionalSource
    "site-sensitive access limits, guide ratios, vessel and landing constraints, and environmental protection precedent"
    Source.publicAttribution

unescoVisitorManagement : Source.AttributedSource
unescoVisitorManagement =
  Source.mkNoDOISource
    "UNESCO World Heritage Centre"
    "Visitor management and carrying capacity"
    "World Heritage policy compendium"
    "ongoing"
    "https://whc.unesco.org/en/compendium/225"
    Source.institutionalSource
    "visitor-management planning and carrying-capacity precedent; not direct authority over community knowledge disclosure"
    Source.publicAttribution

iachrVoluntaryIsolation : Source.AttributedSource
iachrVoluntaryIsolation =
  Source.mkNoDOISource
    "Inter-American Commission on Human Rights"
    "Indigenous Peoples in Voluntary Isolation and Initial Contact in the Americas: Recommendations for the Full Respect of Their Human Rights"
    "Organization of American States, thematic report"
    "2013"
    "https://www.oas.org/en/iachr/indigenous/docs/pdf/report-indigenous-peoples-voluntary-isolation.pdf"
    Source.institutionalSource
    "no-contact and self-determination boundary; scientific interest and public curiosity do not create permission to contact or expose"
    Source.publicAttribution

canonicalCuisineKnowledgeSources : List Source.AttributedSource
canonicalCuisineKnowledgeSources =
  wovenPalateArchitectureOfAsh
  ∷ castilloCisnerosEnMiMeroMole
  ∷ hryciukAlquimistaSabores
  ∷ hernandezAlbarranCulturaAlimentaria
  ∷ buenahoraExperienciasSilenciadas
  ∷ pilcherMoleDigitalHistory
  ∷ bakGellerCuevasFoodSovereignty
  ∷ kimmererBraidingSweetgrass
  ∷ yunkaportaSandTalk
  ∷ unescoTraditionalMexicanCuisine
  ∷ rubinTraditionalCuisineTenYears
  ∷ conabioSIAgroBD
  ∷ mathijssenCulinaryFluidMechanics
  ∷ guyHardParticleSuspensions
  ∷ ragouilliauxThixotropicTransition
  ∷ dawBatchArrivals
  ∷ euGeographicalIndications
  ∷ comiteChampagneGovernance
  ∷ galapagosVisitorSites
  ∷ antarcticVisitorGuidelines
  ∷ unescoVisitorManagement
  ∷ iachrVoluntaryIsolation
  ∷ []

canonicalCuisineKnowledgeSourceCount : Nat
canonicalCuisineKnowledgeSourceCount =
  Source.sourceCount canonicalCuisineKnowledgeSources

canonicalCuisineKnowledgeSourceCountIsTwentyTwo :
  canonicalCuisineKnowledgeSourceCount ≡ 22
canonicalCuisineKnowledgeSourceCountIsTwentyTwo = refl

canonicalCuisineKnowledgeSourceAtlas : Source.AttributedSourceAtlas
canonicalCuisineKnowledgeSourceAtlas =
  Source.mkSourceAtlas
    "situated cuisine and controlled-success source atlas"
    "DASHI.Culture.Cuisine.CuisineKnowledgeSourceAtlas"
    canonicalCuisineKnowledgeSources
    "mole process, ethnography, food systems, Afro-Mexican memory, gender, tourism, agrobiodiversity, material science, burst demand, designation, carrying capacity, preservation, and no-contact boundaries"

canonicalCuisineKnowledgeSourceReceipt : GenericReceipt.GenericReceipt
canonicalCuisineKnowledgeSourceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "situated cuisine source atlas"
    "DASHI.Culture.Cuisine.CuisineKnowledgeSourceAtlas"
    "canonicalCuisineKnowledgeSourceAtlas"
    "attaches author or institutional author, exact title, publication context, DOI state, canonical URL, and bounded formalisation relationship to twenty-two sources"
    "the atlas does not claim source agreement, exhaustive coverage, empirical validation of the candidate models, or cultural, scientific, historical, legal, political, safety, or publication authority"
    "agda -i . DASHI/Culture/Cuisine/CuisineKnowledgeSourceAtlas.agda"
