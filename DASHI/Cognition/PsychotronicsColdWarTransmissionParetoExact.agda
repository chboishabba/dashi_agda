module DASHI.Cognition.PsychotronicsColdWarTransmissionParetoExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Core.SnowballOSINTAcquisitionInvariantExact as OSINT
import DASHI.Core.EmpiricalSourceDiligenceAdmissionExact as Diligence
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.IbrahimSnowballParetoFrontierExact as Pareto
import DASHI.Wikimedia.IbrahimSnowballInvestigativeClaimSourceLineageBidiExact as Investigation

------------------------------------------------------------------------
-- COLD-WAR / NAZI-ERA PSYCHOTRONICS:
-- HISTORICAL TRANSMISSION CONSUMER, NOT ANOTHER SOURCE-TRUTH ONTOLOGY.
--
-- Primary original author / publication / institution / archival custodian
-- must survive a snowball; a mirror or translated catalogue DOES NOT
-- create a separate observation of an allegedly paranormal mechanism.
--
-- Only grounded documentary links are represented as direct edges.
-- No Nazi-to-Soviet, Nazi-to-Croft, Soviet-to-iTorus or Pavlita-to-Croft
-- technology transfer is established by the following data.
------------------------------------------------------------------------

wimmer1940 : Source.AttributedSource
wimmer1940 = Source.mkNoDOISource
  "Josef Wimmer"
  "Assessment of Confiscated Dowsing and Pendulum Literature for Reinhard Heydrich"
  "30 October 1940 German original, Ursinus College Ahnenerbe/Dowsing collection; folder 12, documents 38 and 42; English translation is a separate derivative carrier"
  "1940"
  "https://digitalcommons.ursinus.edu/dowsing/25/"
  Source.archivalSource
  "primary actor's report on classification of nine confiscated texts, dowsing/pendulum science claims and proposed Ahnenerbe oversight; not a physics replication"
  Source.publicAttribution

sievers1940 : Source.AttributedSource
sievers1940 = Source.mkNoDOISource
  "Wolfram Sievers"
  "Letter to Reinhard Heydrich on confiscated dowsing and pendulum literature"
  "20 November 1940 original German letter, Ursinus College collection, folder 12 document 18; summary explicitly refers to Wimmer's assessment"
  "1940"
  "https://digitalcommons.ursinus.edu/dowsing/13/"
  Source.archivalSource
  "direct same-administration documentary reference and proposed research oversight, not operational electromagnetic technology"
  Source.publicAttribution

ostranderSchroeder1970 : Source.AttributedSource
ostranderSchroeder1970 = Source.mkNoDOISource
  "Sheila Ostrander and Lynn Schroeder"
  "Psychic Discoveries Behind the Iron Curtain"
  "Prentice-Hall, Englewood Cliffs, 1970; publisher/year/title corroborated by library catalogue; later 1973 PSI edition distinct from original"
  "1970"
  "https://books.google.com/books/about/Psychic_discoveries_behind_the_Iron_Curt.html?id=Od4vAAAAYAAJ"
  (Source.namedSourceKind "popular-reporting book")
  "original popular-reporting book about Soviet/Czechoslovak paranormal claims and Kirlian/psychotronic topics; original experiments are not supplied by its existence"
  Source.publicAttribution

maireLaMothe1975 : Source.AttributedSource
maireLaMothe1975 = Source.mkNoDOISource
  "Louis F. Maire III and Major J. D. LaMothe, MSC"
  "Soviet and Czechoslovakian Parapsychology Research (U)"
  "DST-1810S-387-75; prepared by U.S. Army Medical Intelligence and Information Agency, Office of the Surgeon General for a DIA task; information cutoff 15 April 1975, published September 1975; 69-page scan via Black Vault"
  "1975"
  "https://www.theblackvault.com/documents/parapsychology/sovczech.pdf"
  Source.governmentSource
  "primary US intelligence authors' analytic account of reported Eastern Bloc psychic/psychotronic work; printed bibliography p.69 item 5 explicitly cites Ostrander/Schroeder 1970; reported claims are not lab confirmation"
  Source.publicAttribution

czechArchive1985 : Source.AttributedSource
czechArchive1985 = Source.mkNoDOISource
  "Security Services Archive, Czech Republic"
  "Psychotronics in the Czechoslovak People's Army"
  "archival-custodian summary of unprocessed collection of Czechoslovak general staff intelligence records; cites 6 September, 24 October and 31 October 1985 documents; original record images not presented on this web page"
  "1985 events; modern undated archival summary"
  "https://www.abscr.cz/en/archivalie/psychotronics-in-the-czechoslovak-peoples-army/"
  Source.archivalSource
  "archivist describes defence-ministry instruction and requests for USSR and GDR military intelligence assistance; requested cooperation does not prove it occurred or yielded effective apparatus"
  Source.publicAttribution

pehekKylerFaust1976 : Source.AttributedSource
pehekKylerFaust1976 = Source.mkDOISource
  "J. O. Pehek; H. J. Kyler; D. L. Faust"
  "Image modulation in corona discharge photography"
  "Science 194(4262), 263-270, published 15 October 1976; PubMed PMID 968480; abstract independently inspected"
  "1976"
  "10.1126/science.968480"
  "https://pubmed.ncbi.nlm.nih.gov/968480/"
  Source.academicArticleSource
  "real high-voltage Kirlian/corona images modulated by sample moisture, voltage waveform, circuit resistance, electrode configuration; mechanism discriminator, not historical provenance of any claimed aura"
  Source.publicAttribution

kirkus1970 : Source.AttributedSource
kirkus1970 = Source.mkNoDOISource
  "Kirkus Reviews (contemporary reviewer)"
  "Psychic Discoveries Behind the Iron Curtain"
  "21 April 1970 review describing the 1968 trip and claims in the Ostrander/Schroeder book; reviewer is an external source on public reception, not independent evidence for psychic experiments"
  "1970"
  "https://www.kirkusreviews.com/book-reviews/a/sheila-lynn-schroeder-ostrander-2/psychic-discoveries-behind-the-iron-curtain/"
  Source.newsSource
  "independent contemporary circulation/reception evidence for 1970 publication and topics; repeats the book's extraordinary claims without validating them"
  Source.publicAttribution


pragueJPRS1974 : Source.AttributedSource
pragueJPRS1974 = Source.mkNoDOISource
  "1973 Prague First Conference on Psychotronic Research contributors; translated by U.S. Joint Publications Research Service"
  "Proceedings of the Conference on Psychotronic Research (1st), Part I"
  "original 1973 Prague conference, 1974 JPRS translation/report JPRSL50221, National Technical Reports Library metadata; catalog inspected; full conference papers not acquired"
  "1973 conference; 1974 translation"
  "https://ntrl.ntis.gov/NTRL/dashboard/searchResults/titleDetail/JPRSL50221.xhtml"
  Source.archivalSource
  "specific original participant paper acquisition target; contents include biological electrodynamics, image currents and subjective states; listing establishes publication/report existence, not experimental truth"
  Source.publicAttribution

soucek2020 : Source.AttributedSource
soucek2020 = Source.mkDOISource
  "Ivan Souček"
  "Medical Pluralism During and After Socialism: A Study of Psychotronics in the Former Czechoslovakia"
  "Český lid 107(1), 51-69; original peer-reviewed 2020 sociohistorical fieldwork/analysis, visibly inspected pp.51,58"
  "2020"
  "10.21104/CL.2020.1.03"
  "https://ceskylid.avcr.cz/media/articles/712/submission/original/712-2425-1-SM.pdf"
  Source.academicArticleSource
  "independent sociohistorical account of Rejdák and psychotronics institutionalisation; original ethnography and cited histories support cultural analysis, not bioenergy efficacy"
  Source.publicAttribution

vasiliev1963English : Source.AttributedSource
vasiliev1963English = Source.mkNoDOISource
  "Leonid L. Vasiliev (original author; English translation authorised and revised by him)"
  "Experiments in Mental Suggestion"
  "1962 Leningrad University Russian original, 1963 authorised English translation, Institute for the Study of Mental Images; Wellcome catalogue (item in closed stores)"
  "1962 original; 1963 translation"
  "https://wellcomecollection.org/works/ygf3wazt"
  Source.academicBookSource
  "bibliographically verified Soviet experiment-author source and English dissemination; catalogue only, actual primary protocol and field-shielding experiments not independently inspected"
  Source.publicAttribution

clercaudioHistoricalQuote : Source.AttributedSource
clercaudioHistoricalQuote = Source.mkNoDOISource
  "Institut Metapsychique International; reproducing Fernand Clerc in Toute la Radio"
  "La parapsychologie hier, aujourd'hui, demain"
  "retrospective institutional essay preserves 1954 La Vie des Metiers proposal quoted in Toute la Radio no.192 of 12 January 1955; 1954/55 originals not separately acquired"
  "1981 historical essay; 1954/55 embedded contemporary quotations"
  "https://www.metapsychique.org/la-parapsychologie-hier-aujourdhui-demain/"
  Source.institutionalSource
  "attributed semantic predecessor to Rejdak's 1967/1970 use of psychotronique; historic quotation not experimental psi evidence"
  Source.publicAttribution

kholodnyi2017 : Source.AttributedSource
kholodnyi2017 = Source.mkNoDOISource
  "Yuri I. Kholodnyi"
  "History of psychotronic weapons: appearance, development and threat of recurrence"
  "Byulleten V zashchitu nauki 19 (2017), pp.140-162; search-index excerpts available, original PDF URL currently returns 404"
  "2017"
  "https://klnran.ru/wp-content/uploads/2017/04/BVZN_19.pdf"
  (Source.namedSourceKind "critical historical science-policy article")
  "secondary retrospective account quoting Yuri Azarov and Kitaygorodsky on reported 1972 conventional experiments; not the original 1972 lab log or independent modern replication"
  Source.publicAttribution

kuchinov2021 : Source.AttributedSource
kuchinov2021 = Source.mkNoDOISource
  "Eugene Kuchinov"
  "Quesalid's Knots: A Guide to the Soviet Union's Esoteric Research Institutes"
  "V-A-C Sreda 2021 cultural-history essay; full original online text and footnotes inspected"
  "2021"
  "https://sreda.v-a-c.org/en/read-01"
  (Source.namedSourceKind "independent historical interpretive essay")
  "explicitly cites Kholodnyi 2017 pp.144-150 for Azarov and Kitaygorodsky's reported 1972 field/reconstruction; NOT an independent 1972 experimental dataset"
  Source.publicAttribution

canner2021 : Source.AttributedSource
canner2021 = Source.mkNoDOISource
  "Stephen Canner"
  "The Comet, the Typist, and the Psychotronic Think Tank"
  "2021 independent cultural-history article with participant recollections/original personal-archive photos"
  "2021"
  "https://mediatedsignals.com/2021/04/26/the-comet-the-typist-and-the-psychotronic-think-tank-a-tale-of-the-new-age/"
  (Source.namedSourceKind "historical narrative and interview-based report")
  "documents a historian-mediated link between the 1970 book, Max Toth, Drbal, 1973 conference and 1974 Pyramid Power; underlying Toth contemporary documentation not acquired"
  Source.publicAttribution

mills2009 : Source.AttributedSource
mills2009 = Source.mkDOISource
  "Allan Mills"
  "Kirlian Photography"
  "History of Photography 33(3), 278-287, 2009"
  "2009"
  "10.1080/03087290802582988"
  "https://doi.org/10.1080/03087290802582988"
  Source.academicArticleSource
  "historical technical interpretation: ordinary corona discharge is real; psychic/health inference and poor repeatability challenged"
  Source.publicAttribution

tressoldiStorm2024 : Source.AttributedSource
tressoldiStorm2024 = Source.mkDOISource
  "Patrizio E. Tressoldi; Lance Storm"
  "Stage 2 Registered Report: Anomalous perception in a Ganzfeld condition"
  "F1000Research 10:234, final revised version 2024; meta-analysis of 113 reports dated 1974-2020"
  "2024 revised version"
  "10.12688/f1000research.51746.4"
  "https://doi.org/10.12688/f1000research.51746.4"
  Source.academicArticleSource
  "authors report small favourable anomalous-perception meta-analytic signal with methodological claims; NOT verification of Pavlita generator, Kirlian aura, 5D, or physical EM transfer"
  Source.publicAttribution

historicalDocuments : List Source.AttributedSource
historicalDocuments =
  wimmer1940 ∷ sievers1940 ∷ ostranderSchroeder1970 ∷
  maireLaMothe1975 ∷ czechArchive1985 ∷
  pehekKylerFaust1976 ∷ kirkus1970 ∷
  pragueJPRS1974 ∷ soucek2020 ∷ vasiliev1963English ∷
  clercaudioHistoricalQuote ∷ kholodnyi2017 ∷ kuchinov2021 ∷
  canner2021 ∷ mills2009 ∷ tressoldiStorm2024 ∷ []

historicalDocumentsCount : Source.sourceCount historicalDocuments ≡ 16
historicalDocumentsCount = refl

------------------------------------------------------------------------
-- Reuse canonical SOURCE-CROLE snowball and investigative claim receipts.
------------------------------------------------------------------------

wimmerSourceRetention : Snowball.SourceRoleSnowballReceipt wimmer1940
wimmerSourceRetention = Snowball.canonicalSourceRoleSnowballReceipt wimmer1940

diaSourceRetention : Snowball.SourceRoleSnowballReceipt maireLaMothe1975
diaSourceRetention = Snowball.canonicalSourceRoleSnowballReceipt maireLaMothe1975

ostranderCitedByDIA : Investigation.InvestigativeClaimReceipt
ostranderCitedByDIA = Investigation.investigative-claim-receipt
  "1975 analytic report explicitly cites 1970 public book"
  "DST-1810S-387-75 printed bibliography item 5, September 1975"
  "Maire and LaMothe 1975 government report"
  "https://www.theblackvault.com/documents/parapsychology/sovczech.pdf"
  Investigation.primaryCarrier
  Investigation.inspectedAndClaimLocated
  "1970 Ostrander/Schroeder book explicitly listed, not a secondary reviewer reporting a citation"
  Investigation.commonSourceDependent
  "web PDF page index 66, printed p.69, bibliography item 5"
  "No claim-by-claim mapping from each reported Pavlita or Kirlian passage to a specific 1970 page; inspect primary cited Soviet/Czech experiments before scientific promotion"
  Investigation.supportsBoundedClaim
  true false false

------------------------------------------------------------------------
-- Claim-level source-diligence gate: actual bibliography carrier inspected.
------------------------------------------------------------------------

bookReportCitationDiligence : Diligence.SourceDiligence
bookReportCitationDiligence = Diligence.source-diligence
  "Explicit 1970 book citation in 1975 US intelligence report"
  maireLaMothe1975
  Diligence.primaryProposition
  true refl
  "opened 69-page public PDF scan, visually inspected report title/author and selected bibliography pages"
  Diligence.primaryLocated
  "PDF index 66, printed p.69, selected bibliography reference 5"
  "report published September 1975; information cutoff 15 April 1975"
  "exact printed DST-1810S-387-75 report same-object title/date/author checked"
  "1970 publication predates 1975 report, not reverse"
  "actual bibliography citation establishes documentary dependence only"
  "contemporary Kirkus review and original Prentice-Hall library metadata separate existence/wording from paranormal experimental validity"
  "no reader may infer book experiments were independently replicated by US government"
  "concrete citation graph; no 1985 Czech ministry event attributed to this 1975 report"

------------------------------------------------------------------------
-- CLAIM-SPECIFIC RIVAL INTERPRETATIONS: ISOLATE THE 1972 EVENT.
-- Two later publications are a CHAIN, not two independent trials.
------------------------------------------------------------------------

reported1972SovietEvaluation : Investigation.InvestigativeClaimReceipt
reported1972SovietEvaluation = Investigation.investigative-claim-receipt
  "Secondary historical account of Soviet-Czech investigation of Pavlita's psychotronic devices in 1972"
  "Kholodnyi 2017 pp.144-150 as cited/recounted in Kuchinov 2021 footnotes 20,22-26"
  "Kuchinov 2021 discussion of Yuri Azarov's first-person retrospective account"
  "https://sreda.v-a-c.org/en/read-01"
  Investigation.secondaryCarrier
  Investigation.inspectedAndClaimLocated
  "Kuchinov cites Kholodnyi; Kholodnyi quotes Azarov and names physicist Alexander Kitaygorodsky. Original 1972 notebook/circuit/film was NOT acquired."
  Investigation.commonSourceDependent
  "same reported 1972 visit, not the distinct 1985 ministerial Soviet-GDR requests"
  "Acquire 1974 Vesmir Kitaygorodsky original and Azarov account, film and physical control descriptions"
  Investigation.supportsBoundedClaim
  true false false

reported1955FrenchCoinage : Investigation.InvestigativeClaimReceipt
reported1955FrenchCoinage = Investigation.investigative-claim-receipt
  "Clerc's French term psychotronique preceded Rejdak's Czech use"
  "La Vie des Metiers Nov 1954 and Toute la Radio no.192 12 January 1955, quoted in later IMI institutional essay"
  "IMI retrospective reproducing named Fernand Clerc original"
  "https://www.metapsychique.org/la-parapsychologie-hier-aujourdhui-demain/"
  Investigation.secondaryCarrier
  Investigation.inspectedAndClaimLocated
  "first-party contemporary periodical pages not acquired; later essay retains exact named author/date"
  Investigation.commonSourceDependent
  "a term of art, not proof that the underlying hypothesised energy exists"
  "Retrieve 1954 original and 1955 magazine issue, then Rejdak's exact first use"
  Investigation.supportsBoundedClaim
  true false false

------------------------------------------------------------------------
-- Directed transmission edges. Wording reflects the exact consumer:
-- correspondence / citation / request / independent mechanism control.
------------------------------------------------------------------------

data DocumentEdgeKind : Set where
  directCitation : DocumentEdgeKind
  directAdministrativeReference : DocumentEdgeKind
  archivistReportedContactRequest : DocumentEdgeKind
  contemporaryIndependentReview : DocumentEdgeKind
  controlsAlternativeMechanism : DocumentEdgeKind

record BoundedHistoricalEdge : Set where
  constructor historical-edge
  field
    origin : Source.AttributedSource
    destination : Source.AttributedSource
    relation : DocumentEdgeKind
    exactSpan : String
    transmittedClaimScope : String
    firstUnpaidLeaf : String
    sourceEvidenceEqualsMechanismProof : Bool
    hardwareInheritanceEstablished : Bool
    independentExperimentalReplicationEstablished : Bool
    sourceEvidenceEqualsMechanismProofIsFalse :
      sourceEvidenceEqualsMechanismProof ≡ false
    hardwareInheritanceEstablishedIsFalse :
      hardwareInheritanceEstablished ≡ false
    independentExperimentalReplicationEstablishedIsFalse :
      independentExperimentalReplicationEstablished ≡ false
open BoundedHistoricalEdge public

wimmerToSievers : BoundedHistoricalEdge
wimmerToSievers = historical-edge
  wimmer1940 sievers1940 directAdministrativeReference
  "Ursinus /dowsing/13/ Sievers letter description and German transcription, 20 Nov 1940, identifies the Wimmer review of seized dowsing literature"
  "The Ahnenerbe/SD administrative correspondence routed a named assessment; shared Nazi institutional activity, NOT paranormal success"
  "Obtain dated dispatch/receipt for particular paper versions if reconstructing exact correspondence movement"
  false false false refl refl refl

publicBookCitedByMilitaryReport : BoundedHistoricalEdge
publicBookCitedByMilitaryReport = historical-edge
  ostranderSchroeder1970 maireLaMothe1975 directCitation
  "DIA task DST-1810S-387-75 selected bibliography, printed p.69, scan index 66, entry 5"
  "Direct documentary bibliographic reuse of Ostrander/Schroeder 1970 by Maire/LaMothe 1975; NOT independent verification of public book's alleged research"
  "Locate each downstream specific proposition's source notes and independently inspect the original Eastern Bloc experiment when available"
  false false false refl refl refl

contemporaryReviewOfBook : BoundedHistoricalEdge
contemporaryReviewOfBook = historical-edge
  ostranderSchroeder1970 kirkus1970 contemporaryIndependentReview
  "Kirkus review, release date 21 April 1970"
  "Independent existence/public reception corroboration, derivative testimony about experimental details"
  "Do not count contemporary review as experimental replication"
  false false false refl refl refl

kirlianPhysicalNullControl : BoundedHistoricalEdge
kirlianPhysicalNullControl = historical-edge
  ostranderSchroeder1970 pehekKylerFaust1976 controlsAlternativeMechanism
  "Science 194(4262):263-270, DOI 10.1126/science.968480, abstract; earlier 1970 book indexes Kirlian claims"
  "Different authors directly tested a conventional mechanism for Kirlian-style images; NOT proof of their direct reading of the 1970 book"
  "Original article full methods and instrumentation plus exact source comparison to each earlier aura claim"
  false false false refl refl refl

-- The 1985 archive is a custodian SUMMARY OF RECORDS.
-- Soviet/GDR request directions remain reported requests; do not invent
-- a correspondent's incoming response or fabricated source document.
data CzechoslovakRequestTarget : Set where
  sovietMilitaryIntelligence : CzechoslovakRequestTarget
  eastGermanMilitaryIntelligence : CzechoslovakRequestTarget

record ReportedArchiveRequest : Set where
  constructor archive-request
  field
    custodian : Source.AttributedSource
    target : CzechoslovakRequestTarget
    exactStatement : String
    archivalOriginalOpened : Bool
    incomingAcceptanceVerified : Bool
    jointExperimentVerified : Bool
open ReportedArchiveRequest public

czechToSovietRequest : ReportedArchiveRequest
czechToSovietRequest = archive-request czechArchive1985
  sovietMilitaryIntelligence
  "Czech Security Services Archive paragraphs following 6 September 1985 order; reports requested assistance from Soviet General Staff Intelligence Directorate"
  false false false

czechToGDRRequest : ReportedArchiveRequest
czechToGDRRequest = archive-request czechArchive1985
  eastGermanMilitaryIntelligence
  "Same Czech archival summary, 1985, reports request for GDR General Staff Intelligence Directorate cooperation"
  false false false

------------------------------------------------------------------------
-- A shared motif is not a genealogical edge. Exact two-world witness:
-- identical 'paranormal apparatus' wording can coexist with sourced
-- transmission or independent later rediscovery. Names do not tell which.
------------------------------------------------------------------------

data HypotheticalHistoricalWorld : Set where
  worldDocumentedReuse : HypotheticalHistoricalWorld
  worldIndependentSymbolism : HypotheticalHistoricalWorld

data CoarseMotif : Set where
  invisibleEnergyTechnology : CoarseMotif

coarseHistoricalMotif : HypotheticalHistoricalWorld → CoarseMotif
coarseHistoricalMotif _ = invisibleEnergyTechnology

data TransferStatus : Set where
  documentaryReuse : TransferStatus
  noDocumentedReuse : TransferStatus

historicalTransferAt : HypotheticalHistoricalWorld → TransferStatus
historicalTransferAt worldDocumentedReuse = documentaryReuse
historicalTransferAt worldIndependentSymbolism = noDocumentedReuse

coarseWordCannotTellGenealogy :
  INF.FactorsThrough coarseHistoricalMotif historicalTransferAt → ⊥
coarseWordCannotTellGenealogy =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      worldDocumentedReuse worldIndependentSymbolism refl (λ ()))

-- No claim that Nazi scientists supplied Soviet/Czech institutions with
-- effective technology, or that Pavlita designs physically reached modern
-- Succor Punch/Rodin/iTorus products, is warranted on these receipts.
data NaziToSovietDeviceTransmissionEstablished : Set where
data PavlitaToCroftHardwareTransmissionEstablished : Set where
data USIntelligenceReportValidatesPavlitaPhysics : Set where
data ArchivedCorrespondenceProvesParanormalEffect : Set where

noNaziToSovietHardwareReceipt :
  NaziToSovietDeviceTransmissionEstablished → ⊥
noNaziToSovietHardwareReceipt ()

noPavlitaToCroftHardwareReceipt :
  PavlitaToCroftHardwareTransmissionEstablished → ⊥
noPavlitaToCroftHardwareReceipt ()

noScienceFromMilitaryBibliography :
  USIntelligenceReportValidatesPavlitaPhysics → ⊥
noScienceFromMilitaryBibliography ()

noParanormalProofFromAdministrativeArchive :
  ArchivedCorrespondenceProvesParanormalEffect → ⊥
noParanormalProofFromAdministrativeArchive ()

------------------------------------------------------------------------
-- Existing Ibrahim Pareto consumers. These ranks are LOCAL to this
-- historical research question; they are not a re-ranking of the global
-- 2014 FLN dump/producer custody frontier.
------------------------------------------------------------------------

transmissionCitationPaid : Pareto.ParetoFrontierLeaf
transmissionCitationPaid = Pareto.pareto-frontier-leaf
  0 Pareto.paidSharedParent
  "Direct Ostrander/Schroeder 1970 -> Maire/LaMothe 1975 bibliographic reference"
  "Web screenshot of DST-1810S-387-75 p.69/index66, item 5; 1970 publication independent bibliographic coordinates"
  "No exact page-to-claim citation trace or authorial source-criticism verification yet"
  "Existence of explicit citation closes the bounded documentary reuse edge only"
  "Separates actual historical media transmission from physical research reproduction"
  false

firstUnpaidEasternPrimary : Pareto.ParetoFrontierLeaf
firstUnpaidEasternPrimary = Pareto.pareto-frontier-leaf
  1 Pareto.currentHighestAlpha
  "Pavlita original design/claims and 1970 book exact page-to-original-document citation trail"
  "1975 US analytic report describes generators on pp.46-49; cites the 1970 book in selected bibliography"
  "Acquire and inspect primary Pavlita/Rejdak contemporaneous technical publications or 1973 Prague conference proceedings; map which Maire paragraphs rely on book vs independent Eastern Bloc sources"
  "Only claim-specific original-first lineage and diagram comparison, no popularity-based promotion"
  "Separates first-party apparatus from Western secondary retellings"
  false

unprocessedMilitaryArchive : Pareto.ParetoFrontierLeaf
unprocessedMilitaryArchive = Pareto.pareto-frontier-leaf
  2 Pareto.currentHighestAlpha
  "1985 Czech defence ministry instruction and actual Soviet/GDR request correspondence"
  "Czech Security Services Archive public summary names 6 September, 24 October, 31 October 1985"
  "Request archive file images/fonds identifiers and independently establish actual outgoing requests, incoming responses and any funded tests"
  "Only incoming documents/receipts can upgrade proposed cooperation to actual bilateral programme"
  "Institutional contact lineage without hardware mythology"
  false

ahnenerbeGraph : Pareto.ParetoFrontierLeaf
ahnenerbeGraph = Pareto.pareto-frontier-leaf
  3 Pareto.consumerDrivenOnly
  "Wimmer/Sievers 1940 correspondence and publication control"
  "Two original actor-authored German documents with Ursinus transcriptions"
  "Scope limits: no physics replication; no demonstrated link to Soviet/Czech psychotronics or later Vril fiction"
  "Attach further 1940 correspondence only if it disambiguates actual institutional action"
  "Institutional chronology and disconfirmation of over-broad Nazi technology claims"
  false

modernTransmission : Pareto.ParetoFrontierLeaf
modernTransmission = Pareto.pareto-frontier-leaf
  4 Pareto.consumerDrivenOnly
  "1970/1975 -> Reich/Welz/Croft/Rodin/modern commercial models"
  "Cultural and device-family similarities already catalogued in existing PsychotronicsSuccorSourceAtlasExact"
  "Obtain a dated actual citation/book owner/interview/circuit drawing before asserting a named downstream influence"
  "Any claimed direct technology transfer needs same-design, author, version and custody receipts"
  "Manufacturers' vocabulary without invented genealogical arrows"
  false

-- Source retention reused, proof/truth/authority not imported by citation.
sourceDoesNotCreateProof :
  Source.citationImportsProof maireLaMothe1975 ≡ false
sourceDoesNotCreateProof = refl

sourceDoesNotCreateAuthority :
  Source.citationCreatesAuthority wimmer1940 ≡ false
sourceDoesNotCreateAuthority = refl

-- Exact connection to existing OSINT source-role catalog:
institutionalArchiveObservation : OSINT.OSINTObservation
institutionalArchiveObservation = OSINT.osint-observation
  "https://www.abscr.cz/en/archivalie/psychotronics-in-the-czechoslovak-peoples-army/"
  "unprocessed Czechoslovak intelligence archive collection, raw images not opened"
  "official custodian web summary inspected 2026-10-24"
  OSINT.publicInstitutionalStatement
  OSINT.sourceOfSourceCarrier
  "1985 instruction, requests, October reports"
  "secondary archivist summary of underlying original records"
  "no native file hash; do not manufacture"
  false true true
