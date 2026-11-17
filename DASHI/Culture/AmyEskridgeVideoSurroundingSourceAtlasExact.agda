module DASHI.Culture.AmyEskridgeVideoSurroundingSourceAtlasExact where

-- Source-family registry covering the original HAL5 slideshow, its omitted
-- historical bibliographies and the edited Be Inspired video. Each source is
-- preserved under its actual inventor/author/institution and exact DOI when
-- known. A patent grant is not a successful experiment. Author testimony is
-- not independently verified operation. Bibliographic identity is NOT proof.
-- HAL5: Amy Eskridge, A Historical Perspective on Anti-Gravity Technology,
-- 2018-12-06, https://www.hal5.org/PDF/HAL5-Dec2018-Talk-AntiGravity.pdf
-- Video: Be Inspired, 2026-05-12, ID acw16d6CCnY.
-- See Docs/SourceAttributionPolicy.md.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)
import DASHI.Core.AttributedSourceCore as A

data ReadingDepth : Set where
  patent : ReadingDepth
  body : ReadingDepth
  abstract : ReadingDepth
  locator : ReadingDepth

record LinkedSource : Set where
  constructor linked-source
  field
    source : A.AttributedSource
    readingDepth : ReadingDepth
    deckPDFPage : String
    editedVideoTime : String
    strictlySourcePaid : String
    independentUnpaid : String
open LinkedSource public

brown1960 : LinkedSource
brown1960 = linked-source
  (A.mkNoDOISource
    "Thomas Townsend Brown"
    "Electrokinetic apparatus"
    "US2949550A"
    "1960"
    "https://patents.google.com/patent/US2949550A/en"
    A.governmentSource
    "Patent claims relative motion in surrounding medium"
    A.publicAttribution)
  patent
  "10"
  "06:21-06:46"
  "Patent claims relative motion in surrounding medium"
  "Independent vacuum/ionic-wind controlled measurements"

brown1967 : LinkedSource
brown1967 = linked-source
  (A.mkNoDOISource
    "Thomas Townsend Brown"
    "Method and apparatus for producing ions and electrically-charged aerosols"
    "US3296491A"
    "1967"
    "https://patents.google.com/patent/US3296491A/en"
    A.governmentSource
    "Related patent explicitly names electrohydrodynamic ion forces"
    A.publicAttribution)
  patent
  "10"
  "Brown confounder"
  "Related patent explicitly names electrohydrodynamic ion forces"
  "Direct relation to alleged prior vacuum apparatus"

teslaIncorrect : LinkedSource
teslaIncorrect = linked-source
  (A.mkNoDOISource
    "Joseph Hallgarth; Earl E. Chandler"
    "Grain-treating machine"
    "US1655144A"
    "1928"
    "https://patents.google.com/patent/US1655144A/en"
    A.governmentSource
    "The number shown in HAL5 and the edited video is not a Tesla patent"
    A.publicAttribution)
  patent
  "12"
  "06:51"
  "The number shown in HAL5 and the edited video is not a Tesla patent"
  "An original Tesla source for the attributed claimed space drive"

teslaAerial : LinkedSource
teslaAerial = linked-source
  (A.mkNoDOISource
    "Nikola Tesla"
    "Apparatus for aerial transportation"
    "US1655114A"
    "1928"
    "https://patents.google.com/patent/US1655114A/en"
    A.governmentSource
    "A distinct Tesla aircraft patent"
    A.publicAttribution)
  patent
  "12"
  "06:51"
  "A distinct Tesla aircraft patent"
  "Evidence of any reactionless or metric-engineered vehicle"

grfInstitution : LinkedSource
grfInstitution = linked-source
  (A.mkNoDOISource
    "Gravity Research Foundation"
    "Founding history"
    "Official institute history"
    "1949"
    "https://www.gravityresearchfoundation.org/historic"
    A.institutionalSource
    "Foundation organised 19 January 1949 and first awarded essays December 1949"
    A.publicAttribution)
  body
  "13"
  "07:32"
  "Foundation organised 19 January 1949 and first awarded essays December 1949"
  "Resolve conflicting 1948 historical founding wording"

grfScholarship : LinkedSource
grfScholarship = linked-source
  (A.mkDOISource
    "David Kaiser; Dean Rickles"
    "The Price of Gravity: Private Patronage and the Transformation of Gravitational Physics after World War II"
    "Historical Studies in the Natural Sciences 48(3) 338-379"
    "2018"
    "10.1525/hsns.2018.48.3.338"
    "https://doi.org/10.1525/hsns.2018.48.3.338"
    A.academicArticleSource
    "Scholarly explanation of real gravity research patronage"
    A.publicAttribution)
  abstract
  "13-15"
  "07:32"
  "Scholarly explanation of real gravity research patronage"
  "Experimental anti-gravity outcome"

dewittHistory : LinkedSource
dewittHistory = linked-source
  (A.mkNoDOISource
    "Edition Open Sources history"
    "The Chapel Hill Conference in Context"
    "Scholarly edited history of DeWitt"
    "2011"
    "https://www.edition-open-sources.org/sources/5/3/index.html"
    A.academicChapterSource
    "Historical 1953 Bryce DeWitt prize essay and its critical interpretation"
    A.publicAttribution)
  body
  "14"
  "omitted"
  "Historical 1953 Bryce DeWitt prize essay and its critical interpretation"
  "Full original 1953 manuscript and quote calibration"

dean : LinkedSource
dean = linked-source
  (A.mkNoDOISource
    "Norman L. Dean"
    "System for converting rotary motion into unidirectional motion"
    "US2886976A"
    "1959"
    "https://patents.google.com/patent/US2886976A/en"
    A.governmentSource
    "Patented oscillatory inertia mechanism"
    A.publicAttribution)
  patent
  "17"
  "08:15"
  "Patented oscillatory inertia mechanism"
  "Isolated no-exhaust thrust"

wallace605 : LinkedSource
wallace605 = linked-source
  (A.mkNoDOISource
    "Henry William Wallace"
    "Method and apparatus for generating a secondary gravitational force field"
    "US3626605A"
    "1971"
    "https://patents.google.com/patent/US3626605A/en"
    A.governmentSource
    "Patent claims kinemassic field"
    A.publicAttribution)
  patent
  "18"
  "08:38"
  "Patent claims kinemassic field"
  "Replicable gravity-force measurements"

wallace606 : LinkedSource
wallace606 = linked-source
  (A.mkNoDOISource
    "Henry William Wallace"
    "Method and apparatus for generating a dynamic force field"
    "US3626606A"
    "1971"
    "https://patents.google.com/patent/US3626606A/en"
    A.governmentSource
    "Second distinct Wallace patent"
    A.publicAttribution)
  patent
  "18"
  "08:38"
  "Second distinct Wallace patent"
  "Independent device/field replication"

royalInstitution : LinkedSource
royalInstitution = linked-source
  (A.mkNoDOISource
    "Royal Institution"
    "The gyroscope an engineer and the Christmas Lectures"
    "Official Royal Institution history"
    "1974"
    "https://www.rigb.org/explore-science/explore/blog/gyroscope-engineer-and-christmas-lectures"
    A.institutionalSource
    "Original 8 November 1974 Friday Discourse documented"
    A.publicAttribution)
  body
  "19"
  "09:01"
  "Original 8 November 1974 Friday Discourse documented"
  "Specific fellowship removal or anomalous sustained force"

cambridgeGyro : LinkedSource
cambridgeGyro = linked-source
  (A.mkNoDOISource
    "University of Cambridge"
    "Laithwaite gyroscope replications and Newtonian explanation"
    "Cambridge engineering"
    "undated"
    "https://www3.eng.cam.ac.uk/~hemh1/gyroscopes/laithwaite.html"
    A.institutionalSource
    "Replications of observed motions with classical mechanics"
    A.publicAttribution)
  body
  "19"
  "09:01"
  "Replications of observed motions with classical mechanics"
  "Experimental antigravity or institutional expulsion"

gao1969 : LinkedSource
gao1969 = linked-source
  (A.mkNoDOISource
    "United States Government Accountability Office"
    "Implementation of 1970 Defense Procurement Authorization Act requiring relation to military functions"
    "GAO B-167034 Public Law 91-121 section 203"
    "1970"
    "https://www.gao.gov/products/b-167034"
    A.governmentSource
    "1969 law restricted DoD basic research spending in specified terms"
    A.publicAttribution)
  body
  "21"
  "11:31"
  "1969 law restricted DoD basic research spending in specified terms"
  "Mandatory antigravity classification or secret-budget transfer"

hutchison : LinkedSource
hutchison = linked-source
  (A.mkNoDOISource
    "Hutchison Files"
    "Hutchison Effect source-catalogue and apparatus descriptions"
    "Source/secondary archive"
    "2026"
    "https://hutchisonfiles.com/"
    A.archivalSource
    "Historical source discovery for John Hutchison claims"
    A.publicAttribution)
  body
  "22"
  "omitted"
  "Historical source discovery for John Hutchison claims"
  "Reliable independent controlled replication"

woodward1992 : LinkedSource
woodward1992 = linked-source
  (A.mkDOISource
    "James F. Woodward"
    "A stationary apparent weight shift from a transient Machian mass fluctuation"
    "Foundations of Physics Letters 5 425-442"
    "1992"
    "10.1007/BF00690424"
    "https://doi.org/10.1007/BF00690424"
    A.academicArticleSource
    "Original Machian thrust hypothesis"
    A.publicAttribution)
  abstract
  "23"
  "12:01"
  "Original Machian thrust hypothesis"
  "Verified propellantless engine"

liTorr1991 : LinkedSource
liTorr1991 = linked-source
  (A.mkDOISource
    "Ning Li; D. G. Torr"
    "Effects of a gravitomagnetic field on pure superconductors"
    "Physical Review D 43 457"
    "1991"
    "10.1103/PhysRevD.43.457"
    "https://doi.org/10.1103/PhysRevD.43.457"
    A.academicArticleSource
    "Original superconductor gravitational theory"
    A.publicAttribution)
  abstract
  "24"
  "09:30"
  "Original superconductor gravitational theory"
  "Observed antigravity"

liTorr1992 : LinkedSource
liTorr1992 = linked-source
  (A.mkDOISource
    "Ning Li; D. G. Torr"
    "Gravitational effects on the magnetic attenuation of superconductors"
    "Physical Review B 46 5489"
    "1992"
    "10.1103/PhysRevB.46.5489"
    "https://doi.org/10.1103/PhysRevB.46.5489"
    A.academicArticleSource
    "Separate published theoretical proposal"
    A.publicAttribution)
  abstract
  "24"
  "09:30"
  "Separate published theoretical proposal"
  "Experimental source-to-field transfer"

li1997 : LinkedSource
li1997 = linked-source
  (A.mkDOISource
    "Ning Li et al"
    "Static test for a gravitational force coupled to type II YBCO superconductors"
    "Physica C 281 260-267"
    "1997"
    "10.1016/S0921-4534(97)01462-7"
    "https://ntrs.nasa.gov/citations/19990039542"
    A.academicArticleSource
    "Bounded negative static gravimeter constraint"
    A.publicAttribution)
  abstract
  "24"
  "09:30"
  "Bounded negative static gravimeter constraint"
  "Direct falsification of every rotating configuration"

nasa1998 : LinkedSource
nasa1998 = linked-source
  (A.mkNoDOISource
    "D. Noever; R. Koczor; R. Robertson"
    "Superconductor-Mediated Modification of Gravity AC Motor Experiments with Bulk YBCO Disks in Rotating Magnetic Fields"
    "NASA NTRS 19990019627"
    "1998"
    "https://ntrs.nasa.gov/citations/19990019627"
    A.governmentSource
    "Rotating-field test reported null in its sensitivity"
    A.publicAttribution)
  abstract
  "26"
  "10:43"
  "Rotating-field test reported null in its sensitivity"
  "Every related apparatus regime"

nasaGrant : LinkedSource
nasaGrant = linked-source
  (A.mkNoDOISource
    "Ning Li; UAH"
    "Activities of UAH cooperative agreement NCC8-124"
    "NASA NTRS 20000038203"
    "2000"
    "https://ntrs.nasa.gov/citations/20000038203"
    A.governmentSource
    "Two YBCO disks; planned all-up gravity test incomplete"
    A.publicAttribution)
  body
  "24-25"
  "09:55"
  "Two YBCO disks; planned all-up gravity test incomplete"
  "Army contract technical result"

armyOriginalLocator : LinkedSource
armyOriginalLocator = linked-source
  (A.mkNoDOISource
    "U.S. Department of Defense"
    "FY2001 Other Transactions report concerning DAAH01-01-9-R001"
    "DoD annual report FY01RPT.doc"
    "2001"
    "https://web.archive.org/web/20210801183915id_/https://www.acq.osd.mil/dpap/Docs/FY01RPT.doc"
    A.governmentSource
    "Archive locator already discovered in Ning Li source producer"
    A.publicAttribution)
  locator
  "24"
  "10:03"
  "Archive locator already discovered in Ning Li source producer"
  "Original row inspection and test closeout"

podk1992 : LinkedSource
podk1992 = linked-source
  (A.mkDOISource
    "E. Podkletnov; R. Nieminen"
    "A possibility of gravitational force shielding by bulk YBCO superconductor"
    "Physica C 203 441-444"
    "1992"
    "10.1016/0921-4534(92)90055-H"
    "https://www.sciencedirect.com/science/article/pii/092145349290055H"
    A.academicArticleSource
    "Authors report 0.05-0.3 percent weight reduction in original rig"
    A.publicAttribution)
  body
  "26"
  "10:43"
  "Authors report 0.05-0.3 percent weight reduction in original rig"
  "Independent replication"

podk1997 : LinkedSource
podk1997 = linked-source
  (A.mkNoDOISource
    "E. E. Podkletnov"
    "Weak gravitation shielding properties of composite bulk YBCO below 70 K under e.m. field"
    "arXiv cond-mat/9701074"
    "1997"
    "https://arxiv.org/abs/cond-mat/9701074"
    A.academicArticleSource
    "Later author reports 1.9-2.1 percent in a changed rig"
    A.publicAttribution)
  abstract
  "26"
  "10:43"
  "Later author reports 1.9-2.1 percent in a changed rig"
  "Independent matched apparatus high-speed replication"

hathaway2003 : LinkedSource
hathaway2003 = linked-source
  (A.mkDOISource
    "G. Hathaway; B. Cleveland; Y. Bao"
    "Gravity modification experiment using a rotating superconducting disk and radio frequency fields"
    "Physica C 385 488-500"
    "2003"
    "10.1016/S0921-4534(02)02284-0"
    "https://www.sciencedirect.com/science/article/pii/S0921453402022840"
    A.academicArticleSource
    "Authors report no effect at 0.001 percent using dummy controls and a lower max rpm"
    A.publicAttribution)
  body
  "26"
  "surrounding control"
  "Authors report no effect at 0.001 percent using dummy controls and a lower max rpm"
  "Universal rejection of untested faster rotation"

tajmar2007 : LinkedSource
tajmar2007 = linked-source
  (A.mkNoDOISource
    "M. Tajmar; F. Plesescu; B. Seifert; R. Schnitzer; I. Vasiljevich"
    "Search for Frame-Dragging-Like Signals Close to Spinning Superconductors"
    "arXiv 0707.3806"
    "2007"
    "https://arxiv.org/abs/0707.3806"
    A.academicArticleSource
    "Critical temperature mismatch and theoretical magnitude constraints"
    A.publicAttribution)
  abstract
  "26"
  "surrounding control"
  "Critical temperature mismatch and theoretical magnitude constraints"
  "Independent physical origin of all anomalies"

torrVargas2005 : LinkedSource
torrVargas2005 = linked-source
  (A.mkNoDOISource
    "Douglas G. Torr; Jose G. Vargas"
    "Field converter"
    "US6891712B2"
    "2005"
    "https://patents.google.com/patent/US6891712B2/en"
    A.governmentSource
    "Inhomogeneous electric-field electrode patent originally claimed"
    A.publicAttribution)
  patent
  "27"
  "omitted"
  "Inhomogeneous electric-field electrode patent originally claimed"
  "Verified gravity-beam propulsion"

torrVargas2008 : LinkedSource
torrVargas2008 = linked-source
  (A.mkNoDOISource
    "Douglas G. Torr; Jose G. Vargas"
    "Field converter"
    "US7327548B2"
    "2008"
    "https://patents.google.com/patent/US7327548B2/en"
    A.governmentSource
    "Related second patent with separate filing"
    A.publicAttribution)
  patent
  "27"
  "omitted"
  "Related second patent with separate filing"
  "Independent force test or Timir Datta as patent inventor"

poher2020 : LinkedSource
poher2020 = linked-source
  (A.mkDOISource
    "Claude Poher; Danielle Poher"
    "Quantum Model of Inertia"
    "Applied Physics Research 12(4)"
    "2020"
    "10.5539/apr.v12n4p8"
    "https://ccsenet.org/journal/index.php/apr/article/view/0/43410"
    A.academicArticleSource
    "Author-proposed Universon model and experimental interpretation"
    A.publicAttribution)
  abstract
  "29"
  "11:12"
  "Author-proposed Universon model and experimental interpretation"
  "2015 NASA original report and independent replication"

jane2002 : LinkedSource
jane2002 = linked-source
  (A.mkNoDOISource
    "Nick Cook"
    "Anti-gravity propulsion comes out of the closet"
    "Jane's Defence Weekly"
    "2002"
    "https://archive.md/lG1GW"
    A.newsSource
    "Reports Boeing GRASP in July 2002"
    A.publicAttribution)
  body
  "31"
  "12:36"
  "Reports Boeing GRASP in July 2002"
  "Successful Boeing antigravity system"

diaFOIA2022 : LinkedSource
diaFOIA2022 = linked-source
  (A.mkNoDOISource
    "U.S. Defense Intelligence Agency"
    "FOIA-00159-2018 response and 37-document DIRD inventory"
    "DIA U-22-7061/IMO-2"
    "2022"
    "https://documents2.theblackvault.com/documents/dia/AAWSAP-DIRDs/FOIA%2000159-2018.pdf"
    A.governmentSource
    "37 titles 1473 listed pages"
    A.publicAttribution)
  body
  "32"
  "14:07"
  "37 titles 1473 listed pages"
  "Video 38th title and operational technology"

fox2026 : LinkedSource
fox2026 = linked-source
  (A.mkNoDOISource
    "Morgan Phillips"
    "11th scientist death emerges in string of missing dead officials"
    "Fox News Digital 17 April 2026"
    "2026"
    "https://www.foxnews.com/politics/11th-scientist-death-emerges-string-missing-dead-officials-access-us-secrets/"
    A.newsSource
    "Secondary media 11-person collection"
    A.publicAttribution)
  body
  "none"
  "00:21"
  "Secondary media 11-person collection"
  "Forensic cause and common programme"

house2026 : LinkedSource
house2026 = linked-source
  (A.mkNoDOISource
    "House Oversight and Government Reform"
    "FBI letter investigating unconfirmed missing-scientist reports"
    "House Oversight 20 April 2026"
    "2026"
    "https://oversight.house.gov/wp-content/uploads/2026/04/FBI-Missing-Scientists-Letter_4.20.26.pdf"
    A.governmentSource
    "Official request says at least ten reports unconfirmed"
    A.publicAttribution)
  body
  "none"
  "00:21"
  "Official request says at least ten reports unconfirmed"
  "Named shared programme and motive"

amyZoom : LinkedSource
amyZoom = linked-source
  (A.mkNoDOISource
    "Amy Eskridge; Jeremy Rys; Mark Sokol"
    "Amy Eskridge Zoom source recording"
    "Blocked Epistemology archived transcript"
    "2020"
    "https://blockedepistemology.substack.com/p/archive-amy-eskridge-zoom"
    A.archivalSource
    "Original speaker testimony including NSA hearsay"
    A.publicAttribution)
  body
  "none"
  "00:00-01:53"
  "Original speaker testimony including NSA hearsay"
  "NSA documentary list and physical surveillance proof"

burisch2006 : LinkedSource
burisch2006 = linked-source
  (A.mkNoDOISource
    "Dan Burisch; Kerry Cassidy; Bill Ryan"
    "Out From Under Majestic Part 2"
    "Project Camelot primary interview"
    "2006"
    "https://projectavalon.net/lang/en/dan_burisch_interview_transcript_2_en.html"
    A.archivalSource
    "Speaker P-45 future-human assertion"
    A.publicAttribution)
  body
  "none"
  "02:04"
  "Speaker P-45 future-human assertion"
  "Actual time-travel mechanism"

burisch2007 : LinkedSource
burisch2007 = linked-source
  (A.mkNoDOISource
    "Dan Burisch; Kerry Cassidy; Bill Ryan"
    "Stargate Secrets Part 1"
    "Project Camelot primary interview"
    "2007"
    "https://projectavalon.net/lang/en/dan_burisch_stargate_secrets_interview_transcript_1_en.html"
    A.archivalSource
    "Speaker account of Looking Glass >50 stargates and NATO custody"
    A.publicAttribution)
  body
  "none"
  "16:02-32:04"
  "Speaker account of Looking Glass >50 stargates and NATO custody"
  "Physical experimental government confirmation"

dick1977 : LinkedSource
dick1977 = linked-source
  (A.mkNoDOISource
    "Philip K. Dick"
    "If You Find This World Bad You Should See Some of the Others"
    "Metz 1977 speech transcript"
    "1977"
    "https://singjupost.com/transcript-philip-k-dick-speech-at-metz-france-1977/"
    A.archivalSource
    "Source of speculative speech"
    A.publicAttribution)
  body
  "none"
  "16:49"
  "Source of speculative speech"
  "Time-machine engineering"

deutsch1995 : LinkedSource
deutsch1995 = linked-source
  (A.mkNoDOISource
    "David Deutsch; Noorderlicht"
    "The Multiverse television interview"
    "Noorderlicht interview 1995"
    "1995"
    "https://www.youtube.com/watch?v=SDZ454K_lBY"
    A.archivalSource
    "Direct quote about many-worlds and quantum interference"
    A.publicAttribution)
  body
  "none"
  "17:13"
  "Direct quote about many-worlds and quantum interference"
  "Alternate timeline device testimony"

deutsch2002 : LinkedSource
deutsch2002 = linked-source
  (A.mkDOISource
    "David Deutsch"
    "The structure of the multiverse"
    "Proceedings Royal Society A 458 2911-2923"
    "2002"
    "10.1098/rspa.2002.1015"
    "https://arxiv.org/abs/quant-ph/0104033"
    A.academicArticleSource
    "Published quantum multiverse mathematical proposal"
    A.publicAttribution)
  abstract
  "none"
  "17:13"
  "Published quantum multiverse mathematical proposal"
  "Macroscopic timeline alteration"

bem2011 : LinkedSource
bem2011 = linked-source
  (A.mkDOISource
    "Daryl J. Bem"
    "Feeling the future experimental evidence for anomalous retroactive influences"
    "JPSP 100(3) 407-425"
    "2011"
    "10.1037/a0021524"
    "https://pubmed.ncbi.nlm.nih.gov/21280961/"
    A.academicArticleSource
    "Nine reported retrospective psychology experiments"
    A.publicAttribution)
  abstract
  "none"
  "18:35"
  "Nine reported retrospective psychology experiments"
  "Original audiovisual physiological demonstration identity"

cornellBem2010 : LinkedSource
cornellBem2010 = linked-source
  (A.mkNoDOISource
    "Cornell Chronicle"
    "Study looks at brains ability to see the future"
    "Cornell University 2010"
    "2010"
    "https://news.cornell.edu/stories/2010/12/study-looks-brains-ability-see-future"
    A.institutionalSource
    "Contemporaneous Bem paraphrase near identical to video"
    A.publicAttribution)
  body
  "none"
  "18:35"
  "Contemporaneous Bem paraphrase near identical to video"
  "Direct audiovisual source speaker identity"

radin2004 : LinkedSource
radin2004 = linked-source
  (A.mkNoDOISource
    "Dean I. Radin"
    "Psychophysiological Evidence of Possible Retrocausal Effects in Humans"
    "Institute of Noetic Sciences conference manuscript"
    "2004"
    "https://citeseerx.ist.psu.edu/document?doi=b48b5fa8cf7aaf451a4d40da8b68841d886e30dd&repid=rep1&type=pdf"
    A.academicArticleSource
    "Different actual skin-conductance presentiment protocol"
    A.publicAttribution)
  abstract
  "none"
  "18:39 comparison"
  "Different actual skin-conductance presentiment protocol"
  "Independent replication and video speaker identification"

bemMeta2015 : LinkedSource
bemMeta2015 = linked-source
  (A.mkDOISource
    "Daryl J. Bem; Patrizio Tressoldi; Thomas Rabeyron; Michael Duggan"
    "Feeling the future meta-analysis of 90 experiments"
    "F1000Research 4 1188"
    "2015"
    "10.12688/f1000research.7177.2"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC4706048/"
    A.academicArticleSource
    "Authors report a positive small meta-analytic effect"
    A.publicAttribution)
  abstract
  "none"
  "18:35 context"
  "Authors report a positive small meta-analytic effect"
  "Independent methodological evaluation and preregistration"

allSurroundingSources : List LinkedSource
allSurroundingSources =
  brown1960 ∷
  brown1967 ∷
  teslaIncorrect ∷
  teslaAerial ∷
  grfInstitution ∷
  grfScholarship ∷
  dewittHistory ∷
  dean ∷
  wallace605 ∷
  wallace606 ∷
  royalInstitution ∷
  cambridgeGyro ∷
  gao1969 ∷
  hutchison ∷
  woodward1992 ∷
  liTorr1991 ∷
  liTorr1992 ∷
  li1997 ∷
  nasa1998 ∷
  nasaGrant ∷
  armyOriginalLocator ∷
  podk1992 ∷
  podk1997 ∷
  hathaway2003 ∷
  tajmar2007 ∷
  torrVargas2005 ∷
  torrVargas2008 ∷
  poher2020 ∷
  jane2002 ∷
  diaFOIA2022 ∷
  fox2026 ∷
  house2026 ∷
  amyZoom ∷
  burisch2006 ∷
  burisch2007 ∷
  dick1977 ∷
  deutsch1995 ∷
  deutsch2002 ∷
  bem2011 ∷
  cornellBem2010 ∷
  radin2004 ∷
  bemMeta2015 ∷ []

sourceLength : List LinkedSource → Nat
sourceLength [] = zero
sourceLength (_ ∷ xs) = suc (sourceLength xs)

sourceFamilyCount : sourceLength allSurroundingSources ≡ 42
sourceFamilyCount = refl

-- Named HAL5-only pointers not promoted: government labs at Wright
-- Patterson and RIASS, Searl construction, Hutchison anomalous effects,
-- Poher's alleged 2015 NASA test, Morningstar's alleged 7 percent loss,
-- TR3B aerospace vehicle, Modanese Wikipedia deletion.
data BibliographyCreatesExperimentalReplication : Set where
data OriginalPatentCreatesCausalGravityProof : Set where
data UnavailableOfficialFileProvesSecrecy : Set where

bibliographyCannotProveReplication : BibliographyCreatesExperimentalReplication → ⊥
bibliographyCannotProveReplication ()
patentCannotProveGravity : OriginalPatentCreatesCausalGravityProof → ⊥
patentCannotProveGravity ()
missingFileCannotProveSecrecy : UnavailableOfficialFileProvesSecrecy → ⊥
missingFileCannotProveSecrecy ()
