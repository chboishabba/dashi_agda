module DASHI.Culture.AmyEskridgeVideoOmittedOriginalResearchWeldExact where

-- Source-attributed extension for source families named on Amy Eskridge's
-- original 35-page HAL5 talk but omitted or paraphrased in the 2026 Be
-- Inspired edited video. Each source's author, venue, year and canonical
-- document reference are retained without attributing their results to Amy.
-- This is provenance acquisition, not successful experimental certification.
--
-- Amy Eskridge, HAL5, 2018-12-06:
-- https://www.hal5.org/PDF/HAL5-Dec2018-Talk-AntiGravity.pdf
-- Sources: Sandberg (1987), Datta/Yin/Vargas (STAIF-2004 p240),
-- Murad/Brandenburg (JMESS 2020), Hathaway (MS&T 2009),
-- Modanese/Fontana (STAIF-2004 p239), Paul March (p241).
-- Sources were inspected to the extents recorded, not all independently
-- replicated. See Docs/SourceAttributionPolicy.md.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)
import DASHI.Core.AttributedSourceCore as A
import DASHI.Culture.AmyEskridgeVideoHAL5AllSlidesExact as Slides
import DASHI.Culture.AmyEskridgeVideoClaimAttributionLedgerExact as Video

data ReadExtent : Set where
  originalPaperRead : ReadExtent
  participantPaperRead : ReadExtent
  conferenceAbstractRead : ReadExtent
  archiveReportRead : ReadExtent
  archivalReprintRead : ReadExtent
  bibliographyLocatorOnly : ReadExtent

data VideoRelation : Set where
  videoOmits : VideoRelation
  videoIncludes : Video.RawAttributedClaim → VideoRelation

record SurroundingPrimary : Set where
  constructor surrounding-primary
  field
    originalSource : A.AttributedSource
    originalReadExtent : ReadExtent
    originalHAL5Page : Slides.HAL5Slide
    videoRelation : VideoRelation
    strictlyPaid : String
    independentUnpaid : String
open SurroundingPrimary public

searlSandberg1987 : SurroundingPrimary
searlSandberg1987 = surrounding-primary
  (A.mkNoDOISource
    "S. Gunnar Sandberg"
    "The Searl Effect & the Searl-Effect Generator"
    "Sandberg report, June 17 1987"
    "1987"
    "https://toba60.com/wp-content/uploads/2020/07/John-Searl-The-Searl-Effect-The-Searl-Effect-Generator.pdf"
    A.archivalSource
    "Sandberg reconstructs Searl work from interviews since 1982, noting historical apparatus and experimental documentation reportedly destroyed in 1983"
    A.publicAttribution)
  archiveReportRead
  Slides.deck16
  (videoIncludes Video.claim030)
  "Sandberg reconstructs Searl work from interviews since 1982, noting historical apparatus and experimental documentation reportedly destroyed in 1983"
  "Original 1946–1952 experimental protocols, independent replication or validation of levitation"

dattaYinVargas2004 : SurroundingPrimary
dattaYinVargas2004 = surrounding-primary
  (A.mkNoDOISource
    "Timir Datta; Ming Yin; Jose Vargas"
    "A Gravitational Experiment Involving Inhomogeneous Electric Fields"
    "STAIF-2004 Abstract Book, page 240; NASA GSFC-hosted conference volume"
    "2004"
    "https://science.gsfc.nasa.gov/attic/ants/documents/staif2004spacepower.pdf"
    A.academicArticleSource
    "Authors report preliminary correlations of inhomogeneous applied electric fields with force, including a claimed mass-scaling signature"
    A.publicAttribution)
  conferenceAbstractRead
  Slides.deck27
  videoOmits
  "Authors report preliminary correlations of inhomogeneous applied electric fields with force, including a claimed mass-scaling signature"
  "Full data, charge/ionic/EHD controls, gravitational interpretation and independent reproduction"

morningstar2020 : SurroundingPrimary
morningstar2020 = surrounding-primary
  (A.mkNoDOISource
    "P. A. Murad; J. E. Brandenburg"
    "A Nonlinear Electromagnetic Device and Potential Explanations"
    "Journal of Multidisciplinary Engineering Science Studies 6(12), 3587 ff.; document JMESSP13420694"
    "2020"
    "https://www.jmess.org/wp-content/uploads/2020/12/JMESSP13420694.pdf"
    A.academicArticleSource
    "Authors describe a 190-pound Energy Box and report 7% steady-state and 20% transient apparent-weight reductions; explicitly report NO self-acceleration"
    A.publicAttribution)
  originalPaperRead
  Slides.deck30
  videoOmits
  "Authors describe a 190-pound Energy Box and report 7% steady-state and 20% transient apparent-weight reductions; explicitly report NO self-acceleration"
  "Raw instrument/scale force calibration, rpm-control and independently repeated gravitational effect"

hutchisonHathaway2009 : SurroundingPrimary
hutchisonHathaway2009 = surrounding-primary
  (A.mkNoDOISource
    "G. Hathaway"
    "Hutchison Effect Metal Samples: Description and Analysis"
    "Materials Science and Technology (MS&T) 2009, pp. 667–678"
    "2009"
    "https://ia902306.us.archive.org/1/items/g-hathaway-hutchison-metal-analysis/G.%20Hathaway%20Hutchison%20Metal%20Analysis%20-%20cp2009mst0667%20ASM%20int.%20-%20Enrico.pdf"
    A.academicArticleSource
    "Longtime participant documents apparatus/media/sample descriptions and explicitly says repeatability/controllability were not achieved by him"
    A.publicAttribution)
  participantPaperRead
  Slides.deck22
  videoOmits
  "Longtime participant documents apparatus/media/sample descriptions and explicitly says repeatability/controllability were not achieved by him"
  "Independent blind replication; full laboratory time series and unattended controls"

hutchisonLADS1990 : SurroundingPrimary
hutchisonLADS1990 = surrounding-primary
  (A.mkNoDOISource
    "George D. Hathaway"
    "The Hutchison Effect: A Lift and Disruption System"
    "New Energy Technology 1990 article reproduced in historical archive"
    "1990"
    "https://gbppr.net/hutchinson/The-Hutchison-File.pdf"
    A.archivalSource
    "Hathaway's contemporary Pharos / LADS presentation is an involved source account, not external verification"
    A.publicAttribution)
  archivalReprintRead
  Slides.deck22
  videoOmits
  "Hathaway's contemporary Pharos / LADS presentation is an involved source account, not external verification"
  "Exact document edition, continuous filmed apparatus and independently controlled result"

modaneseFontana2004 : SurroundingPrimary
modaneseFontana2004 = surrounding-primary
  (A.mkNoDOISource
    "Giovanni Modanese; Giorgio Fontana"
    "Effect of the Vacuum Energy Density on Gravitation Propagation"
    "STAIF-2004 Abstract Book, p. 239; NASA GSFC-hosted conference volume"
    "2004"
    "https://science.gsfc.nasa.gov/attic/ants/documents/staif2004spacepower.pdf"
    A.academicArticleSource
    "Authors discuss conditional vacuum-energy/cosmological-constant effects on model gravitational propagation"
    A.publicAttribution)
  conferenceAbstractRead
  Slides.deck28
  (videoIncludes Video.claim046)
  "Authors discuss conditional vacuum-energy/cosmological-constant effects on model gravitational propagation"
  "Exact nonperturbative derivation, physical stress-energy production, positive experimental verification"

paulMarch2004 : SurroundingPrimary
paulMarch2004 = surrounding-primary
  (A.mkNoDOISource
    "Paul March"
    "Woodward Effect Experimental Verifications"
    "STAIF-2004 Abstract Book, p. 241; NASA GSFC-hosted conference volume"
    "2004"
    "https://science.gsfc.nasa.gov/attic/ants/documents/staif2004spacepower.pdf"
    A.academicArticleSource
    "Abstract announces/claims initial Woodward-effect tests and MHD-like force rectification"
    A.publicAttribution)
  conferenceAbstractRead
  Slides.deck23
  (videoIncludes Video.claim051)
  "Abstract announces/claims initial Woodward-effect tests and MHD-like force rectification"
  "Actual complete results/uncertainty and controls; a 2004 programme abstract is not a passed replication"

morningstarAIAA2012 : SurroundingPrimary
morningstarAIAA2012 = surrounding-primary
  (A.mkNoDOISource
    "P. A. Murad; M. J. Boardman; J. E. Brandenburg; J. McCabe; W. Mitzen"
    "The Morningstar Energy Box"
    "AIAA-2012-0998, 50th AIAA Aerospace Sciences Meeting, 9–12 Jan 2012"
    "2012"
    "https://kepleraerospace.com/wp-content/uploads/2023/03/NASA-NSPIRES-DraftProposal.pdf"
    A.archivalSource
    "2014 Morningstar-authored proposal bibliography identifies earlier AIAA-2012-0998 title and speaker group"
    A.publicAttribution)
  bibliographyLocatorOnly
  Slides.deck30
  videoOmits
  "2014 Morningstar-authored proposal bibliography identifies earlier AIAA-2012-0998 title and speaker group"
  "Actual original AIAA paper text, measurement tables, public test data and quantitative third-party replication"

omittedAndAdditionalOriginalSources : List SurroundingPrimary
omittedAndAdditionalOriginalSources =
  searlSandberg1987 ∷
  dattaYinVargas2004 ∷
  morningstar2020 ∷
  hutchisonHathaway2009 ∷
  hutchisonLADS1990 ∷
  modaneseFontana2004 ∷
  paulMarch2004 ∷
  morningstarAIAA2012 ∷ []

countOriginalSources : List SurroundingPrimary → Nat
countOriginalSources [] = zero
countOriginalSources (_ ∷ xs) = suc (countOriginalSources xs)

allAdditionalSourcesIndexed : countOriginalSources omittedAndAdditionalOriginalSources ≡ 8
allAdditionalSourcesIndexed = refl

-- The 2020 Murad/Brandenburg article expressly reports no successful
-- self-acceleration, despite reported load change; first-person measurements
-- cannot be turned into a demonstrated gravitational source by citation.
data ParticipantPaperProvesIndependentReplication : Set where
data NASAHostedAbstractMeansNASATested : Set where
data UnlocatableOriginalReportProvesSeizure : Set where

notIndependentByParticipantAccount : ParticipantPaperProvesIndependentReplication → ⊥
notIndependentByParticipantAccount ()
notNASATestedByHostingAbstract : NASAHostedAbstractMeansNASATested → ⊥
notNASATestedByHostingAbstract ()
notSeizureFromOriginalMissing : UnlocatableOriginalReportProvesSeizure → ⊥
notSeizureFromOriginalMissing ()
