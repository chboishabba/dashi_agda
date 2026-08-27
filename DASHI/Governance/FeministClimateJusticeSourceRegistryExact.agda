module DASHI.Governance.FeministClimateJusticeSourceRegistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- FEMINIST ECONOMICS / CLIMATE-JUSTICE SOURCE REGISTRY
--
-- Source roles are bounded.  A citation supplies provenance for a conceptual or
-- empirical interpretation; it does not transfer authorship of DASHI's finite
-- countermodels or generic nonfactorability theorems to the cited author.
--
-- No DOI is invented.  Books and DOI-less articles use verified ISBNs or stable
-- institutional handles instead.
------------------------------------------------------------------------

record SourceReference : Set where
  constructor sourceReference
  field
    authors : String
    title : String
    venue : String
    year : Nat
    identifierKind : String
    identifier : String
    sourceClass : String
    boundedRole : String

open SourceReference public

power2004 : SourceReference
power2004 = sourceReference
  "Marilyn Power"
  "Social Provisioning as a Starting Point for Feminist Economics"
  "Feminist Economics 10(3):3-19"
  2004
  "DOI"
  "10.1080/1354570042000267608"
  "peer-reviewed methodological article"
  "owns the social-provisioning methodological vocabulary: care/unpaid labour, wellbeing, economic-political-social processes and power relations, ethical goals, and interrogation of class/race-ethnicity/other differences; does not endorse DASHI's particular formal carrier"

waring1988 : SourceReference
waring1988 = sourceReference
  "Marilyn Waring"
  "If Women Counted: A New Feminist Economics"
  "Harper & Row, San Francisco"
  1988
  "ISBN"
  "9780062509338"
  "scholarly book / feminist economics"
  "source for critique of national-accounting production boundaries and exclusion of unpaid household/care work from core economic valuation; no numerical unpaid-work estimate is encoded here"

saundersDalziel2017 : SourceReference
saundersDalziel2017 = sourceReference
  "Caroline Saunders; Paul Dalziel"
  "Twenty-Five Years of Counting for Nothing: Waring's Critique of National Accounts"
  "Feminist Economics 23(2):200-218"
  2017
  "DOI"
  "10.1080/13545701.2016.1178854"
  "peer-reviewed historical/methodological reassessment"
  "corroborates Waring's challenge to the national-accounting framework, including exclusion of unpaid household work and environmental impacts from core statistics"

macGregor2010 : SourceReference
macGregor2010 = sourceReference
  "Sherilyn MacGregor"
  "'Gender and climate change': from impacts to discourses"
  "Journal of the Indian Ocean Region 6(2):223-238"
  2010
  "DOI"
  "10.1080/19480881.2010.536669"
  "peer-reviewed feminist climate-politics article"
  "source for critique of an unnecessarily narrow fixation on material/measurable gendered climate impacts and passive-victim framing; motivates discourse/observer audit without rejecting measurement or impact research"

macGregor2014 : SourceReference
macGregor2014 = sourceReference
  "Sherilyn MacGregor"
  "Only Resist: Feminist Ecological Citizenship and the Post-politics of Climate Change"
  "Hypatia 29(3):617-633"
  2014
  "DOI"
  "10.1111/hypa.12065"
  "peer-reviewed feminist political-theory article"
  "source for the post-political critique of replacing democratic public debate with expert administration and individual behaviour change; does not imply all expertise or administration is illegitimate"

sultana2022 : SourceReference
sultana2022 = sourceReference
  "Farhana Sultana"
  "The Unbearable Heaviness of Climate Coloniality"
  "Political Geography 99:102638"
  2022
  "DOI"
  "10.1016/j.polgeo.2022.102638"
  "peer-reviewed critical climate-justice article"
  "source for climate-coloniality framing of uneven vulnerability, colonial dispossession, racial capitalism and climate debt; DASHI uses this to motivate separate responsibility and burden coordinates, not a universal scalar blame score"

carterHoward2020 : SourceReference
carterHoward2020 = sourceReference
  "George Carter; Elise Howard"
  "Pacific women in climate change negotiations"
  "Small States & Territories 3(2):303-318"
  2020
  "ANU repository handle"
  "http://hdl.handle.net/1885/262370"
  "peer-reviewed qualitative climate-negotiation study"
  "source for underacknowledged Pacific women's leadership as technical negotiators and coalition coordinators despite lower visibility as heads of delegation; no DOI asserted"

alstonFullerKwarney2023 : SourceReference
alstonFullerKwarney2023 = sourceReference
  "Margaret Alston; Sascha Fuller; Nikita Kwarney"
  "Women and climate change in Vanuatu, Pacific Islands Region"
  "Gender, Place & Culture 32(1):83-104"
  2023
  "DOI"
  "10.1080/0966369X.2023.2229530"
  "peer-reviewed qualitative empirical study"
  "source for gendered and situated climate impacts, food-production/food-security burdens, and women's desire to participate in international climate conversations; online publication 2023, volume issue publication 2025"

yusoff2018 : SourceReference
yusoff2018 = sourceReference
  "Kathryn Yusoff"
  "A Billion Black Anthropocenes or None"
  "University of Minnesota Press, Forerunners: Ideas First"
  2018
  "ISBN (paperback)"
  "9781517907532"
  "scholarly monograph"
  "source for historically situated critique of geology, extraction, colonialism, slavery, race and Anthropocene origin stories; does not establish that every scientific category is invalid or that planetary-boundary science is definitionally racist"

maathai2004 : SourceReference
maathai2004 = sourceReference
  "Wangari Maathai"
  "Nobel Lecture"
  "Nobel Peace Prize 2004, Nobel Foundation"
  2004
  "stable institutional source"
  "NobelPrize.org Wangari Maathai Nobel Lecture"
  "primary public lecture / movement testimony"
  "source for Green Belt Movement's response to needs identified by rural women and later linkage of ecological action with governance and democratic organisation; not a controlled causal evaluation"

record FeministClimateSourceBoundary : Set where
  constructor feministClimateSourceBoundary
  field
    sourceCitationTransfersTheoremAuthorship : Bool
    sourceCitationTransfersTheoremAuthorshipIsFalse :
      sourceCitationTransfersTheoremAuthorship ≡ false
    qualitativeEvidenceIsUniversalPointwiseLaw : Bool
    qualitativeEvidenceIsUniversalPointwiseLawIsFalse :
      qualitativeEvidenceIsUniversalPointwiseLaw ≡ false
    criticalCategoryAuditMeansScientificInvalidity : Bool
    criticalCategoryAuditMeansScientificInvalidityIsFalse :
      criticalCategoryAuditMeansScientificInvalidity ≡ false
    movementTestimonyIsControlledCausalEvaluation : Bool
    movementTestimonyIsControlledCausalEvaluationIsFalse :
      movementTestimonyIsControlledCausalEvaluation ≡ false

canonicalFeministClimateSourceBoundary : FeministClimateSourceBoundary
canonicalFeministClimateSourceBoundary =
  feministClimateSourceBoundary false refl false refl false refl false refl
