module DASHI.Governance.KnowledgeProcessingCaptureSourceAtlas20261101Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RECOVERABLE ORIGINAL SOURCE / CLAIM / PROMOTION ATLAS
-- Repository-native source-carrier synthesis: not empirical verification.
-- The bibliography, dates, accounting objects, quotations and legal status
-- must be checked against the linked originals before any external use.
-- Source reporting != causal effects != motive != proof of covert control.
------------------------------------------------------------------------

data EvidenceKind : Set where
  firstPartyIssuer  governmentInstrument  securityMaintainer
    attributedAuthor  secondaryContext  negativeControl : EvidenceKind

record SourceReceipt : Set where
  constructor sourceReceipt
  field
    authorOrIssuer : String
    title : String
    publishedOrObserved : String
    originalURL : String
    kind : EvidenceKind
    supportedScope : String
    unlicensedPromotion : String
open SourceReceipt public

skHynixQ3 : SourceReceipt
skHynixQ3 = sourceReceipt
  "SK hynix" "SK hynix Announces 3Q26 Financial Results"
  "2026-10-28" "https://news.skhynix.com/en/q3-2026-business-results/"
  firstPartyIssuer
  "Company reports 80 percent Q3 2026 operating margin; high-value HBM and server memory sales."
  "Supplier margin != frontier-lab terminal profit; preliminary issuer statements != independent verification."

micronFY26 : SourceReceipt
micronFY26 = sourceReceipt
  "Micron Technology" "Reports Record Fiscal Fourth-Quarter and Full-Year 2026 Results"
  "2026-09" "https://investors.micron.com/news/press-release/2026/Micron-Technology-Inc--Reports-Record-Fiscal-Fourth-Quarter-and-Full-Year-2026-Results/default.aspx"
  firstPartyIssuer
  "FY2026 consolidated 74.6 percent operating margin; Q4 core-data-center segment 85 percent operating margin."
  "Segment gross, operating and consolidated margins are different denominators; none proves a lab's insolvency."

palantirArmy : SourceReceipt
palantirArmy = sourceReceipt
  "US Army Public Affairs" "US Army Awards Enterprise Service Agreement"
  "2025-07-31"
  "https://www.army.mil/article-amp/287506/u_s_army_awards_enterprise_service_agreement_to_enhance_military_readiness_and_drive_operational_efficiency"
  governmentInstrument
  "Consolidates 75 contracts into an enterprise framework with up-to-USD10B 10-year purchasing ceiling."
  "Ceiling != obligation != revenue != demonstrated irreversibility or vendor indispensability."

palantirQ2 : SourceReceipt
palantirQ2 = sourceReceipt
  "Palantir Technologies" "Q2 2026 Financial Results"
  "2026-08"
  "https://investors.palantir.com/news-details/2026/Palantir-Reports"
  firstPartyIssuer
  "Q2 US government revenue USD809M and US commercial revenue USD764M as company reported."
  "Contractual customer reliance != unavoidable critical-service dependence."

usNSPM : SourceReceipt
usNSPM = sourceReceipt
  "White House" "AI in the National Security Enterprise, presidential memorandum fact sheet"
  "2026-06-05"
  "https://www.whitehouse.gov/fact-sheets/2026/06/fact-sheet-president-donald-j-trump-signs-historic-directive-on-ai-in-the-national-security-enterprise/"
  governmentInstrument
  "Calls for frontier multi-vendor access, high-security compute and government approval before vendor impairment of defence AI systems."
  "Operational security mandate != lab acquisition, nationalisation, exclusive state access or proved capture."

usTerminologyEO : SourceReceipt
usTerminologyEO = sourceReceipt
  "White House" "Inaugurating The Era Of Super Intelligence, Executive Order 14434"
  "2026-09-29"
  "https://www.whitehouse.gov/presidential-actions/2026/09/inaugurating-the-era-of-super-intelligence/"
  governmentInstrument
  "Directs executive-branch use of the term SI for AI, with a statutory-definition proposal process."
  "Renaming AI as SI != technical proof of superhuman general intelligence."

whiteHouseAccord : SourceReceipt
whiteHouseAccord = sourceReceipt
  "Participating companies / White House"
  "White House Accord on Super Intelligence"
  "2026-09-29"
  "https://www.presidency.ucsb.edu/documents/white-house-accord-super-intelligence"
  governmentInstrument
  "Voluntary company control, evaluation and board-oversight commitments; potential later codification."
  "Shared governance meeting or draft standard != enacted compulsory law or proven industry capture."

phpMaintainer : SourceReceipt
phpMaintainer = sourceReceipt
  "PHP Foundation" "Today's PHP Security Release, and How We're Strengthening PHP Security"
  "2026-10-21"
  "https://thephp.foundation/blog/2026/10/21/todays-php-security-release-and-how-were-strengthening-php-security/"
  securityMaintainer
  "Two real CVE vulnerabilities, years-old root cause, multi-party independent discovery, premature leak and expedited patch."
  "Disclosure disruption != intentional manufacture of an AI-doom narrative or coordinated lobbying."

wizPHP2Shell : SourceReceipt
wizPHP2Shell = sourceReceipt
  "Sagi Tzadik; Shir Tamari; Nir Ohfeld; Tomer Schwartz / Wiz"
  "PHP2Shell: AI uncovers critical RCE vulnerabilities"
  "2026-10-21" "https://www.wiz.io/blog/php2shell-php-rce"
  firstPartyIssuer
  "Wiz's discovery/confirmation/testing assertions and two CVE descriptions."
  "Vendor marketing wording != independent measurement of universe-wide exposure or successful exploitation."

html2shellNegative : SourceReceipt
html2shellNegative = sourceReceipt
  "Maarten Schenk / Lead Stories"
  "Fact Check: JOKE CVE-2026-42069 HTML2Shell"
  "2026-10-25"
  "https://leadstories.com/hoax-alert/2026/10/fact-check-cve-2026-42069-html2shell-vulnerability.html"
  negativeControl
  "Viral HTML2Shell claim was a joke misusing an unrelated CVE, not a second corroborated PHP incident."
  "Memetic recurrence != independent technical evidence."

thielWolfeOriginal : SourceReceipt
thielWolfeOriginal = sourceReceipt
  "Peter Thiel; Sam Wolfe"
  "Voyages to the End of the World, First Things"
  "2025-10-01"
  "https://firstthings.com/voyages-to-the-end-of-the-world/"
  attributedAuthor
  "Authors discuss Bacon, technology, religious/apocalyptic interpretations and the Antichrist."
  "Thiel's authored theology != the ideology or private intentions of every lab or Commanding Heights author."

thielWolfeLater : SourceReceipt
thielWolfeLater = sourceReceipt
  "Peter Thiel; Sam Wolfe"
  "The Pope and the Antichrist, First Things"
  "2026-07-15"
  "https://firstthings.com/the-pope-and-the-antichrist/"
  attributedAuthor
  "Thiel's coauthored account of his Rome lectures and Catholic response."
  "His public religious doctrine != proof of covert cybersecurity/national-security coordination."

commandingHeights : SourceReceipt
commandingHeights = sourceReceipt
  "Will Manidis; Joe Roberts"
  "The Commanding Heights"
  "2026-10-29" "https://commanding-heights.com/"
  attributedAuthor
  "Authors' forecasting thesis on scarce controllable distribution routes and sovereign AI frontier."
  "Author rhetoric != authored Thiel doctrine, endorsement by named feedback contributors, or observed sovereign capture."

-- An original primary statement is a receipt for what the named original
-- says, not a receipt for the correctness of every empirical prediction.
record AttributionBoundary : Set where
  constructor attributionBoundary
  field
    commonFundingProvesCommonDirection : Bool
    sharedApocalypseLanguageProvesSharedDoctrine : Bool
    sameDisclosureNewsProvesCoordinatedAction : Bool
    executiveAIToSIRenameProvesTechnicalSuperintelligence : Bool
open AttributionBoundary public

canonicalNoPromotion : AttributionBoundary
canonicalNoPromotion = attributionBoundary false false false false
