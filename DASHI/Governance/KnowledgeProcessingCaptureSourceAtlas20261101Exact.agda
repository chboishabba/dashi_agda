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

whiteHouseMeeting : SourceReceipt
whiteHouseMeeting = sourceReceipt
  "The White House" "President Trump Participates in a Meeting and Luncheon on Super Intelligence"
  "2026-09-29"
  "https://www.whitehouse.gov/videos/president-trump-participates-in-a-meeting-and-luncheon-on-super-intelligence/"
  governmentInstrument
  "Original White House event documents direct executive meeting with leading AI-industry participants; compare published accord and statements."
  "Meeting presence != proof of improper influence, adopted regulation or government operational control."

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

------------------------------------------------------------------------
-- Followthrough 2026-11-01: first-person regulatory proposal, same-object
-- compute financing, preceding Project 2025 policy, measured vulnerability
-- disclosure baseline, and Epstein/Black AI research evidence.
------------------------------------------------------------------------

darioPolicyJune2026 : SourceReceipt
darioPolicyJune2026 = sourceReceipt
  "Dario Amodei" "Policy on the AI Exponential"
  "2026-06" "https://darioamodei.com/post/policy-on-the-ai-exponential"
  attributedAuthor
  "Explicitly asks for mandatory external frontier-model tests and scoped government power to block/reverse unsafe deployments; discusses protection against state and corporate autocracy and AI parity for citizens in adverse proceedings."
  "Authored policy proposal != enacted regulation; advocating it != evidence that cyber incidents were fabricated or that entrants were intentionally excluded."

anthropicRegulatoryImplementation : SourceReceipt
anthropicRegulatoryImplementation = sourceReceipt
  "Anthropic" "Our compliance framework for California SB 53"
  "2025-12-19"
  "https://www.anthropic.com/news/compliance-framework-SB53"
  firstPartyIssuer
  "Anthropic says it advocated for federal rules and endorsed California transparency law; its existing safety procedures became compliance baseline."
  "Corporate advocacy/first-party account != measured market capture; small-company exemptions and provenance of each enacted clause must remain visible."

anthropicSECRegistration : SourceReceipt
anthropicSECRegistration = sourceReceipt
  "Anthropic, PBC / US SEC archive" "Form S-1 amended draft registration statement"
  "2026-09-03"
  "https://www.sec.gov/Archives/edgar/data/2130357/000162827926001111/filename1.htm"
  firstPartyIssuer
  "Six months to June 2026 company-reported operations +USD3.929bn, investing -USD17.181bn, financing +USD110.774bn; compute commitments generally payable regardless of use or revenue; material partner-provided/facilitated credit."
  "Operating cash != free cash; contractual compute spending != all currently due; source reported operating profitability != sustainable terminal risk-adjusted recovery."

openAIFiveYearCashProjection : SourceReceipt
openAIFiveYearCashProjection = sourceReceipt
  "Reuters / Financial Times, citing OpenAI company investor presentation"
  "OpenAI forecasts cash burn near USD278bn by 2030"
  "2026-09-18"
  "https://www.investing.com/news/economy-news/openai-expects-to-burn-through-almost-280-billion-by-2030-ft-reports-4907970"
  secondaryContext
  "Secondary report of OpenAI forecast: cumulative negative free cash flow USD278bn for 2026-2030, infrastructure spending projection USD856bn, cumulative revenue forecast USD840bn."
  "Forecast is not realised failure, enacted bailout or independently acquired original investor presentation."

anthropicLobbyingSecondary : SourceReceipt
anthropicLobbyingSecondary = sourceReceipt
  "Maria Curi / Axios" "Anthropic ramps up lobbying spending amid AI policy fights"
  "2026-07-21"
  "https://www.axios.com/2026/07/21/anthropic-ramps-up-lobbying-spending-ai-policy-fights"
  secondaryContext
  "Federal disclosure-based report: more than USD3.5m Anthropic lobbying in first half 2026 versus USD3.1m in 2025, including cybersecurity, model standards, procurement and export controls."
  "Lobbying spending != causal efficacy; retrieve exact original filings and post-policy differential costs for promotion."

heritagePolicy2025Defense : SourceReceipt
heritagePolicy2025Defense = sourceReceipt
  "Christopher Miller; Paul Dans and Steven Groves (eds.); Heritage Foundation"
  "Mandate for Leadership: The Conservative Promise, Dept of Defense, print p106"
  "2023"
  "https://static.heritage.org/project2025/2025_MandateForLeadership_FULL.pdf"
  attributedAuthor
  "Printed page 106 proposes expanding DoD machine-learning/AI processing of public and classified intelligence and integrated cyber operations."
  "Proposed 2023 policy != implemented 2026 rule; evidence of programme origin != private company selection."

heritagePolicy2025Trade : SourceReceipt
heritagePolicy2025Trade = sourceReceipt
  "Peter Navarro; Paul Dans and Steven Groves (eds.); Heritage Foundation"
  "Mandate for Leadership: The Conservative Promise, trade chapter, print p790"
  "2023"
  "https://static.heritage.org/project2025/2025_MandateForLeadership_FULL.pdf"
  attributedAuthor
  "Printed page 790 recommends DHS/DOJ contracting with US-owned AI firms to detect and disrupt specified social-media influence networks and funding."
  "Proposed procurement != resulting award, operational behaviour or legitimate targeting of specific groups."

octoberCveVolumeSecondary : SourceReceipt
octoberCveVolumeSecondary = sourceReceipt
  "Bryant Eadon / Balance Bits Consulting"
  "Black October 2026: the month the CVE count broke"
  "2026-10-28"
  "https://www.balancebitsconsulting.com/insights/black-october-2026-the-month-the-cve-count-broke"
  secondaryContext
  "Reproducible stated 1-27 Oct 2026 baseline: 14,514 published CVE records and 30 CISA known-exploited additions through Oct 27; denominator and censoring stated."
  "Published CVEs != exploited in the wild != AI-discovered != artificially induced for a regulatory narrative."

goertzelEpsteinReporting : SourceReceipt
goertzelEpsteinReporting = sourceReceipt
  "Connor Mycroft / South China Morning Post"
  "Epstein funded AI pioneer, helped him get HKD8.9m government grants"
  "2026-02-16"
  "https://www.scmp.com/news/hong-kong/society/article/3343645/epstein-funded-ai-pioneer-helped-him-get-hk89-million-hong-kong-government-grants"
  secondaryContext
  "Journalistic review of roughly 800 pages of original Epstein records describes at least USD113k OpenCog support during 2010-2015 and grant-brokerage claims."
  "Historical support or brokerage != present-day AI industry command, unified programme, or wrongdoing by recipients."

humanityPlusBlackDraft : SourceReceipt
humanityPlusBlackDraft = sourceReceipt
  "DOJ EFTA00587395 (original release); third-party text mirrors"
  "Bracketed draft letter for Humanity+ / Ben Goertzel, proposed Leon Black / family foundation donation"
  "2014-12 (incomplete draft)"
  "https://www.justice.gov/epstein/files/DataSet%209/EFTA00587395.pdf"
  secondaryContext
  "DOJ indexed EFTA00587395, transcribed draft letter describes USD300k proposed AI cognitive-architecture support with unfilled author/foundation variants and transfer language."
  "Unsigned bracketed draft != bank-settlement confirmation; DOJ release != independent endorsement of embedded facts."

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
