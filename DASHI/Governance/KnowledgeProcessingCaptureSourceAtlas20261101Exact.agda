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

thielOriginal2009 : SourceReceipt
thielOriginal2009 = sourceReceipt
  "Peter Thiel" "The Education of a Libertarian, Cato Unbound"
  "2009-04-13"
  "https://www.cato-unbound.org/2009/04/13/peter-thiel/education-libertarian/"
  attributedAuthor
  "Author rejects compatibility of freedom and democracy, seeks technology-enabled escape from conventional politics, and explicitly calls himself libertarian."
  "Authored anti-democratic/libertarian argument != demonstration of a coordinated actor-network conspiracy; compare actual investments, state contracts and policy consequences."

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

------------------------------------------------------------------------
-- ORIGINAL REGULATOR + CURRENT PUBLIC S-1 AS OF 2026-11-01.
-- This adds genuine primary-source warnings of financial contagion, not a
-- finding that public intervention, nationalisation or vendor misconduct
-- has already happened.
------------------------------------------------------------------------

rbaOct2026FinancialStability : SourceReceipt
rbaOct2026FinancialStability = sourceReceipt
  "Reserve Bank of Australia"
  "Financial Stability Review, October 2026, The Global Macro-financial Environment: Funding the AI investment boom"
  "2026-10"
  "https://www.rba.gov.au/publications/fsr/2026/oct/the-global-macro-financial-environment.html"
  governmentInstrument
  "Primary central-bank financial-stability assessment explicitly notes opaque AI capital links, vendor financing/circular arrangements, growing debt exposure and risks from disappointed AI investment returns."
  "Financial-stability vulnerability != recorded public rescue, monetary bailout, forced acquisition or proved irrecoverable loss; bank's risk analysis is not a causal identification of a particular actor's intent."

rbaOct2026FinancialAssessment : SourceReceipt
rbaOct2026FinancialAssessment = sourceReceipt
  "Reserve Bank of Australia"
  "Financial Stability Review, October 2026, Financial Stability Assessment"
  "2026-10"
  "https://www.rba.gov.au/publications/fsr/2026/oct/financial-stability-assessment.html"
  governmentInstrument
  "Official RBA risk assessment states AI profitability reappraisal could sharply reprice markets, exacerbated by market concentration, leverage and opacity, and that vulnerability spillovers could grow."
  "Could pose systemic risk != has already crossed public-intervention threshold."

anthropicCurrentPublicS1 : SourceReceipt
anthropicCurrentPublicS1 = sourceReceipt
  "Anthropic, PBC; U.S. Securities and Exchange Commission"
  "Anthropic Form S-1, SEC accession 0001628280-26-067168"
  "2026-10-26"
  "https://www.sec.gov/Archives/edgar/data/2130357/000162828026067168/anthropicpbc-sx1.htm"
  firstPartyIssuer
  "Latest publicly filed S-1 available for this cut: first-half 2026 operating cash +USD3,929m, investing cash -USD17,181m, financing cash +USD110,774m; significant fixed compute purchase commitments independent of utilisation; 2026 year-to-date customer and platform dependence described."
  "Positive cash from operations != terminal independently funded cash; cash raised != revenue; disclosed multi-year purchase/lease schedule includes some unpriced blanks in preliminary prospectus; externally calculated ~USD637bn partner-specific sums are NOT a literal fully quantified issuer total here."

anthropicCurrentSECIndex : SourceReceipt
anthropicCurrentSECIndex = sourceReceipt
  "U.S. Securities and Exchange Commission"
  "Form S-1 filing index 0001628280-26-067168"
  "2026-10-26"
  "https://www.sec.gov/Archives/edgar/data/2130357/000162828026067168/0001628280-26-067168-index.htm"
  governmentInstrument
  "Primary filing/index fixes October 26 filing date, accession and current public document identity, superseding a September 3 confidential draft."
  "Prior draft and later public S-1 are different temporal versions; do not promote September-specific figures when October-specific amended statements supersede them."

------------------------------------------------------------------------
-- 26-30 October 2026 new market/procurement and Thiel first-person roots.
------------------------------------------------------------------------

fedSeptemberHike2026 : SourceReceipt
fedSeptemberHike2026 = sourceReceipt
  "U.S. Federal Reserve, FOMC"
  "Federal Reserve issues FOMC statement, 16 September 2026"
  "2026-09-16"
  "https://www.federalreserve.gov/newsevents/pressreleases/monetary20260916a.htm"
  governmentInstrument
  "12-0 FOMC vote raised target funds-rate range 25bp to 3.75-4.00%; official issuer."
  "September increase is not an October rate increase; no statement that debt yields move one-for-one with the target."

fedOctoberHold2026 : SourceReceipt
fedOctoberHold2026 = sourceReceipt
  "U.S. Federal Reserve, FOMC"
  "Federal Reserve issues FOMC statement, 28 October 2026"
  "2026-10-28"
  "https://www.federalreserve.gov/newsevents/pressreleases/monetary20261028a.htm"
  governmentInstrument
  "10-2 vote HELD 3.75-4.00% range; Cook/Hammack dissented preferring a 25bp increase; future rates uncommitted."
  "Dissents do not change the adopted decision; a December hike forecast is not enacted policy."

lsegHyperscalerCredit20261029 : SourceReceipt
lsegHyperscalerCredit20261029 = sourceReceipt
  "Lydia Hamill; Paul Amery; FTSE Russell / LSEG"
  "AI's borrowing boom: What it means for bond indices"
  "2026-10-29"
  "https://www.lseg.com/en/insights/ftse-russell/ais-borrowing-boom-what-it-means-for-bond-indices"
  firstPartyIssuer
  "Index-provider primary data: broad IG issuance USD218.1bn by early Oct 2026 vs USD107.3bn in all 2025; narrower USD fixed-rate index eligible issuance 151.75bn as of 2 Oct; approx USD500bn outstanding end-Aug; Sep30 OAS issuer Microsoft54, Alphabet74, Amazon75, Meta123, Oracle210 bp; group119 vs broad86; Oct21 Oracle CDS331, Amazon80, Microsoft56 bp."
  "Issuance vs outstanding vs benchmark index eligibility differ; OAS vs CDS differ; credit spreads cannot by themselves establish lab default, full AI loss, bailout, legal capture or motive."

reutersOct30EquityRisk : SourceReceipt
reutersOct30EquityRisk = sourceReceipt
  "Reuters / Wall Street close"
  "Wall Street closes sharply lower as AI cash burn fears spark tech selloff"
  "2026-10-30"
  "https://www.reuters.com/business/nasdaq-futures-tumble-amazon-intel-results-deepen-ai-spending-woes-2026-10-30/"
  secondaryContext
  "Nasdaq -2.86pct Oct30, down 7.8pct from Oct6 peak; semiconductor index -7.2pct and S&P500 -1.82pct, with capital-recovery concerns."
  "One bad session does not establish insolvency, the loss attributable solely to AI, or inevitable systemic collapse."

ukMODExclusiveSupplier : SourceReceipt
ukMODExclusiveSupplier = sourceReceipt
  "United Kingdom Ministry of Defence"
  "UK5 Transparency Notice 2025/S 000-083858 / MOD Palantir Enterprise Agreement"
  "2025-12-17"
  "https://www.find-tender.service.gov.uk/Notice/083858-2025"
  governmentInstrument
  "Official direct-award notice states USD-equivalent not needed: GBP240.6m 3-year 2026-29 Palantir contract, technical architecture only Palantir can license/support, with rebuilding, accreditation, retraining and interoperability disruption on substitution."
  "MoD's contemporaneous vendor-specific justification proves stated procurement dependence, not universal technological impossibility or independent adjudication of proportionality."

ukMODOriginalAward : SourceReceipt
ukMODOriginalAward = sourceReceipt
  "United Kingdom Ministry of Defence"
  "UK6 award notice 006344-2026 / MOD Palantir Enterprise Agreement"
  "2026-01-23"
  "https://www.find-tender.service.gov.uk/Notice/006344-2026"
  governmentInstrument
  "Government award notice records GBP240.6m direct award to Palantir Technologies UK Ltd, contracted 2025-12-30, service 2026-04-01 through 2029-03-31."
  "This awarded contract does not prove every Palantir service or other states' procurements are non-substitutable."

ftUkPaymentReconciliation : SourceReceipt
ftUkPaymentReconciliation = sourceReceipt
  "Financial Times / Stotles independently reconciling original MoD spreadsheets"
  "UK defence ministry spent GBP186m more on Palantir than value of public contracts"
  "2026-10-28"
  "https://www.ft.com/content/5c237fb3-23ba-4c1a-9257-fd66b9d42d6c"
  secondaryContext
  "Reporter/independent source comparison GBP282m MoD supplier payments in period versus GBP95.9m published contract notices; >80pct payments from noncompetitive procurement."
  "Payments vs contract award notices differ in legal basis, period, classification and definitions; unexplained publication gap is not proof of corruption or illegal nondisclosure."

thielCowenOriginal2024 : SourceReceipt
thielCowenOriginal2024 = sourceReceipt
  "Tyler Cowen interviews Peter Thiel"
  "Peter Thiel on Political Theology, Conversations with Tyler episode 210"
  "2024-04-17"
  "https://conversationswithtyler.com/episodes/peter-thiel-political-theology/"
  attributedAuthor
  "Primary speaker transcript: Thiel fears safety-motivated one-world totalitarian government; says the katechon/restrainer may mimic or become Antichrist; discusses Girard, Schmitt and AI centralization, return to scale and possible harm from governance."
  "Interview is authored spoken claim, not an agreed policy, proved theological doctrine of other people, or a company action."

thielLecturesAttendeeRecording : SourceReceipt
thielLecturesAttendeeRecording = sourceReceipt
  "The Guardian / attendee-supplied audio, Thiel San Francisco lectures"
  "Inside tech billionaire Peter Thiel's off-the-record lectures about the antichrist"
  "2025-10-10"
  "https://www.theguardian.com/us-news/2025/oct/10/peter-thiel-lectures-antichrist"
  secondaryContext
  "Journalists describe direct attendee recording, confirm spokesperson did not dispute authenticity while correcting a transcription, and identify Girard, Carl Schmitt and Newman in lecture content."
  "Reporter transcript is not independent consent or company endorsement and the cited religious thinkers are not political co-conspirators."

thielRomeAP2026 : SourceReceipt
thielRomeAP2026 = sourceReceipt
  "Associated Press"
  "Thiel brings his Antichrist lectures to the Vatican's doorstep"
  "2026-03"
  "https://apnews.com/article/c3a6c7d2daba501caf8152558ac2d743"
  secondaryContext
  "Journalistic account of Rome four-part lecture and theological/political controversy; Catholic institutions explicitly denied organising/hosting."
  "Near the Vatican != Vatican sponsorship, papal agreement, clandestine religious programme or direct executive influence."

------------------------------------------------------------------------
-- October CDS stress + original philosophical and historical-network leads
------------------------------------------------------------------------

coreweaveCreditReutersOct2026 : SourceReceipt
coreweaveCreditReutersOct2026 = sourceReceipt
  "Reuters, 15-16 October 2026, using LSEG market data"
  "CoreWeave debt stress tests private credit's AI financing boom"
  "2026-10-16"
  "https://www.investing.com/news/stock-market-news/coreweave-bond-rout-tests-market-s-math-on-ai-buildout-4954178"
  secondaryContext
  "Reported CoreWeave USD50bn financing obligations, five-year CDS near 1000-1200bp, and 2031 bond yields near 15-16pct; original Reuters report references LSEG."
  "Credit spreads are time-, bond- and instrument-specific; not a realised default, audited balance sheet sum, or proof of public rescue."

jpmorganCreditOct2026 : SourceReceipt
jpmorganCreditOct2026 = sourceReceipt
  "Justin Biemann / J.P. Morgan Private Bank"
  "Credit markets look for AI's weak links"
  "2026-10-23"
  "https://privatebank.jpmorgan.com/nam/en/insights/markets-and-investing/tmt/credit-markets-look-for-ai-s-weak-links"
  firstPartyIssuer
  "Bank analysis reports investment-grade CDS 50-120bp, infrastructure CDS toward 300bp, financing-dependent borrower above 1100bp; juxtaposes Lehman 2007 below 100bp, 2008 above 1400bp."
  "Analogy is risk-signal comparison, not an identical collateral/counterparty structure or a statistical insolvency forecast."

landFangedNoumenaPublisher : SourceReceipt
landFangedNoumenaPublisher = sourceReceipt
  "Nick Land; Robin Mackay and Ray Brassier (eds.); Urbanomic/Sequence"
  "Fanged Noumena: Collected Writings 1987-2007, ISBN 978-0-9553087-8-9"
  "2011-03"
  "https://www.sequencepress.com/products/fanged-noumena-collected-writings-1987-2007"
  attributedAuthor
  "Original publisher records 2011 collection, intellectual trajectory of Land's accelerationist/CCRU writings."
  "Land's theory is not a documented shared policy of Thiel, Epstein, Anthropic, Roko or the Commanding Heights authors."

rokoBasiliskRetrospective : SourceReceipt
rokoBasiliskRetrospective = sourceReceipt
  "LessWrong editors, describing Roko's 2010 thought experiment"
  "Roko's Basilisk retrospective, LessWrong"
  "2010/retrospective"
  "https://www.lesswrong.com/w/rokos-basilisk"
  secondaryContext
  "A thought experiment about speculative acausal blackmail, heavily disputed and broadly rejected in its original community; discussion ban caused publicity amplification."
  "No observed dangerous agent, genuine blackmail, prophetic information hazard or objective threat to readers is established."

epsteinThielWiredResearch : SourceReceipt
epsteinThielWiredResearch = sourceReceipt
  "WIRED / 2026 DOJ correspondence review"
  "The Tech Elites in the Epstein Files"
  "2026-02"
  "https://www.wired.com/story/epstein-files-tech-elites-gates-thiel-musk/"
  secondaryContext
  "Journalists report repeated 2014-2019 Thiel-Epstein scheduling and direct correspondence, distinct from third-party mere mentions; named 2016 lunch request."
  "Meeting correspondence is not evidence of Epstein's sex offences by any named contact or collective government-tech command."

epsteinThiel2014Correspondence : SourceReceipt
epsteinThiel2014Correspondence = sourceReceipt
  "US DOJ Epstein Library, released email chain"
  "EFTA02587213-EFTA02587214: Epstein-Thiel August 2014 introductions and invitation"
  "2014-08"
  "https://epstein-data.com/EFTA02587213"
  secondaryContext
  "Source-access mirror of original DOJ Bates-identified email chain: Epstein offered introduction to William Burns and invitation to island, with Thiel's NYC timing response."
  "An introduction offer or island invitation is not verified meeting with Burns, travel to island, endorsement or wrongdoing."

coreweaveOriginalRating2026 : SourceReceipt
coreweaveOriginalRating2026 = sourceReceipt
  "S&P Global Ratings"
  "CoreWeave Outlook Revised To Positive; B+ Issuer Rating Affirmed; Notes Rated B"
  "2026-04-09"
  "https://www.spglobal.com/ratings/en/regulatory/article/-/view/type/HTML/id/3543327"
  firstPartyIssuer
  "Rating agency affirms CoreWeave B+ speculative-grade issuer, assigns B unsecured-note rating with specific recovery rating 5 (10-30pct estimated recovery)."
  "Issuer rating, specific unsecured bond rating, secured GPU-backed loans and market CDS are distinct instruments. Recovery for rated notes cannot be silently used as CDS recovery assumption for all liabilities."

coreweaveFINRATradeSnapshot : SourceReceipt
coreweaveFINRATradeSnapshot = sourceReceipt
  "FINRA TRACE as collected by Kilambi Research"
  "CoreWeave fixed income issuer snapshot, bond trade date 2026-10-30"
  "2026-10-31"
  "https://news.kilambi.com/leverage/issuer/coreweave/"
  secondaryContext
  "Secondary retrieval of FINRA trade prints: multiple CoreWeave notes traded below 90 pct of par on Oct30; some near 80 pct; current bond-level issue credit data shown."
  "Illiquid trade prints, holder fund marks and modelled prices are different observations; one last trade does not guarantee executable size or company-wide marginal funding cost."

------------------------------------------------------------------------
-- FIRST-PARTY OFF-BALANCE + SOFTBANK + ED ZITRON ORIGINAL COMMENTARY
-- The formal consumer uses these only as typed observation/argument roots.
------------------------------------------------------------------------

metaSept30LeaseAndCommitments : SourceReceipt
metaSept30LeaseAndCommitments = sourceReceipt
  "Meta Platforms, Inc.; SEC Form 10-Q"
  "Third-quarter 2026 notes: leases and contractual commitments"
  "2026-09-30"
  "https://www.sec.gov/Archives/edgar/data/1326801/000162828026066773/meta-20260930_htm.xml"
  firstPartyIssuer
  "Meta reports USD355.73bn uncommenced leases, USD454.52bn noncancel commitments, USD84.00bn senior notes, 2027 contractual payments USD121.41bn, and additional USD14.72bn contingent purchases; leases commence through 2036."
  "The two future obligation buckets MAY overlap; do not add the categories, call disclosed future rent fraudulent hidden debt, or replace 2027 commitments with 2027 bond maturity."

microsoftFY26LeaseDisclosure : SourceReceipt
microsoftFY26LeaseDisclosure = sourceReceipt
  "Microsoft Corp."
  "Microsoft 2026 Annual Report, Leases"
  "2026-06-30"
  "https://www.microsoft.com/investor/reports/ar26/"
  firstPartyIssuer
  "Annual report gives USD329.1bn datacentre-related leases not yet commenced, potentially conditional, commencing fiscal 2027-2033 and lasting 1-20 years."
  "Unsigned options and commencement conditions are not necessarily unconditional present debt. Do not merge cross-issuer lease totals into a single legally callable loan."

metaHyperionBlueOwlOriginal : SourceReceipt
metaHyperionBlueOwlOriginal = sourceReceipt
  "Meta Platforms Inc."
  "Meta Announces Joint Venture With Blue Owl Capital to Develop Hyperion Data Center"
  "2025-10-21"
  "https://investor.atmeta.com/investor-news/press-release-details/2025/Meta-Announces-Joint-Venture-with-Funds-Managed-by-Blue-Owl-Capital-to-Develop-Hyperion-Data-Center/"
  firstPartyIssuer
  "Blue Owl funds own 80pct and Meta 20pct of JV, ~USD27bn construction budget; Meta will lease completed facility and granted capped conditional residual-value guarantee for first 16 years, linked to nonrenewal/termination; third-party bonds issued."
  "JV project debt is not necessarily consolidated Meta corporate debt; guarantee is conditional and capped, not equivalent to current payable principal; do not infer same-accounting total without full annex."

coreWeaveH1SecCashClock : SourceReceipt
coreWeaveH1SecCashClock = sourceReceipt
  "CoreWeave Inc.; SEC Form 10-Q"
  "Quarter ended 30 June 2026, cash and financing liquidity note"
  "2026-06-30"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000366/crwv-20260630.htm"
  firstPartyIssuer
  "H1 operating cash USD3.663bn, investing outflow USD14.874bn, financing inflow USD13.985bn; USD5.524bn cash and USD10.014bn available debt draws, USD15.553bn company-defined liquidity; USD35.6bn debt and USD16.3bn recognised operating-lease liabilities. Facilities include specific GPU/cashflow security and guarantee differences."
  "H1 run-rate is not full-year forecast; undrawn debt is NOT cash; customer backlog is NOT free cash; secured/unsecured/operating leases require distinct claims and maturities."

softBankSep24SecuredNoneNotes : SourceReceipt
softBankSep24SecuredNoneNotes = sourceReceipt
  "SoftBank Group Corp."
  "Issuance of Foreign Currency-Denominated Senior Notes"
  "2026-09-24"
  "https://group.softbank/en/news/press/20260924"
  firstPartyIssuer
  "USD10bn unsecured BB+ notes: USD1bn 2030 at 8.625pct, USD4.5bn 2032 at 9.25pct, USD4.5bn 2034 at 9.75pct; plus EUR1bn separate notes. Announced use included USD10bn OpenAI follow-on tranche; implied annual USD coupons USD941.25m excluding EUR notes and other debt."
  "Do not treat note coupons as total portfolio funding costs or count the replaced bridge as still borrowed."

softBankOctober1BridgeResolved : SourceReceipt
softBankOctober1BridgeResolved = sourceReceipt
  "SoftBank Group Corp."
  "Execution of Follow-on Investment (Third Tranche) in OpenAI"
  "2026-10-01"
  "https://group.softbank/en/news/press/20261001"
  firstPartyIssuer
  "Executed USD10bn third tranche funded by proceeds of 24 September notes; completed USD30bn follow-on, cumulative USD64.6bn OpenAI investment, ~13pct interest; fully repaid and cancelled USD40bn bridge facility by end September."
  "Old bridge liability must not be double-counted with the newly issued takeout notes. Equity stake value and company NAV are not independent external cash or cash servicing."

softBankCFOFY26NonRecoursePlan : SourceReceipt
softBankCFOFY26NonRecoursePlan = sourceReceipt
  "Yoshimitsu Goto / SoftBank Group Corp."
  "SoftBank Group Report 2026 CFO Message"
  "2026"
  "https://group.softbank/en/ir/financials/annual_reports/2026/message/goto"
  firstPartyIssuer
  "SoftBank CFO describes portfolio-backed takeout financing, NAV/LTV management, and project-level nonrecourse AI infrastructure debt intended not to increase SoftBank parent LTV."
  "Stated nonrecourse policy is not evidence every project is legally remote from all parent risks, nor proof project returns exceed financing."

edZitronCreditCrunch2026 : SourceReceipt
edZitronCreditCrunch2026 = sourceReceipt
  "Ed Zitron"
  "Credit Crunch"
  "2026-10-06"
  "https://www.wheresyoured.at/credit-crunch/"
  attributedAuthor
  "Authored critical financial interpretation of AI debt, rising Treasury funding costs, SPVs, compute contract economics and off-balance project funding."
  "Original critical commentary, not independent regulator measurement; quantify assertions against issuer filings and preserve interpretations as attributed."

edZitronAnnualizedEnron2026 : SourceReceipt
edZitronAnnualizedEnron2026 = sourceReceipt
  "Ed Zitron"
  "Annualized Enron Rate"
  "2026-10-13"
  "https://www.wheresyoured.at/annualized-enron-rate/"
  attributedAuthor
  "Authored critique of annualised run-rate representations and gross/net customer revenue, including alleged OpenAI definition changes."
  "Criticism and reporting are not audited issuer statements; trailing-realised revenues and annualised hypothetical run rates are different metrics."

------------------------------------------------------------------------
-- CONTINUING CAPITAL CYCLE, OCTOBER 2026 issuer-report refinements.
------------------------------------------------------------------------

coreWeaveCashPrepaymentsOriginal2026 : SourceReceipt
coreWeaveCashPrepaymentsOriginal2026 = sourceReceipt
  "CoreWeave Inc.; U.S. SEC"
  "2026-06-30 Form 10-Q, consolidated statements of cash flow: deferred revenue movement and liquidity note"
  "2026-06-30"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000366/crwv-20260630.htm"
  firstPartyIssuer
  "Six months operating cash +USD3663m include +USD1365m net movement in deferred revenue; reported company liquidity USD15553m is cash USD5524m, securities USD15m and unused SECURED borrowing capacity USD10014m."
  "Customer prepayment is genuine cash and a future service commitment, not automatically independently recurring terminal cash; subtracting the deferred revenue movement is a sensitivity, not a corrected GAAP OCF or proof of round-tripped demand."

metaEscrowRestricted2026 : SourceReceipt
metaEscrowRestricted2026 = sourceReceipt
  "Meta Platforms Inc.; U.S. SEC"
  "2026-09-30 Form 10-Q, Note 10: restricted cash tied to multi-year infrastructure agreements"
  "2026-09-30"
  "https://www.sec.gov/Archives/edgar/data/1326801/000162828026066773/meta-20260930.htm"
  firstPartyIssuer
  "USD10800m money-market funds reclassified as restricted cash equivalents under infrastructure escrow conditions, release expected in 2028-30 contingent on obligations; in addition to issuer's USD355730m future not-commenced leases and USD454520m noncancel commitments."
  "Restricted funds are not free corporate liquidity; do not add escrow to gross liability amounts or automatically count the two future-obligation categories as disjoint."

------------------------------------------------------------------------
-- ORIGINAL COREWEAVE DDTL 3.0 CASH WATERFALL + CONTRACT REALISATION
-- Source priority: SEC-filed actual contractual text, not later synthesis.
-- Prior independent source-written owner PR #1101 already reads DDTL3;
-- this PR #1443 is ONLY a governance consumer of its contract economics.
------------------------------------------------------------------------

coreWeaveDDTL3Sec220WaterfallOriginal : SourceReceipt
coreWeaveDDTL3Sec220WaterfallOriginal = sourceReceipt
  "CoreWeave Inc., Compute Acquisition Co. VII / V; US SEC"
  "2025-07-28 DDTL 3.0 Credit Agreement Exhibit 10.1, Section 2.20(b), pp 57-59"
  "2025-07-28"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962825000033/coreweave30-ex101xtermlo.htm"
  firstPartyIssuer
  "Original cash-control priority: (i) eligible operating expenses, up to USD50m per calendar month in that first step; (ii) trustee/administrative indemnity and fees; (iii) interest and scheduled swap payments; (iv) liquidity-account top-up; (v) scheduled principal and certain swap termination amounts; (vi) conditional cash trap; (vii) other operating/capital expenditure only with OpEx Payment Condition; (viii) remaining cash to distribution reserve. Section 2.20(d) says reserve withdrawal remains conditional."
  "The account accepts parent deposits and certain reserves, not only external customer cash. These priority categories, timing and legal conditions are NOT a public statement of realised receipt or upstream legally distributable company cash."

coreWeaveDDTL3CureDecember31Original : SourceReceipt
coreWeaveDDTL3CureDecember31Original = sourceReceipt
  "CoreWeave Inc.; US SEC"
  "First Amendment to Credit Agreement and Parent Guarantee and Pledge Agreement, Exhibit 10.31, sections 1.01 and 6.12"
  "2025-12-31"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000104/ex10311.htm"
  firstPartyIssuer
  "Amended Contract Realization Ratio numerator includes MSA billed/received contract amounts without duplication PLUS CRR Cure Proceeds from equity. Minimum ratio 0.85:1.00 after the specified February 2026 commencement, subject to the disclosed zero-denominator exception; projected contract cash denominator uses a financial model and 360-day convention."
  "Passing CRR alone does not mean customers paid cash; billed revenue may be accrued, equity cure is not customer cash, compliance cannot establish actual observed ratio, and an amendment cannot prove any cure occurred."

coreWeaveDDTL3OriginalHedgeSerialRelease : SourceReceipt
coreWeaveDDTL3OriginalHedgeSerialRelease = sourceReceipt
  "CoreWeave Compute Acquisition Co. VII / V; US SEC"
  "2025-07-28 Credit Agreement Exhibit 10.1 §§5.22–5.23, 6.06"
  "2025-07-28"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962825000033/coreweave30-ex101xtermlo.htm"
  firstPartyIssuer
  "§5.22 requires borrower to provide financed GPU-rack serial numbers to lenders within 60 days of each borrowing, but individual GPU serial lists from NVIDIA/Dell are subject to receipt and reasonable efforts. §5.23 requires swap/cap protection on at least 75pct of reasonably projected floating-rate loan principal by deadlines and adjustment on draws/prepayments, subject to derivative basis/conditions. §6.06 limits restricted payments by distribution conditions and specified exceptions."
  "A 12pct flat new-money interest simulation does not describe the hedged actual DDTL 3.0 coupon; projected hedge notional != verified effective coverage, parent sponsor distribution or public GPU registry. Section 2.20 priorities and separate Interparty Agreement are not fully executable from this summary."

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
