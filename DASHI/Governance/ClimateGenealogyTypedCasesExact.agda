module DASHI.Governance.ClimateGenealogyTypedCasesExact where

------------------------------------------------------------------------
-- TWO-AXIS CLIMATE / TOBACCO WORKED CASE
--
-- Source rows here mirror the supplied typed-edge research manifest.  Relation
-- kind and evidence quality remain independent.
--
-- Primary / institutional sources represented below:
--
-- Frederick Seitz, interview by FRONTLINE / PBS, "Hot Politics: Interview --
-- Frederick Seitz" (2006).  No DOI asserted.  Bounded role: first-person
-- testimony concerning R.J. Reynolds research funding and Seitz's George C.
-- Marshall Institute chairmanship; memory testimony is not an internal RJR
-- accounting record.
--
-- Brown & Williamson Tobacco Corporation,
-- "Smoking and Health Proposal" (1969), Bates 690010951--690010959,
-- UCSF Industry Documents Library.  No DOI asserted.
--
-- American Petroleum Institute / Global Climate Science Communications Team,
-- "Global Climate Science Communications Action Plan" (1998).
-- Archived primary planning document; no DOI asserted.
--
-- Naomi Oreskes; Erik M. Conway,
-- "Defeating the merchants of doubt", Nature 465:686--687 (2010),
-- DOI 10.1038/465686a.
-- Bounded role: historical corroboration and search map, not a replacement for
-- the primary endpoint documents.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.TypedGenealogyEdgeExact as Typed
import DASHI.Core.IntersectionalNonFactorability as INF
open import Agda.Builtin.Equality using (refl)

seitzPBS : Typed.SourceReceipt
seitzPBS = Typed.sourceReceipt
  "Frederick Seitz; FRONTLINE / PBS"
  "Hot Politics: Interview -- Frederick Seitz"
  "2006"
  "PBS FRONTLINE interview; no DOI asserted"
  "first-person testimony concerning R.J. Reynolds research-funding relationship and George C. Marshall Institute chairmanship"

bw1969 : Typed.SourceReceipt
bw1969 = Typed.sourceReceipt
  "Brown & Williamson Tobacco Corporation"
  "Smoking and Health Proposal"
  "1969"
  "Bates 690010951--690010959; UCSF Industry Documents Library; no DOI asserted"
  "primary tobacco document establishing the stated doubt/controversy communication objective"

api1998 : Typed.SourceReceipt
api1998 = Typed.sourceReceipt
  "American Petroleum Institute / Global Climate Science Communications Team"
  "Global Climate Science Communications Action Plan"
  "1998"
  "archived primary planning document; no DOI asserted"
  "primary climate-communications plan naming the George C. Marshall Institute and stating uncertainty-oriented public-policy objectives"

oreskesConwayNature : Typed.SourceReceipt
oreskesConwayNature = Typed.sourceReceipt
  "Naomi Oreskes; Erik M. Conway"
  "Defeating the merchants of doubt"
  "2010"
  "Nature 465:686--687; DOI 10.1038/465686a"
  "historical corroboration/search map; not by itself a primary transfer document"

------------------------------------------------------------------------
-- E1--E3: composed institutional path.  These edges deliberately assert
-- funding/personnel/organisation relations, not method transfer.
------------------------------------------------------------------------

rjrToSeitz : Typed.TypedGenealogyEdge
rjrToSeitz = Typed.typedGenealogyEdge
  "E1" "R.J. Reynolds Tobacco Co." "Frederick Seitz"
  Typed.funding Typed.corroborated
  (seitzPBS ∷ [])
  "RJR-to-Seitz funding relationship is supported by Seitz's first-person account; direct RJR financial records would strengthen documentary corroboration"

seitzToMarshall : Typed.TypedGenealogyEdge
seitzToMarshall = Typed.typedGenealogyEdge
  "E2" "Frederick Seitz" "George C. Marshall Institute"
  Typed.personnelContinuity Typed.corroborated
  (seitzPBS ∷ [])
  "Seitz identifies himself as chairman emeritus; this is personnel continuity, not proof that a tobacco method was transferred"

marshallInAPIPlan : Typed.TypedGenealogyEdge
marshallInAPIPlan = Typed.typedGenealogyEdge
  "E3" "George C. Marshall Institute" "1998 API climate communications plan"
  Typed.organisationalContinuity Typed.primary
  (api1998 ∷ [])
  "the Marshall Institute is textually present in the primary plan as a participating/potential allocation organization; no inferred method-transfer claim is needed"

------------------------------------------------------------------------
-- E4/E4b: SAME endpoint documents, TWO propositions.
--
-- E4: method recurrence is primary-source strong.
-- E4b: historical transfer remains pending because no intervening transmission
-- witness has been installed.
------------------------------------------------------------------------

bwToAPIRecurrence : Typed.TypedGenealogyEdge
bwToAPIRecurrence = Typed.typedGenealogyEdge
  "E4" "1969 B&W Smoking and Health Proposal" "1998 API climate communications plan"
  Typed.methodRecurrence Typed.primary
  (bw1969 ∷ api1998 ∷ [])
  "two primary documents support a tightly comparable uncertainty/controversy communication pattern; this edge asserts recurrence, not transmission"

bwToAPIHistoricalTransferPending : Typed.TypedGenealogyEdge
bwToAPIHistoricalTransferPending = Typed.typedGenealogyEdge
  "E4b" "1969 B&W Smoking and Health Proposal" "1998 API climate communications plan"
  Typed.historicalTransfer Typed.pendingBridge
  (bw1969 ∷ api1998 ∷ oreskesConwayNature ∷ [])
  "historical-transfer hypothesis remains open pending a personnel, citation, consulting, document-flow, or equivalent transmission bridge"

recurrenceCannotBePromotedByPrimaryQualityAlone :
  Typed.StrongHistoricalTransfer bwToAPIRecurrence → ⊥
recurrenceCannotBePromotedByPrimaryQualityAlone transfer =
  Typed.methodRecurrenceIsNotTransferRelation
    (Typed.relationIsTransfer transfer)

pendingHistoricalTransferIsNotStrongYet :
  Typed.StrongHistoricalTransfer bwToAPIHistoricalTransferPending → ⊥
pendingHistoricalTransferIsNotStrongYet transfer =
  Typed.pendingBridgeIsNotStrong
    (Typed.evidenceIsStrong transfer)

------------------------------------------------------------------------
-- E5--E7: institutional continuity and explicitly unresolved candidates.
------------------------------------------------------------------------

hillKnowltonContinuity : Typed.TypedGenealogyEdge
hillKnowltonContinuity = Typed.typedGenealogyEdge
  "E5" "Hill & Knowlton tobacco-era PR" "Hill+Knowlton fossil-fuel-era client work"
  Typed.organisationalContinuity Typed.corroborated
  []
  "same-firm/institutional-continuity proposition; a source-specific client/lineage receipt should be attached before stronger method claims are made"

hillKnowltonMethodTransferCandidate : Typed.TypedGenealogyEdge
hillKnowltonMethodTransferCandidate = Typed.typedGenealogyEdge
  "E6" "Hill & Knowlton tobacco-era methods" "later climate/fossil-fuel communications"
  Typed.specificMethodTransfer Typed.candidateUnresolved
  []
  "specific method transmission is not installed; seek named personnel, internal memo, consulting record, or equivalent transmission evidence"

singerTobaccoContinuityCandidate : Typed.TypedGenealogyEdge
singerTobaccoContinuityCandidate = Typed.typedGenealogyEdge
  "E7" "S. Fred Singer" "tobacco funding/direction"
  Typed.personnelContinuity Typed.candidateUnresolved
  []
  "repeated secondary assertion is retained as an unresolved search candidate; no primary funding/direction receipt is installed here"

singerCandidateIsNotStrong :
  Typed.StrongEvidence (Typed.evidenceStrength singerTobaccoContinuityCandidate) → ⊥
singerCandidateIsNotStrong = Typed.candidateUnresolvedIsNotStrong

record ClimateTypedCaseBoundary : Set where
  constructor climateTypedCaseBoundary
  field
    composedInstitutionalPathInstalled : Bool
    methodRecurrencePrimary : Bool
    recurrencePromotedToTransfer : Bool
    historicalTransferBridgeInstalled : Bool
    singerPrimaryReceiptInstalled : Bool
    unresolvedSingerTreatedAsRefuted : Bool

canonicalClimateTypedCaseBoundary : ClimateTypedCaseBoundary
canonicalClimateTypedCaseBoundary =
  climateTypedCaseBoundary true true false false false false


------------------------------------------------------------------------
-- 1998 documented COMMON PRODUCTION TEAM, exact contributors rather than
-- an inferred celebrity/ideological network. Joe Walker's cover letter and
-- the 3 Apr action plan are printed in the 27 Apr Congressional Record.
-- A participant credit is NOT proof of a personally authored sentence,
-- funding payment, implementation or a downstream 2026 broadcast direction.
------------------------------------------------------------------------

apiCongressional1998 : Typed.SourceReceipt
apiCongressional1998 = Typed.sourceReceipt
  "American Petroleum Institute / Joseph Walker / Global Climate Science Communications Team; US Congressional Record"
  "Global Climate Science Communications Action Plan and covering letter"
  "1998-04-03; entered Congressional Record 1998-04-27"
  "https://www.govinfo.gov/content/pkg/CREC-1998-04-27/html/CREC-1998-04-27-pt1-PgH2323.htm"
  "Original publicly filed proposed communications strategy with 13 named workshop contributors, possible funders, public and media uncertainty objectives. A draft and funding prospectus are not an implementation/payment receipt."

api1998TeamContributorNames : List String
api1998TeamContributorNames =
  "A. John Adams (John Adams Associates)" ∷
  "Candace Crandall (Science and Environmental Policy Project)" ∷
  "David Rothbard (Committee for a Constructive Tomorrow (CFACT))" ∷
  "Jeffrey Salmon (George C. Marshall Institute)" ∷
  "Lee Garrigan (Environmental Issues Council)" ∷
  "Lynn Bouchey (Frontiers of Freedom)" ∷
  "Myron Ebell (Frontiers of Freedom)" ∷
  "Peter Cleary (Americans for Tax Reform)" ∷
  "Randy Randol (Exxon Corp.)" ∷
  "Robert Gehri (Southern Company)" ∷
  "Sharon Kneiss (Chevron Corp.)" ∷
  "Steve Milloy (The Advancement of Sound Science Coalition (TASSC))" ∷
  "Joseph Walker (American Petroleum Institute (API))" ∷ []

apiNamedContributorAJohnAdams : Typed.TypedGenealogyEdge
apiNamedContributorAJohnAdams = Typed.typedGenealogyEdge
  "E8-01" "A. John Adams (John Adams Associates)" "1998 API communications team"
  Typed.personnelContinuity Typed.primary
  (apiCongressional1998 ∷ [])
  "Named contributor to a shared draft plan according to API's original team list; not a personally authored claim, approved funding payment, executed grant, or later coordination proof."

apiNamedContributorCandaceCrandall : Typed.TypedGenealogyEdge
apiNamedContributorCandaceCrandall = Typed.typedGenealogyEdge
  "E8-02" "Candace Crandall (Science and Environmental Policy Project)" "1998 API communications team"
  Typed.personnelContinuity Typed.primary
  (apiCongressional1998 ∷ [])
  "Named by API's original draft as contributor; not personally attributed any sentence, payment or later order. Crandall's claimed involvement is reported as subsequently disputed in SourceWatch; no first-person rebuttal acquired here."

apiNamedContributorDavidRothbard : Typed.TypedGenealogyEdge
apiNamedContributorDavidRothbard = Typed.typedGenealogyEdge
  "E8-03" "David Rothbard (Committee for a Constructive Tomorrow (CFACT))" "1998 API communications team"
  Typed.personnelContinuity Typed.primary
  (apiCongressional1998 ∷ [])
  "Named contributor to a shared draft plan according to API's original team list; not a personally authored claim, approved funding payment, executed grant, or later coordination proof."

apiNamedContributorJeffreySalmon : Typed.TypedGenealogyEdge
apiNamedContributorJeffreySalmon = Typed.typedGenealogyEdge
  "E8-04" "Jeffrey Salmon (George C. Marshall Institute)" "1998 API communications team"
  Typed.personnelContinuity Typed.primary
  (apiCongressional1998 ∷ [])
  "Named contributor to a shared draft plan according to API's original team list; not a personally authored claim, approved funding payment, executed grant, or later coordination proof."

apiNamedContributorLeeGarrigan : Typed.TypedGenealogyEdge
apiNamedContributorLeeGarrigan = Typed.typedGenealogyEdge
  "E8-05" "Lee Garrigan (Environmental Issues Council)" "1998 API communications team"
  Typed.personnelContinuity Typed.primary
  (apiCongressional1998 ∷ [])
  "Named contributor to a shared draft plan according to API's original team list; not a personally authored claim, approved funding payment, executed grant, or later coordination proof."

apiNamedContributorLynnBouchey : Typed.TypedGenealogyEdge
apiNamedContributorLynnBouchey = Typed.typedGenealogyEdge
  "E8-06" "Lynn Bouchey (Frontiers of Freedom)" "1998 API communications team"
  Typed.personnelContinuity Typed.primary
  (apiCongressional1998 ∷ [])
  "Named contributor to a shared draft plan according to API's original team list; not a personally authored claim, approved funding payment, executed grant, or later coordination proof."

apiNamedContributorMyronEbell : Typed.TypedGenealogyEdge
apiNamedContributorMyronEbell = Typed.typedGenealogyEdge
  "E8-07" "Myron Ebell (Frontiers of Freedom)" "1998 API communications team"
  Typed.personnelContinuity Typed.primary
  (apiCongressional1998 ∷ [])
  "Named contributor to a shared draft plan according to API's original team list; not a personally authored claim, approved funding payment, executed grant, or later coordination proof."

apiNamedContributorPeterCleary : Typed.TypedGenealogyEdge
apiNamedContributorPeterCleary = Typed.typedGenealogyEdge
  "E8-08" "Peter Cleary (Americans for Tax Reform)" "1998 API communications team"
  Typed.personnelContinuity Typed.primary
  (apiCongressional1998 ∷ [])
  "Named contributor to a shared draft plan according to API's original team list; not a personally authored claim, approved funding payment, executed grant, or later coordination proof."

apiNamedContributorRandyRandol : Typed.TypedGenealogyEdge
apiNamedContributorRandyRandol = Typed.typedGenealogyEdge
  "E8-09" "Randy Randol (Exxon Corp.)" "1998 API communications team"
  Typed.personnelContinuity Typed.primary
  (apiCongressional1998 ∷ [])
  "Named contributor to a shared draft plan according to API's original team list; not a personally authored claim, approved funding payment, executed grant, or later coordination proof."

apiNamedContributorRobertGehri : Typed.TypedGenealogyEdge
apiNamedContributorRobertGehri = Typed.typedGenealogyEdge
  "E8-10" "Robert Gehri (Southern Company)" "1998 API communications team"
  Typed.personnelContinuity Typed.primary
  (apiCongressional1998 ∷ [])
  "Named contributor to a shared draft plan according to API's original team list; not a personally authored claim, approved funding payment, executed grant, or later coordination proof."

apiNamedContributorSharonKneiss : Typed.TypedGenealogyEdge
apiNamedContributorSharonKneiss = Typed.typedGenealogyEdge
  "E8-11" "Sharon Kneiss (Chevron Corp.)" "1998 API communications team"
  Typed.personnelContinuity Typed.primary
  (apiCongressional1998 ∷ [])
  "Named contributor to a shared draft plan according to API's original team list; not a personally authored claim, approved funding payment, executed grant, or later coordination proof."

apiNamedContributorSteveMilloy : Typed.TypedGenealogyEdge
apiNamedContributorSteveMilloy = Typed.typedGenealogyEdge
  "E8-12" "Steve Milloy (The Advancement of Sound Science Coalition (TASSC))" "1998 API communications team"
  Typed.personnelContinuity Typed.primary
  (apiCongressional1998 ∷ [])
  "Named contributor to a shared draft plan according to API's original team list; not a personally authored claim, approved funding payment, executed grant, or later coordination proof."

apiNamedContributorJosephWalker : Typed.TypedGenealogyEdge
apiNamedContributorJosephWalker = Typed.typedGenealogyEdge
  "E8-13" "Joseph Walker (American Petroleum Institute (API))" "1998 API communications team"
  Typed.personnelContinuity Typed.primary
  (apiCongressional1998 ∷ [])
  "Named contributor to a shared draft plan according to API's original team list; not a personally authored claim, approved funding payment, executed grant, or later coordination proof."


gccLennyBernstein1995 : Typed.SourceReceipt
gccLennyBernstein1995 = Typed.sourceReceipt
  "Lenny Bernstein / Mobil Corporation / Global Climate Coalition"
  "Predicting Future Climate Change: A Primer (1995 draft)"
  "1995-12"
  "https://www.climatefiles.com/denial-groups/global-climate-coalition-collection/global-climate-coalition-draft-primer/"
  "Original internal industry-coalition draft acknowledges anthropogenic greenhouse science and criticises specific contrarian theories; archive's document history says these were omitted from a later public version. Separate method-content and redaction receipts."

exxonInternal1982 : Typed.SourceReceipt
exxonInternal1982 = Typed.sourceReceipt
  "M.B. Glaser / Exxon Research and Engineering Company"
  "CO2 Greenhouse Effect memorandum to management"
  "1982-11-12"
  "https://www.climatefiles.com/exxonmobil/1982-memo-to-exxon-management-about-co2-greenhouse-effect/"
  "Original internal company science projected warming and discussed emissions reduction, with real scientific uncertainty also acknowledged. Private acknowledgement is not every employee's belief or proof of subsequent intent."

shellInternal1988 : Typed.SourceReceipt
shellInternal1988 = Typed.sourceReceipt
  "Royal Dutch/Shell Greenhouse Effect Working Group"
  "The Greenhouse Effect, confidential HSE 88-001"
  "1988"
  "https://climateinvestigations.org/shell-oil-climate-documents/"
  "Archived internal 1988 report rooted in Shell's research programme since 1981; publicly rediscovered by Jelmer Mommers and published through Climate Investigations Center."

shellFirstParty1998 : Typed.SourceReceipt
shellFirstParty1998 = Typed.sourceReceipt
  "Royal Dutch/Shell Group"
  "The Shell Report 1998: lobbying and industry associations, p. 38 (PDF index 40)"
  "1998"
  "https://www.shell.com/sustainability/transparency-and-sustainability-reporting/sustainability-reports/_jcr_content/root/main/section/list/list_item.multi.stream/1657185136417/8c7cf7e17abcd9772af39994b88ed37a5a86e216/shell-sustainability-report-1998-1997.pdf"
  "Shell itself states Shell Oil withdrew from the Global Climate Coalition in April 1998 over Kyoto targets and contrasts the coalition's opposition with Shell's precautionary approach. Report also proposes expanding natural gas."

bpLeadership1997 : Typed.SourceReceipt
bpLeadership1997 = Typed.sourceReceipt
  "John Browne / British Petroleum, retrospective interview at Stanford GSB"
  "Former BP head reflects on his 1997 call for climate action"
  "1997 speech, revisited 2022"
  "https://www.gsb.stanford.edu/insights/former-bp-head-reflects-his-call-climate-action-25-years-ago"
  "First-person retrospective account says BP leadership supported taking climate risk seriously and trade-group peers often favoured delay; not the uninspected signed GCC resignation paperwork."

mooreCO2Coalition : Typed.SourceReceipt
mooreCO2Coalition = Typed.sourceReceipt
  "CO2 Coalition (institution's own leadership biography)"
  "Director Patrick Moore: served as chair 2019 and 2020"
  "2019-2020 role, current biography"
  "https://co2coalition.org/teammember/director-patrick-moore/"
  "Coalition acknowledges Moore's chairmanship, presents him as a Greenpeace cofounder. Greenpeace itself disputes the founder label; early Greenpeace activist/1971 voyage participation is not disputed."

mooreHeartland : Typed.SourceReceipt
mooreHeartland = Typed.sourceReceipt
  "Heartland Institute"
  "Patrick Moore, listed senior fellow"
  "undated current institutional biography"
  "https://heartland.org/about-us/who-we-are/patrick-moore/"
  "Think-tank self-listing establishes public affiliation; role description alone does not establish payments or exact work commissioned."

greenpeaceHistory : Typed.SourceReceipt
greenpeaceHistory = Typed.sourceReceipt
  "Greenpeace International"
  "Founders and early Amchitka voyage"
  "historical institutional account"
  "https://www.greenpeace.org/international/about/founders/"
  "Organisation names its 1970 initiating committee and includes Patrick Moore as 1971 voyage participant while disputing his founder designation. Founder status remains institutionally contested."

hancockIPAJudgment : Typed.SourceReceipt
hancockIPAJudgment = Typed.sourceReceipt
  "NSW Supreme Court, Rinehart v Rinehart [2018] NSWSC 1102"
  "Paragraph 25, schedule of Hancock Prospecting donations to IPA"
  "2018"
  "https://www.casechat.au/cases/au/rinehart-v-rinehart-9"
  "Judgment text reproduced by CaseChat: schedule shows AUD2.3m to IPA in 2016 and AUD2.2m in 2017; current funding/particular editorial instructions not thereby proven."

cfactNova2026 : Typed.SourceReceipt
cfactNova2026 = Typed.sourceReceipt
  "CFACT hosting credited Joanne Nova source"
  "BOM's scientific scandal: The raw data is not raw"
  "2026-10-18"
  "https://www.cfact.org/2026/10/18/boms-scientific-scandal-the-raw-data-is-not-raw/"
  "Original 2026 article names Jo Nova; CFACT is host/republication site, not an independent archival temperature analysis or a source identified as commissioning it."

reefPatrickMoore2021 : Typed.SourceReceipt
reefPatrickMoore2021 = Typed.sourceReceipt
  "Carly Lubicz-Zaorski; Maxine Newlands; Theresa Petray"
  "Fuelling the climate and science ‘denial machine’ on social media: A case study of the Great Barrier Reef’s 2021 ‘in danger’ recommendation on Twitter, YouTube and Facebook"
  "online 2023; 2024 journal issue"
  "DOI 10.1177/09636625231202117"
  "Peer-reviewed 2021 network study attributes sharing of Peter Ridd's reef claim to Patrick Moore; it does not prove funding, command, or a copied scientific measurement."

exxonScienceInternalOwner : Typed.TypedGenealogyEdge
exxonScienceInternalOwner = Typed.typedGenealogyEdge
  "E9-01" "Exxon research and management" "1982 Glaser internal greenhouse-science memo"
  Typed.organisationalContinuity Typed.primary
  (exxonInternal1982 ∷ [])
  "Original Exxon management receipt establishes internal climate-science knowledge and discussion of uncertainties; not a payment or censorship order."

shellScienceInternalOwner : Typed.TypedGenealogyEdge
shellScienceInternalOwner = Typed.typedGenealogyEdge
  "E9-02" "Shell Greenhouse Effect Working Group" "1988 internal Shell greenhouse-science report"
  Typed.organisationalContinuity Typed.primary
  (shellInternal1988 ∷ [])
  "Internal research ownership and findings are distinct from later Shell Oil trade-group decisions."

gccBernsteinPrivatePrimer : Typed.TypedGenealogyEdge
gccBernsteinPrivatePrimer = Typed.typedGenealogyEdge
  "E9-03" "Lenny Bernstein (Mobil)" "1995 GCC private climate science primer"
  Typed.personnelContinuity Typed.primary
  (gccLennyBernstein1995 ∷ [])
  "Named original corporate author of GCC internal science primer, which acknowledged greenhouse mechanisms; the archived public redaction is a separate derivative document, not a named downstream author."

shellGCCDefection1998 : Typed.TypedGenealogyEdge
shellGCCDefection1998 = Typed.typedGenealogyEdge
  "E9-04" "Shell Oil former GCC membership" "Shell Oil April 1998 withdrawal"
  Typed.organisationalContinuity Typed.primary
  (shellFirstParty1998 ∷ [])
  "Shell original 1998 annual/sustainability report explicitly states it exited GCC; therefore do not project historical member funding or communications to 2026."

bpLeadershipBreak1997 : Typed.TypedGenealogyEdge
bpLeadershipBreak1997 = Typed.typedGenealogyEdge
  "E9-05" "John Browne / BP leadership" "1997 publicly climate-risk affirmative policy"
  Typed.personnelContinuity Typed.corroborated
  (bpLeadership1997 ∷ [])
  "Browne's retrospective first-person explanation of BP leadership and public break; not proof all BP policies or investments were precautionary."

mooreCO2Chair : Typed.TypedGenealogyEdge
mooreCO2Chair = Typed.typedGenealogyEdge
  "E9-06" "Patrick Moore" "CO2 Coalition, 2019-20 chairman"
  Typed.personnelContinuity Typed.primary
  (mooreCO2Coalition ∷ [])
  "Coalition original biography supplies exact role; no inferred funding from oil company donors."

mooreHeartlandAffiliation : Typed.TypedGenealogyEdge
mooreHeartlandAffiliation = Typed.typedGenealogyEdge
  "E9-07" "Patrick Moore" "Heartland Institute senior fellow"
  Typed.personnelContinuity Typed.primary
  (mooreHeartland ∷ [])
  "Heartland direct institutional affiliation; not a retainer invoice or proof the institute commissioned every statement."

hancockIPAHistoricalDonations : Typed.TypedGenealogyEdge
hancockIPAHistoricalDonations = Typed.typedGenealogyEdge
  "E9-08" "Hancock Prospecting" "Institute of Public Affairs 2016-17"
  Typed.funding Typed.primary
  (hancockIPAJudgment ∷ [])
  "Court-quoted payment schedule identifies AUD4.5m historical IPA support; does not identify which IPA articles or think-tank conclusions it paid for."

cfactAPITo2026Continuity : Typed.TypedGenealogyEdge
cfactAPITo2026Continuity = Typed.typedGenealogyEdge
  "E9-09" "CFACT named in 1998 API communications team" "CFACT as Joanne Nova 2026 BOM article host"
  Typed.organisationalContinuity Typed.corroborated
  (apiCongressional1998 ∷ cfactNova2026 ∷ [])
  "Same named CFACT institution participates in historical plan and publishes Nova in 2026; 28-year timespan is NOT a demonstrated continuous communications order or funded carry-through."

moore2000sToReefDistribution : Typed.TypedGenealogyEdge
moore2000sToReefDistribution = Typed.typedGenealogyEdge
  "E9-10" "Patrick Moore, CO2 Coalition/Heartland affiliation" "Patrick Moore sharing Peter Ridd reef claims in 2021"
  Typed.personnelContinuity Typed.corroborated
  (mooreCO2Coalition ∷ mooreHeartland ∷ reefPatrickMoore2021 ∷ [])
  "Documented repeated PERSON across institutional affiliation and later reef dissemination; not an independent coral observation or proof either think tank commissioned his sharing."

apiContributorNotMethodTransfer :
  Typed.StrongHistoricalTransfer apiNamedContributorRandyRandol → ⊥
apiContributorNotMethodTransfer witness =
  Typed.personnelContinuityIsNotTransferRelation
    (Typed.relationIsTransfer witness)

ipaFundingNotEditorialMethod :
  Typed.StrongHistoricalTransfer hancockIPAHistoricalDonations → ⊥
ipaFundingNotEditorialMethod witness =
  Typed.fundingIsNotTransferRelation
    (Typed.relationIsTransfer witness)

cfactContinuationNotPlanTransfer :
  Typed.StrongHistoricalTransfer cfactAPITo2026Continuity → ⊥
cfactContinuationNotPlanTransfer witness =
  Typed.organisationalContinuityIsNotTransferRelation
    (Typed.relationIsTransfer witness)



------------------------------------------------------------------------
-- Independent quantitative audits: these are scholarly estimators, not
-- permission to label every dollar in an organisation's accounts as
-- climate-denial spend or every downstream message donor-commissioned.
------------------------------------------------------------------------

brulleFoundationStudy : Typed.SourceReceipt
brulleFoundationStudy = Typed.sourceReceipt
  "Robert J. Brulle"
  "Institutionalizing delay: foundation funding and the creation of U.S. climate change counter-movement organizations"
  "2014"
  "Climatic Change 122:681-694; https://researchdiscovery.drexel.edu/esploro/outputs/journalArticle/Institutionalizing-delay-foundation-funding-and-the/991019167769804721"
  "IRS/Foundation Center analysis of 91 organisations and 140 foundations in 2003-2010; approximately USD900m annual aggregate organisational revenue, USD64m annual identifiable foundation support. Revenue is NOT climate-specific spending."

farrellNetworkStudy : Typed.SourceReceipt
farrellNetworkStudy = Typed.sourceReceipt
  "Justin Farrell"
  "Corporate funding and ideological polarization about climate change"
  "2016"
  "PNAS 113:92-97; DOI 10.1073/pnas.1509433112"
  "Independent empirical network/text analysis of corporate funding and climate-policy polarisation; statistical association and network effect are not a donor-to-every-specific-sentence contract."

supranRahmstorfOreskesExxonAudit : Typed.SourceReceipt
supranRahmstorfOreskesExxonAudit = Typed.sourceReceipt
  "Geoffrey Supran; Stefan Rahmstorf; Naomi Oreskes"
  "Assessing ExxonMobil's global warming projections"
  "2023"
  "Science 379:eabk0063; DOI 10.1126/science.abk0063"
  "Independent quantitative assessment of company models documented 1977-2003 found a majority of Exxon/ExxonMobil original warming predictions accurately forecast subsequent warming. Public statements could differ from internal model conclusions."

record ConcentratedSourceAuditBoundary : Set where
  constructor concentratedSourceAuditBoundary
  field
    aDraftPlanIsNotImplementedCommunications : Bool
    foundingRoleIsNotUnauditedGreenpeaceFact : Bool
    historicOrganisationalFinanceEqualsExactMediaPayment : Bool
    total900mOrganisationRevenueIsClimateSpecificSpending : Bool
    samePersonAcrossPlatformsEqualsCentralCommand : Bool
    shellBPDefectionsPreservedAsCounterExamples : Bool
    independentScientificPredictionAuditIsNotAnAllegation : Bool

canonicalConcentratedSourceAuditBoundary : ConcentratedSourceAuditBoundary
canonicalConcentratedSourceAuditBoundary =
  concentratedSourceAuditBoundary
    true true false false false true true


reefSteveMilloy2021 : Typed.SourceReceipt
reefSteveMilloy2021 = Typed.sourceReceipt
  "Carly Lubicz-Zaorski; Maxine Newlands; Theresa Petray"
  "Fuelling the climate and science ‘denial machine’ on social media: A case study of the Great Barrier Reef’s 2021 ‘in danger’ recommendation on Twitter, YouTube and Facebook"
  "first online 2023-10-26; journal issue 2024"
  "Public Understanding of Science 33(3):270-289; DOI 10.1177/09636625231202117"
  "Original multi-platform 2021 case study explicitly names Fox News contributors including Steve Milloy among later amplifiers; does not claim he used an API draft to produce the post."

milloy1998ToReefMedia : Typed.TypedGenealogyEdge
milloy1998ToReefMedia = Typed.typedGenealogyEdge
  "E9-11" "Steve Milloy, original 1998 API plan participant" "Steve Milloy, 2021 reef-related Fox contributor"
  Typed.personnelContinuity Typed.corroborated
  (apiCongressional1998 ∷ reefSteveMilloy2021 ∷ [])
  "Same named person explicitly occurs in 1998 API communications plan and 2021 reef study: longitudinal identity/role overlap, NOT documentary evidence of continuously coordinated scripts, funding or factual corroboration."

milloyRepeatNotProofOfTwentyThreeYearPlan :
  Typed.StrongHistoricalTransfer milloy1998ToReefMedia → ⊥
milloyRepeatNotProofOfTwentyThreeYearPlan witness =
  Typed.personnelContinuityIsNotTransferRelation
    (Typed.relationIsTransfer witness)


------------------------------------------------------------------------
-- Earlier campaign roots (1991 / 1994), found by original-source snowball.
-- A pledged amount or unsolicited proposal is NEVER recorded as payment.
------------------------------------------------------------------------

ice1991TestCampaign : Typed.SourceReceipt
ice1991TestCampaign = Typed.sourceReceipt
  "Information Council for the Environment (ICE); utility-industry sponsors"
  "1991 Test Market Proposal and Benchmark Survey"
  "1991-02-04"
  "https://www.climatefiles.com/denial-groups/ice-campaign-plan/"
  "Archived original ICE proposal proposes approx USD500k test market strategy for disputing greenhouse-science certainty, sponsored through Edison Electric Institute / electric utility interests. A campaign plan and its budget are not an audited completed expense."

southernICEHistoricalAccount : Typed.SourceReceipt
southernICEHistoricalAccount = Typed.sourceReceipt
  "Energy and Policy Institute original archival investigation of Southern Company records"
  "Southern Company knew about climate change before it funded denial"
  "2022"
  "https://energyandpolicy.org/southern-company-knew-climate-change/"
  "Archival reporting identifies Southern Company PR executive Gale Klappa as 1991 ICE president and reports USD125k Southern commitment. Identity and pledge are reported from leaked records, not a new source-author invoice receipt."

singerGCC1994Proposal : Typed.SourceReceipt
singerGCC1994Proposal = Typed.sourceReceipt
  "S. Fred Singer / Science and Environmental Policy Project (SEPP)"
  "A Public Education Program on Global Warming: proposal to Global Climate Coalition"
  "1994"
  "https://climateinvestigations.org/bbc-radio-series-tracks-history-of-climate-denial/"
  "Archival original proposal seeks approx USD73000 funding for educational/public advocacy programme. Climate Investigations Center explicitly states it lacks evidence the requested payment was received; should not be treated as a grant."

southernCompany1991To1998 : Typed.TypedGenealogyEdge
southernCompany1991To1998 = Typed.typedGenealogyEdge
  "E9-12" "Southern Company, 1991 ICE involvement" "Robert Gehri of Southern Company, 1998 API team"
  Typed.organisationalContinuity Typed.corroborated
  (ice1991TestCampaign ∷ southernICEHistoricalAccount ∷ apiCongressional1998 ∷ [])
  "Same corporate institution is documented at 1991 ICE campaign and in 1998 API named-team list. Different representatives are named; no proof same staff drafted both scripts or planned a seven-year programme."

southernICEPledgeNotDisbursement : Typed.TypedGenealogyEdge
southernICEPledgeNotDisbursement = Typed.typedGenealogyEdge
  "E9-13" "Southern Company 1991 commitment report" "ICE proposed communications campaign funding"
  Typed.fundingCommitment Typed.corroborated
  (southernICEHistoricalAccount ∷ ice1991TestCampaign ∷ [])
  "Reported company commitment USD125000 is a financing pledge reported from archived records, not a produced bank-transfer or independently audited completed payment."

singer1994ToSEPP1998 : Typed.TypedGenealogyEdge
singer1994ToSEPP1998 = Typed.typedGenealogyEdge
  "E9-14" "S. Fred Singer/SEPP 1994 GCC proposal" "Candace Crandall/SEPP in 1998 API team"
  Typed.organisationalContinuity Typed.corroborated
  (singerGCC1994Proposal ∷ apiCongressional1998 ∷ [])
  "Same explicitly named SEPP organisation appears across original 1994 GCC proposal and 1998 API planning team with different named people; not evidence of completed Singer payment, tobacco financing or identical script authorship."

singerGCCSolicitationNotMoneyPaid : Typed.TypedGenealogyEdge
singerGCCSolicitationNotMoneyPaid = Typed.typedGenealogyEdge
  "E9-15" "S. Fred Singer/SEPP 1994 proposal" "Requested GCC USD73000 education-programme funding"
  Typed.fundingProposal Typed.corroborated
  (singerGCC1994Proposal ∷ [])
  "Proposal for funding has direct source existence. Solicitation/expected allocation is not a financial disbursement, and does not resolve the independent E7 tobacco finance hypothesis."

singerSEPPRepeatNotTobaccoPayment :
  Typed.StrongHistoricalTransfer singer1994ToSEPP1998 → ⊥
singerSEPPRepeatNotTobaccoPayment witness =
  Typed.organisationalContinuityIsNotTransferRelation
    (Typed.relationIsTransfer witness)

southernRepeatNotIdenticalScript :
  Typed.StrongHistoricalTransfer southernCompany1991To1998 → ⊥
southernRepeatNotIdenticalScript witness =
  Typed.organisationalContinuityIsNotTransferRelation
    (Typed.relationIsTransfer witness)


fundingRequestIsNotTransfer :
  Typed.StrongHistoricalTransfer singerGCCSolicitationNotMoneyPaid → ⊥
fundingRequestIsNotTransfer witness =
  Typed.fundingProposalIsNotTransferRelation
    (Typed.relationIsTransfer witness)

fundingPledgeIsNotTransfer :
  Typed.StrongHistoricalTransfer southernICEPledgeNotDisbursement → ⊥
fundingPledgeIsNotTransfer witness =
  Typed.fundingCommitmentIsNotTransferRelation
    (Typed.relationIsTransfer witness)


------------------------------------------------------------------------
-- Stronger same-object think-tank content procurement, GCC 1996-97.
-- Sources: independently curated Climate Investigations Center original
-- archival document index linking DocumentCloud original proposals, STAC
-- grant, editorial-rights memo and the separately published ACSH report.
-- DocumentCloud original PDF bodies were not retrievable via web in this
-- pass; these are corroborated document-ID and index observations, not
-- visually checked contract/payment/definitive final-version equivalence.
------------------------------------------------------------------------

gccACSHOriginalInvestigation : Typed.SourceReceipt
gccACSHOriginalInvestigation = Typed.sourceReceipt
  "Climate Investigations Center archival research, attributing GCC STAC, Mobil, Exxon and ACSH original records"
  "GCC Denial of Climate Impacts on Human Health"
  "investigation page undated, examined 2026-10-26"
  "https://climateinvestigations.org/global-climate-coalition-human-health/"
  "Indexed original 1996 STAC proposal and editorial-rights documents, identified co-chair Mobil Lenny Bernstein and Exxon scientists Barry Friedlander/Dennis Devlin, reported commissioned ACSH research. DocumentCloud scans not separately inspected this turn."

gccACSHPublished1997 : Typed.SourceReceipt
gccACSHPublished1997 = Typed.sourceReceipt
  "American Council on Science and Health (ACSH), original publisher"
  "Global climate change and human health"
  "1997"
  "https://www.acsh.org/news/1997/10/01/global-climate-change-and-human-health"
  "First-party ACSH Staff article dated 1 October 1997, publicly readable; it recommends adaptation/public-health capacity and opposes compulsory GHG mitigation on economic grounds. The inspected publisher summary does not identify GCC as sponsor. Whether this actual public text is the 1996-97 commissioned final product remains unresolved."

gccACSHCommissionedClimateHealth : Typed.TypedGenealogyEdge
gccACSHCommissionedClimateHealth = Typed.typedGenealogyEdge
  "E9-16" "Global Climate Coalition / STAC" "ACSH commissioned climate and human health study 1996-97"
  Typed.commissionedResearch Typed.corroborated
  (gccACSHOriginalInvestigation ∷ [])
  "CIC archive documents STAC choosing ACSH and describes funded research on climate-health links. Primary grant scan is indexed but unread by this pass; not a wholly independent publication or a definite downstream media outcome."

gccACSHDocumentedEditorialReviewRights : Typed.TypedGenealogyEdge
gccACSHDocumentedEditorialReviewRights = Typed.typedGenealogyEdge
  "E9-17" "GCC/STAC client" "ACSH commissioned climate-health study final editorial review discretion"
  Typed.editorialReviewRights Typed.corroborated
  (gccACSHOriginalInvestigation ∷ [])
  "CIC links archival agreement stating client had editorial discretion over final copy. This is contractual authority, NOT proof any particular scientifically false line was inserted or that rights were exercised."

gccACSH1997PublicPaperMatch : Typed.TypedGenealogyEdge
gccACSH1997PublicPaperMatch = Typed.typedGenealogyEdge
  "E9-18" "GCC-funded ACSH commissioned health study" "1997 ACSH Global climate change and human health public paper"
  Typed.topicalPublicationMatch Typed.corroborated
  (gccACSHOriginalInvestigation ∷ gccACSHPublished1997 ∷ [])
  "CIC documents an ACSH commission and title match. The ACSH first-party 1 October 1997 article is now inspected and explicitly recommends adaptation while opposing compulsory mitigation as harmful to the economy. It does not disclose GCC sponsorship. CIC did not acquire a final distribution receipt, so paid commissioning, public argument and final-text identity stay separate."

gccCHCReportedLaterExxonGrants : Typed.SourceReceipt
gccCHCReportedLaterExxonGrants = Typed.sourceReceipt
  "Climate Investigations Center analysis of documented Cooler Heads Coalition grants"
  "Cooler Heads Coalition"
  "post-1998 funds, original report later"
  "https://climateinvestigations.org/climate-deniers/cooler-heads-coalition/"
  "CIC reports Exxon gave a cumulative USD2774000 to Cooler Heads Coalition-member groups named on the 1998 API team in years after the plan. Individual payees and timestamps were not reconstructed here; no earmark for the proposed API plan or 2021 reef messaging is established."

exxonToCHCReportedPostAPIGrants : Typed.TypedGenealogyEdge
exxonToCHCReportedPostAPIGrants = Typed.typedGenealogyEdge
  "E9-19" "Exxon Corporation later disclosed funding" "Cooler Heads Coalition groups overlapping the 1998 API team"
  Typed.funding Typed.corroborated
  (gccCHCReportedLaterExxonGrants ∷ [])
  "CIC archival investigation reports cumulative USD2.774m later Exxon funding to CHC groups named in 1998 API team, not original receipts verified in this pass and not proof of an earmarked 1998 communications-plan payment."

gccACSHSharedSubjectNotIdenticalFinalFile :
  Typed.StrongHistoricalTransfer gccACSH1997PublicPaperMatch → ⊥
gccACSHSharedSubjectNotIdenticalFinalFile witness =
  Typed.publicationTopicMatchIsNotMethodTransfer
    (Typed.relationIsTransfer witness)

gccACSHContractualRightsNotProofOfSpecificScientificEdit :
  Typed.StrongHistoricalTransfer gccACSHDocumentedEditorialReviewRights → ⊥
gccACSHContractualRightsNotProofOfSpecificScientificEdit witness =
  Typed.editorialReviewRightsAreNotMethodTransfer
    (Typed.relationIsTransfer witness)



-- 2026-10-26 actual PUBLIC OUTPUT, first-party ACSH Staff. The report's
-- main recommendation is adaptation rather than compulsory emissions cuts.
-- It is not the original GCC/STAC editing contract or proof the STAC
-- client exercised its editorial-review entitlement. Publisher summary
-- acquired; separately referenced 1997 PDF's original pages not verified.
acsh1997OriginalPublicArgument : Typed.SourceReceipt
acsh1997OriginalPublicArgument = Typed.sourceReceipt
  "American Council on Science and Health (ACSH Staff), original publisher"
  "Global Climate Change and Human Health"
  "1997-10-01"
  "https://www.acsh.org/news/1997/10/01/global-climate-change-and-human-health"
  "First-party public text says anthropogenic warming may cause health harm, but argues to prioritise adaptation, public health and economic continuity over compulsory GHG emissions mitigation. This verifies a public position, not a specific GCC-mandated edit nor scientific validity of economic/medical claims."


------------------------------------------------------------------------
-- POLICY ACCESS receipt. The original 2019 CIC archival report describes a
-- 2001 US State Department briefing advising an Undersecretary to tell GCC
-- the administration rejected Kyoto partly based on its input. This is a
-- drafted statement of credited influence, NOT an inspected primary
-- government briefing, delivered remark, independent causal assessment,
-- or proof GCC was the necessary or sufficient reason for the decision.
------------------------------------------------------------------------

gccUSGovernmentBriefing2001 : Typed.SourceReceipt
gccUSGovernmentBriefing2001 = Typed.sourceReceipt
  "Climate Investigations Center, archival investigator (2019)"
  "The Global Climate Coalition: Big Business Funds Climate Change Denial and Regulatory Delay"
  "2019-03-25"
  "https://climateinvestigations.org/wp-content/uploads/2019/04/The-Global-Climate-Coalition-Denial-and-Delay.pdf"
  "CIC describes archived 2001 US State Department briefing instructing an Undersecretary to credit GCC policy input in rejecting Kyoto. CIC report parsed; original 2001 government document not separately acquired, report screenshot service cache-missed."

gcc2001DraftPolicyInputAcknowledgment : Typed.TypedGenealogyEdge
gcc2001DraftPolicyInputAcknowledgment = Typed.typedGenealogyEdge
  "E9-20" "Global Climate Coalition policy submissions" "2001 State Department prewritten administration acknowledgement"
  Typed.recommendationExposure Typed.corroborated
  (gccUSGovernmentBriefing2001 ∷ [])
  "Historical investigator reproduces an official briefing description instructing the recipient to tell GCC it influenced the administration's Kyoto rejection in part. This is evidence of a prepared acknowledgement and access, not independent confirmation remarks delivered or scientific causation of the Kyoto choice."

policyAccessIsNotCompletedMethodTransfer :
  Typed.StrongHistoricalTransfer gcc2001DraftPolicyInputAcknowledgment → ⊥
policyAccessIsNotCompletedMethodTransfer witness =
  Typed.recommendationExposureIsNotDirectMethodTransfer
    (Typed.relationIsTransfer witness)


------------------------------------------------------------------------
-- Cross-period rhetoric and 2026 AUS gas-policy recycled-statistic consumer.
-- Distinct first-party author/producer objects are still separate even when
-- the exact same rounded headline appears. This is not a national census.
------------------------------------------------------------------------

apiCharltonPromotedPoll1998 : Typed.SourceReceipt
apiCharltonPromotedPoll1998 = Typed.sourceReceipt
  "American Petroleum Institute team citing Charlton Research survey"
  "1998 climate communications plan: 1100 informed respondents and 58 percent"
  "1998-04-03"
  "https://www.govinfo.gov/content/pkg/CREC-1998-04-27/html/CREC-1998-04-27-pt1-PgH2323.htm"
  "The API plan says 58 percent were more likely to oppose Kyoto after an uncertainty-framed prompt; neither unprompted national opposition nor the underlying survey questionnaire and responses are acquired."

australiaInstitute17B2025 : Typed.SourceReceipt
australiaInstitute17B2025 = Typed.sourceReceipt
  "The Australia Institute / Mark Ogge"
  "There's a simple way to solve Australia's gas crisis and cut energy bills"
  "2025-12-09"
  "https://australiainstitute.org.au/post/theres-a-simple-way-to-solve-australias-gas-crisis-and-cut-energy-bills/"
  "First-party institute projection that a 25 percent export levy could raise around AUD17b annually. Model scenario/behavioural assumptions not independently recomputed."

futureGroupArthurDLittle2026 : Typed.SourceReceipt
futureGroupArthurDLittle2026 = Typed.sourceReceipt
  "Future Group / commissioned Arthur D. Little modelling"
  "Why Australia should act now on a gas export levy"
  "2026-04-23"
  "https://www.futuregroup.com.au/stories/why-australia-should-act-now-on-a-gas-export-levy"
  "First-party commissioning body reports up to AUD17b first year revenues and up to 15 percent wholesale electricity price reduction. Separately named consultant not proof of independent modelling premises."

pocockGas2026 : Typed.SourceReceipt
pocockGas2026 = Typed.sourceReceipt
  "Senator David Pocock, separate Senate inquiry comments"
  "A fair return: The case for a 25 per cent gas export tax"
  "2026-05-07"
  "https://www.aph.gov.au/Parliamentary_Business/Committees/Senate/Taxation_of_Gas_Resources/TaxationofGasResources/Report/Additional_Comments_from_Senator_David_Pocock"
  "Paragraph 1.28 credits Future Group Arthur D. Little and separately Australia Institute 17b estimates; same rounded conclusion is not evidence methods, base prices or forecasts were statistically independent."

taiGasRoyalty2024 : Typed.SourceReceipt
taiGasRoyalty2024 = Typed.sourceReceipt
  "The Australia Institute"
  "Gas exports: 56 percent given to corporations royalty-free"
  "2024-05-30"
  "https://australiainstitute.org.au/post/gas-exports-56-given-to-corporations-royalty-free/"
  "Original research organisation estimates 56 percent of gas exported paid no royalties, not that every project paid no company tax or that share applied to all extracted gas."

aepWoodMackenzie2026 : Typed.SourceReceipt
aepWoodMackenzie2026 = Typed.sourceReceipt
  "Australian Energy Producers commissioning Wood Mackenzie"
  "Gas tax proposal would make Australia uninvestable"
  "2026-04-12"
  "https://energyproducers.au/news/gas-tax-proposal-would-make-australia-uninvestable-and-threaten-future-energy-supply-report-finds"
  "First-party client release reports effective hypothetical project burden over 80 percent, project-value reduction up to 94 percent. Neither is an observed Australian national average tax burden."

nightlyJohnsonGas2026 : Typed.SourceReceipt
nightlyJohnsonGas2026 = Typed.sourceReceipt
  "Stephen Johnson, The Nightly original journalist"
  "Why a 25 per cent tax on gas exports would hurt everyday Australians"
  "2026-04-22"
  "https://thenightly.com.au/politics/australia/why-a-25-per-cent-tax-on-gas-exports-would-hurt-everyday-australians-c-22175435"
  "Named original 2026 news story reports Janette Hewson QRC warning about diminished investment and includes $17b advocacy estimate; it does not generate either competing econometric model."

hancockJohnsonReprint2026 : Typed.SourceReceipt
hancockJohnsonReprint2026 = Typed.sourceReceipt
  "Hancock Energy, article host crediting Stephen Johnson and The Nightly"
  "Gas tax would burn everyday Australians"
  "2026-04-22"
  "https://www.hancockenergy.com.au/gas-tax-would-burn-everyday-australians/"
  "First-party corporate republishing credits The Nightly and its author. This is an explicit source reprint not another empirical study, not proof a funder supplied journalist script."

iceToAPIUncertaintyStrategicRecurrence : Typed.TypedGenealogyEdge
iceToAPIUncertaintyStrategicRecurrence = Typed.typedGenealogyEdge
  "RC-01" "ICE 1991 warming as theory-not-fact campaign plan" "API 1998 uncertainty-in-public-discourse campaign plan"
  Typed.methodRecurrence Typed.primary
  (ice1991TestCampaign ∷ apiCongressional1998 ∷ [])
  "Original archived ICE plan and Congressional original API plan exhibit recurring uncertainty-oriented strategies. Exact historical ICE to API drafting transfer is not established."

tai17BRestatedByPocock2026 : Typed.TypedGenealogyEdge
tai17BRestatedByPocock2026 = Typed.typedGenealogyEdge
  "RC-02" "Australia Institute original AUD17b annual levy estimate" "David Pocock 2026 Senate comments"
  Typed.reportedStatisticRestatement Typed.primary
  (australiaInstitute17B2025 ∷ pocockGas2026 ∷ [])
  "Senator explicitly names original institute when repeating the numeric conclusion. His speech is not an additional independent model."

futureGroup17BRestatedByPocock2026 : Typed.TypedGenealogyEdge
futureGroup17BRestatedByPocock2026 = Typed.typedGenealogyEdge
  "RC-03" "Arthur D. Little commissioned by Future Group" "David Pocock 2026 Senate comments"
  Typed.reportedStatisticRestatement Typed.primary
  (futureGroupArthurDLittle2026 ∷ pocockGas2026 ∷ [])
  "Parliament separately credits named consultant with a matching rounded number; separate authorship does not imply statistically independent scenario assumptions."

tai56PcRoyaltyRestatedByPocock2026 : Typed.TypedGenealogyEdge
tai56PcRoyaltyRestatedByPocock2026 = Typed.typedGenealogyEdge
  "RC-04" "Australia Institute 56 percent no-royalty research" "David Pocock Senate comments"
  Typed.reportedStatisticRestatement Typed.primary
  (taiGasRoyalty2024 ∷ pocockGas2026 ∷ [])
  "Pocock cites Australia Institute analysis. Relative share of LNG exports attracting no royalties is not a claim that all LNG receives no Australian company tax."

nightlyToHancockExplicitReprint2026 : Typed.TypedGenealogyEdge
nightlyToHancockExplicitReprint2026 = Typed.typedGenealogyEdge
  "RC-05" "Stephen Johnson The Nightly article" "Hancock Energy host with byline credit"
  Typed.explicitAttributedRepublication Typed.primary
  (nightlyJohnsonGas2026 ∷ hancockJohnsonReprint2026 ∷ [])
  "Identifiable journalism text and author are promoted on a corporate site: positive republication, not a fresh independent reporter or evidence of purchased editorial control."

aepWoodMacStatisticsNotNationalTaxRate : Typed.TypedGenealogyEdge
aepWoodMacStatisticsNotNationalTaxRate = Typed.typedGenealogyEdge
  "RC-06" "Wood Mackenzie model commissioned by Australian Energy Producers" "AEP reported high-end 80-plus-percent tax and 94-percent value loss"
  Typed.reportedStatisticRestatement Typed.primary
  (aepWoodMackenzie2026 ∷ [])
  "Numeric statements are client-reported outputs for a model project and price assumptions, not already-realised national tax payments."

historicalUncertaintyStrategyIsNotDirectTransfer :
  Typed.StrongHistoricalTransfer iceToAPIUncertaintyStrategicRecurrence → ⊥
historicalUncertaintyStrategyIsNotDirectTransfer witness =
  Typed.methodRecurrenceIsNotTransferRelation
    (Typed.relationIsTransfer witness)

hancockReprintIsNotIndependentMethodTransmission :
  Typed.StrongHistoricalTransfer nightlyToHancockExplicitReprint2026 → ⊥
hancockReprintIsNotIndependentMethodTransmission witness =
  Typed.articleRepublicationIsNotHistoricalMethodTransfer
    (Typed.relationIsTransfer witness)

sameHeadlineIsNotMethodTransmission :
  Typed.StrongHistoricalTransfer tai17BRestatedByPocock2026 → ⊥
sameHeadlineIsNotMethodTransmission witness =
  Typed.headlineNumberRestatementIsNotHistoricalMethodTransfer
    (Typed.relationIsTransfer witness)

-- TWO different possible source ancestral worlds have the same visible
-- '$17b/year' policy headline. Inferring the number of independently
-- computed models from the public headline alone is therefore impossible.
-- The constructor 'twoNamedAnalyses' certifies two named authors, NOT
-- statistical independence of their underlying data and assumptions.
data Same17BPublicationCase : Set where
  oneNamedAnalysis twoNamedAnalyses : Same17BPublicationCase

data VisibleAnnual17BClaim : Set where
  annual17BHeadline : VisibleAnnual17BClaim

data NumberOfNamedModelSources : Set where
  oneNamedEstimator twoNamedEstimators : NumberOfNamedModelSources

same17BPrinted : Same17BPublicationCase → VisibleAnnual17BClaim
same17BPrinted _ = annual17BHeadline

namedModelSourceCount : Same17BPublicationCase → NumberOfNamedModelSources
namedModelSourceCount oneNamedAnalysis = oneNamedEstimator
namedModelSourceCount twoNamedAnalyses = twoNamedEstimators

sameHeadlineDistinctGenealogies :
  INF.NonFactorabilityWitness same17BPrinted namedModelSourceCount
sameHeadlineDistinctGenealogies =
  INF.nonFactorabilityWitness
    oneNamedAnalysis twoNamedAnalyses refl (λ ())

annual17BHeadlineCannotRevealModelAncestry :
  INF.FactorsThrough same17BPrinted namedModelSourceCount → ⊥
annual17BHeadlineCannotRevealModelAncestry =
  INF.witnessRulesOutEveryFlatFactorisation
    sameHeadlineDistinctGenealogies


------------------------------------------------------------------------
-- 2026 gas-tax proposal falsifier: a headline '25 percent' cannot determine
-- whether PRRT is REPLACED or a levy is ADDED to existing fiscal taxes.
-- These are actually distinct specifications in dated ACTU / AEP sources.
------------------------------------------------------------------------

actu2026OriginalReplacementProposal : Typed.SourceReceipt
actu2026OriginalReplacementProposal = Typed.sourceReceipt
  "ACTU / Michele O'Neil, original trade-union 17 March 2026 release"
  "Windfall profits to oil and gas multinationals should benefit working Australians"
  "2026-03-17"
  "https://www.actu.org.au/wp-content/uploads/2026/03/Windfall-profits-to-oil-and-gas-multinationals-should-benefit-working-Australians-1-1.pdf"
  "ACTU explicitly proposes replacing PRRT with an LNG export-value levy of 25 percent; it says $17.1b is 2023-24 retrospective what-if revenue, not 2026-27 guaranteed annual forecast. Original PDF text parsed but visual screenshot service cache-missed."

actuReplacementVsAEPAddOnSpecification : Typed.TypedGenealogyEdge
actuReplacementVsAEPAddOnSpecification = Typed.typedGenealogyEdge
  "RC-07" "ACTU 17 March 2026 25 percent levy REPLACES PRRT" "AEP Wood Mackenzie 12 April 2026 ADDITIONAL 25 percent tax model"
  Typed.parallelEconomicArgument Typed.primary
  (actu2026OriginalReplacementProposal ∷ aepWoodMackenzie2026 ∷ [])
  "Both promote discussion of 25 percent export tax, but ACTU's original proposal replaces PRRT while AEP's original announcement describes an additional levy. Therefore WoodMac 83 percent model cannot be treated as matching ACTU replacement specification without an explicit counterfactual model bridge."

taxSchemeSimilarityNotScriptCopy :
  Typed.StrongHistoricalTransfer actuReplacementVsAEPAddOnSpecification → ⊥
taxSchemeSimilarityNotScriptCopy witness =
  Typed.economicArgumentSimilarityIsNotHistoricalMethodTransfer
    (Typed.relationIsTransfer witness)

data Same25PcTaxHeadlineWorld : Set where
  replacesExistingPRRT stacksOnExistingPRRT : Same25PcTaxHeadlineWorld

data Displayed25PcRate : Set where
  same25PcLabel : Displayed25PcRate

data EffectivePolicyInstrument : Set where
  replacementInstrument additionalInstrument : EffectivePolicyInstrument

taxRateLabel : Same25PcTaxHeadlineWorld → Displayed25PcRate
taxRateLabel _ = same25PcLabel

taxPolicyMeaning : Same25PcTaxHeadlineWorld → EffectivePolicyInstrument
taxPolicyMeaning replacesExistingPRRT = replacementInstrument
taxPolicyMeaning stacksOnExistingPRRT = additionalInstrument

sameRateDifferentTaxInstrument : INF.NonFactorabilityWitness taxRateLabel taxPolicyMeaning
sameRateDifferentTaxInstrument =
  INF.nonFactorabilityWitness
    replacesExistingPRRT stacksOnExistingPRRT refl (λ ())

same25PcCannotDetermineInstrument :
  INF.FactorsThrough taxRateLabel taxPolicyMeaning → ⊥
same25PcCannotDetermineInstrument =
  INF.witnessRulesOutEveryFlatFactorisation sameRateDifferentTaxInstrument


-- Same displayed percentage can describe unlike policy denominators:
-- production reserved for a market vs sale value taxed on LNG exports.
australianGovernmentGasReservation2025 : Typed.SourceReceipt
australianGovernmentGasReservation2025 = Typed.sourceReceipt
  "Chris Bowen; Madeline King; Tim Ayres, joint Australian Government original"
  "Affordable gas for Australian homes and businesses"
  "2025-12-22"
  "https://minister.dcceew.gov.au/bowen/media-releases/joint-media-release-affordable-gas-australian-homes-and-businesses"
  "15-25 percent of gas production to be reserved for domestic consumers pending consultation, rather than a 25 percent export sales value tax. A proposal at that date, not independently confirmed implementation."

gasReservationIsNot25PcExportLevy : Typed.TypedGenealogyEdge
gasReservationIsNot25PcExportLevy = Typed.typedGenealogyEdge
  "RC-08" "Australian Government 2025 reservation of domestic production" "ACTU 2026 export revenue levy replacing PRRT"
  Typed.parallelEconomicArgument Typed.primary
  (australianGovernmentGasReservation2025 ∷ actu2026OriginalReplacementProposal ∷ [])
  "Both use percentage terms, but one denominator is production volume reserved, while the other is exported LNG revenue taxed. No shared policy object is established by equal numerical percentages."

reservationAndExportTaxAreNotHistoricalMethodTransfer :
  Typed.StrongHistoricalTransfer gasReservationIsNot25PcExportLevy → ⊥
reservationAndExportTaxAreNotHistoricalMethodTransfer witness =
  Typed.economicArgumentSimilarityIsNotHistoricalMethodTransfer
    (Typed.relationIsTransfer witness)


------------------------------------------------------------------------
-- 2025 to 2026 same 21.9b industry-tax statistic: forecast vs paid status.
-- Two original AEP surfaces agree numerically but do not preserve the
-- original qualification. Later survey finalisation is possible yet its
-- audited cash receipt was NOT acquired by this source comparison.
------------------------------------------------------------------------

aep2025OriginalFinancialForecast : Typed.SourceReceipt
aep2025OriginalFinancialForecast = Typed.sourceReceipt
  "Australian Energy Producers, 2025 Financial Survey release"
  "Oil and gas industry delivers record 22 billion in taxes and royalties to government revenues"
  "2025-07-27"
  "https://energyproducers.au/news/all_news/media-release-australian-oil-gas-industry-delivers-record-22-billion-in-taxes-and-royalties-to-government-revenues-in-2024-25"
  "Original industry association first-party table estimates 2024-25 total AUD21943m (13484 company tax + 1347 PRRT + 6620 royalties/excise/fees + 492 other), explicitly presented as forecast. Oil and gas together; not audited actual paid receipts."

aep2026TaxSenateSubmission : Typed.SourceReceipt
aep2026TaxSenateSubmission = Typed.sourceReceipt
  "Australian Energy Producers"
  "Senate Select Committee on Taxation of Gas Resources, 13 April 2026 original"
  "2026-04-13"
  "https://energyproducers.au/hubfs/260413%20AEP%20submission%20to%20Senate%20Select%20Committee%20on%20the%20Taxation%20of%20Gas%20Resources-3.pdf?hsLang=en-au"
  "First page original public submission says 21.9 billion taxes and royalties paid in 2024-25 while citing its 2025 survey. Original 2025 press text said expected/forecast; no revised audited final cash-payment reconciliation inspected. PDF first-page screenshot verified."

aepForecastToPaidStatusRestatement : Typed.TypedGenealogyEdge
aepForecastToPaidStatusRestatement = Typed.typedGenealogyEdge
  "RC-09" "AEP 2025 21.943b forecast gas-and-oil combined taxes" "AEP 2026 21.9b paid headline"
  Typed.reportedStatisticRestatement Typed.primary
  (aep2025OriginalFinancialForecast ∷ aep2026TaxSenateSubmission ∷ [])
  "Same original association cites its 2025 forecast when recasting rounded total as paid in 2026. Later auditing might exist, but is not established by cited original 2025 press summary alone. Numeric reappearance does not independently confirm actual remitted amounts."

-- For a fixed rounded number the evidence status forecast or actual-report
-- is not identifiable from the number itself, even when both documents are
-- genuinely first-party. This toy witness says NOTHING about whether the
-- 2026 paid assertion happens to be true in the actual economy.
data Same21BReportedWorld : Set where
  initialForecastStatus reportedAsPaidStatus : Same21BReportedWorld

data Same21BHeadline : Set where rounded21Point9B : Same21BHeadline

data SourceStatusFor21B : Set where projectedTaxTotal claimedActualTaxTotal : SourceStatusFor21B

same21BPrinted : Same21BReportedWorld → Same21BHeadline
same21BPrinted _ = rounded21Point9B

reportedStatusFor21B : Same21BReportedWorld → SourceStatusFor21B
reportedStatusFor21B initialForecastStatus = projectedTaxTotal
reportedStatusFor21B reportedAsPaidStatus = claimedActualTaxTotal

sameRoundedTaxTotalDifferentSourceStatus :
  INF.NonFactorabilityWitness same21BPrinted reportedStatusFor21B
sameRoundedTaxTotalDifferentSourceStatus =
  INF.nonFactorabilityWitness
    initialForecastStatus reportedAsPaidStatus refl (λ ())

sameTaxNumberCannotDetermineSourceStatus :
  INF.FactorsThrough same21BPrinted reportedStatusFor21B → ⊥
sameTaxNumberCannotDetermineSourceStatus =
  INF.witnessRulesOutEveryFlatFactorisation
    sameRoundedTaxTotalDifferentSourceStatus


------------------------------------------------------------------------
-- 2026 ORIGINAL ARTHUR D. LITTLE REPORT: TWO DISTINCT QUESTIONS
-- 1. Is a 25 percent rate applied to the SAME levy base?
-- 2. Is a quoted 2-percent-sized change a relative return change or a
--    percentage-point change in the internal rate of return?
--
-- Original consultant-authored report, not a third estimate: Future Group,
-- the commissioning body, released the original PDF.  A commissioned model
-- is original authorship but not funding-independent evidence.
--
-- Page 5: 25% broad-based 95-100 A$bn/decade;
--         prospective 28-32 A$bn/decade;
--         price-triggered windfall 9-11 A$bn/decade (A$8.5/GJ threshold).
-- First-year 'up to A$17bn' is an upper bound based on current volumes:
-- 10 x 17 is NOT this report's decade forecast.
-- Page 7: legacy-project IRR down 1-2 *percentage points*, not necessarily
--         a 1-2 percent relative reduction in any project's returns.
-- Page 8: marginal export diversion does not assume more total supply.
-- Page 4: 6.9% resource-rent-only vs 25.8% total tax are distinct bases.
-- Original pages 4, 5, 7, and 8 visually inspected 27 October 2026.
------------------------------------------------------------------------

adlSourceReportPublicRelease2026 : Typed.SourceReceipt
adlSourceReportPublicRelease2026 = Typed.sourceReceipt
  "Arthur D. Little Australia; commissioned by Future Group"
  "Australian Domestic Gas Export Reform: Scenario Analysis and Policy Options Assessment"
  "2026-04, public release"
  "https://www.datocms-assets.com/115668/1777429022-final-ad-little-modelling-gas-exports-15.pdf"
  "Consultant-authored primary report, pages 4-9; page 5 gives nine ten-year levy-base/rate scenarios; upper-bound first-year revenue cannot be multiplied into decade receipts. PDF charts visually inspected. Non-reliance and unverified data/model caveats retained."

futureGroup21AprOriginalRelease : Typed.SourceReceipt
futureGroup21AprOriginalRelease = Typed.sourceReceipt
  "Future Group (commissioner)"
  "New modelling shows gas export levy will significantly reduce energy costs"
  "2026-04-21"
  "https://www.datocms-assets.com/115668/1777429032-260421-export-levy-modelling.pdf"
  "Original commissioner press release labels A$17bn as an upper bound in the first year. Same ADL report as the 23 April corporate website story, not an additional independent modelling team."

adlReportCommissionedAndPublic : Typed.TypedGenealogyEdge
adlReportCommissionedAndPublic = Typed.typedGenealogyEdge
  "RC-10" "Future Group commissioner" "Arthur D. Little authored public report April 2026"
  Typed.commissionedResearch Typed.primary
  (adlSourceReportPublicRelease2026 ∷ futureGroup21AprOriginalRelease ∷ [])
  "The report identifies its commissioner and primary author, and the commissioner publicly supplies the original text. This establishes authorship and commissioning but does not certify independent verification of every price, supply or revenue projection."

adlSeventeenBFirstYearUpperBoundNotTenYearCash : Typed.TypedGenealogyEdge
adlSeventeenBFirstYearUpperBoundNotTenYearCash = Typed.typedGenealogyEdge
  "RC-11" "Arthur D. Little ten-year broad-based 25 percent scenario" "Future Group up-to-A$17bn first-year statement"
  Typed.reportedStatisticRestatement Typed.primary
  (adlSourceReportPublicRelease2026 ∷ futureGroup21AprOriginalRelease ∷ [])
  "The original page 5 has A$95-100bn per decade for broad-based 25 percent and expressly marks A$17bn as up-to based on current export volumes. First-year upper bound is not recurring ten-year average or guaranteed revenue."

adlIRRPointsVersusFutureGroupReturnsPercent : Typed.TypedGenealogyEdge
adlIRRPointsVersusFutureGroupReturnsPercent = Typed.typedGenealogyEdge
  "RC-12" "ADL report page 7 IRR down 1-2 percentage points" "Future Group 23 April summary about 2 percent average reduction in returns"
  Typed.reportedStatisticRestatement Typed.primary
  (adlSourceReportPublicRelease2026 ∷ futureGroupArthurDLittle2026 ∷ [])
  "The unit and project set are less explicit in the client's summary; percentage-point IRR and relative percentage return are different quantities. Do not assert bad faith or even numerically inconsistent results absent original baseline IRR."

-- There is a concrete collision: all three original consultant scenarios
-- display the same 25% nominal rate, but their levy bases and ten-year
-- modelled revenue ranges differ. This witnesses non-factorability without
-- assigning empirical certainty to the modelled revenue.
data ADLLevyScenario : Set where
  broadBase25 prospective25 windfall25 : ADLLevyScenario

data ADLDisplayed25Rate : Set where
  displayed25Rate : ADLDisplayed25Rate

data ADLTenYearRevenueBand : Set where
  broad95To100 prospective28To32 windfall9To11 : ADLTenYearRevenueBand

adlHeadlineRate : ADLLevyScenario → ADLDisplayed25Rate
adlHeadlineRate _ = displayed25Rate

adlTenYearBand : ADLLevyScenario → ADLTenYearRevenueBand
adlTenYearBand broadBase25 = broad95To100
adlTenYearBand prospective25 = prospective28To32
adlTenYearBand windfall25 = windfall9To11

adlSameRateDifferentRevenueBases :
  INF.NonFactorabilityWitness adlHeadlineRate adlTenYearBand
adlSameRateDifferentRevenueBases =
  INF.nonFactorabilityWitness broadBase25 prospective25 refl (λ ())

adlSame25RateCannotDetermineDecadeRevenue :
  INF.FactorsThrough adlHeadlineRate adlTenYearBand → ⊥
adlSame25RateCannotDetermineDecadeRevenue =
  INF.witnessRulesOutEveryFlatFactorisation adlSameRateDifferentRevenueBases

-- A bare value 2 with a percent symbol does not determine whether the
-- statement means two IRR percentage points or a 2% relative return change.
-- This is a loss-of-units obstruction, not proof of either empirical case.
data TwoSizedReturnClaim : Set where
  twoIRRPercentagePoints twoPercentRelativeReturn : TwoSizedReturnClaim

data BareTwoPercentDisplay : Set where
  bareTwoPercent : BareTwoPercentDisplay

data ReturnChangeUnit : Set where
  irrPercentagePoints relativePercent : ReturnChangeUnit

returnHeadlineWithoutUnits : TwoSizedReturnClaim → BareTwoPercentDisplay
returnHeadlineWithoutUnits _ = bareTwoPercent

returnChangeUnit : TwoSizedReturnClaim → ReturnChangeUnit
returnChangeUnit twoIRRPercentagePoints = irrPercentagePoints
returnChangeUnit twoPercentRelativeReturn = relativePercent

samePrintedTwoDifferentReturnUnits :
  INF.NonFactorabilityWitness returnHeadlineWithoutUnits returnChangeUnit
samePrintedTwoDifferentReturnUnits =
  INF.nonFactorabilityWitness twoIRRPercentagePoints twoPercentRelativeReturn refl (λ ())

bareTwoPercentCannotIdentifyReturnUnit :
  INF.FactorsThrough returnHeadlineWithoutUnits returnChangeUnit → ⊥
bareTwoPercentCannotIdentifyReturnUnit =
  INF.witnessRulesOutEveryFlatFactorisation samePrintedTwoDifferentReturnUnits

adlFirstPartyScenarioIsNotProofOfEditorialTransfer :
  Typed.StrongHistoricalTransfer adlIRRPointsVersusFutureGroupReturnsPercent → ⊥
adlFirstPartyScenarioIsNotProofOfEditorialTransfer witness =
  Typed.headlineNumberRestatementIsNotHistoricalMethodTransfer
    (Typed.relationIsTransfer witness)
