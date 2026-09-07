module DASHI.Cognition.PNF.SensibLawCountryRealisedRepairSourceAtlasV02Exact where

------------------------------------------------------------------------
-- COUNTRY / REALISED REPAIR SOURCE ATLAS V02
--
-- Additive source metadata only.  The atlas does not promote source claims into
-- legal holdings, empirical laws, causal explanations, political conclusions or
-- DASHI theorem authority.  Each downstream proposition must cite the source
-- object whose author/title/publication/DOI provenance actually supports it.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

nnttNationalMap2025 : Source.AttributedSource
nnttNationalMap2025 = Source.mkNoDOISource
  "National Native Title Tribunal"
  "Native title determinations / claims map of Australia (October 2025)"
  "National Native Title Tribunal"
  "2025"
  "https://www.nntt.gov.au/assistance/Geospatial/Pages/Maps.aspx"
  Source.governmentSource
  "Primary administrative/geospatial source for native-title determination categories. Percentages used downstream are not silently inferred where the map itself has not supplied them in machine-readable form."
  Source.publicAttribution

aapNativeTitleFactcheck2025 : Source.AttributedSource
aapNativeTitleFactcheck2025 = Source.mkNoDOISource
  "George Driver / AAP FactCheck"
  "Indigenous 'ownership and control' figure vastly overstated"
  "Australian Associated Press"
  "2025"
  "https://aap.com.au/factcheck/indigenous-ownership-and-control-figure-vastly-overstated/"
  Source.newsSource
  "Secondary fact-check reporting NNTT map/spokesperson figures: 55.4% determination coverage, about 31% non-exclusive native title and 15.4% exclusive native title; also reports expert cautions that determination/exclusive title do not equal sovereignty or absolute control."
  Source.publicAttribution

productivityCommissionClosingGapReview2024 : Source.AttributedSource
productivityCommissionClosingGapReview2024 = Source.mkNoDOISource
  "Productivity Commission"
  "Review of the National Agreement on Closing the Gap"
  "Australian Government Productivity Commission"
  "2024"
  "https://www.pc.gov.au/inquiries-and-research/closing-the-gap-review/report/"
  Source.governmentSource
  "Official review source for findings that fundamental change is required and recommendations to share power, recognise/support Indigenous Data Sovereignty, rethink government systems/culture and strengthen accountability."
  Source.publicAttribution

productivityCommissionADCR2026 : Source.AttributedSource
productivityCommissionADCR2026 = Source.mkNoDOISource
  "Productivity Commission"
  "Closing the Gap Annual Data Compilation Report July 2026"
  "Australian Government Productivity Commission"
  "2026"
  "https://www.pc.gov.au/closing-the-gap-data/annual-data-report/2026/"
  Source.governmentSource
  "Official statistical compilation. Downstream use is descriptive: of 19 targets, 1 met, 3 on track, 5 improving but off track and 4 worsening. These statistics do not by themselves identify a single cause."
  Source.publicAttribution

aiatsisPBCSurvey2021 : Source.AttributedSource
aiatsisPBCSurvey2021 = Source.mkNoDOISource
  "Australian Institute of Aboriginal and Torres Strait Islander Studies"
  "Report on the 2019 Survey of Prescribed Bodies Corporate"
  "AIATSIS"
  "2021"
  "https://aiatsis.gov.au/sites/default/files/research_pub/AIATSIS%20-%20PBC%20Survey%20Report%20-%202021.pdf"
  Source.institutionalSource
  "Institutional survey source for PBC-reported resource constraints. Survey responses and the institute's synthesis remain distinct from a claim that every PBC has the same funding deficit."
  Source.publicAttribution

woodsEtAlPBCFunding2021 : Source.AttributedSource
woodsEtAlPBCFunding2021 = Source.mkDOISource
  "Kaely Woods; Francis Markham; Diane Smith; John Taylor; Belinda Burbidge; Yonatan Dinku"
  "Toward a Perpetual Funding Model for Native Title Prescribed Bodies Corporate"
  "CAEPR Commissioned Report No. 7, Australian National University"
  "2021"
  "10.25911/6FPY-AV98"
  "https://researchportalplus.anu.edu.au/en/publications/toward-a-perpetual-funding-model-for-native-title-prescribed-bodi/"
  (Source.namedSourceKind "commissioned academic policy report")
  "Commissioned academic report estimating Australian Government core-compliance funding at about 10% of actual PBC compliance cost. Estimate remains report-authored, not a government admission or universal PBC-specific ratio."
  Source.publicAttribution

abcJuukanFiveYears2025 : Source.AttributedSource
abcJuukanFiveYears2025 = Source.mkNoDOISource
  "Mietta Adams; Alistair Bates"
  "Traditional owners still angry five years after Juukan Gorge destruction"
  "ABC News / ABC Pilbara"
  "2025"
  "https://www.abc.net.au/news/2025-05-24/five-years-since-juukan-gorge-destruction-pilbara-heritage-laws/105295474"
  Source.newsSource
  "Contemporary reporting source for the 2021 heritage-law reform, its repeal after about five weeks in operation, restoration of the 1972 regime with amendments, and attributed Traditional Owner/archaeologist claims about continuing heritage destruction and inadequate protection."
  Source.publicAttribution

abcWanganJagalingouQCA2026 : Source.AttributedSource
abcWanganJagalingouQCA2026 = Source.mkNoDOISource
  "Liam McNally; Yasmine Wright Gittins"
  "Doongmabulla Springs decision leaves Qld government to weigh appeal or face trial"
  "ABC News / ABC Tropical North"
  "2026"
  "https://www.abc.net.au/news/2026-02-11/doongmabulla-springs-qld-government-appeal-or-face-trial/106305714"
  Source.newsSource
  "Secondary reporting of the 28 January 2026 Queensland Court of Appeal result restoring the cultural custodians' case for full Supreme Court trial. It is not the judgment itself and does not establish final merits or a protection order."
  Source.publicAttribution

abcWanganJagalingouTrial2026 : Source.AttributedSource
abcWanganJagalingouTrial2026 = Source.mkNoDOISource
  "Liam O'Connell; Yasmine Wright Gittins"
  "Doongmabulla Springs case proceeds to civil trial in Queensland's Supreme Court"
  "ABC News / ABC Tropical North"
  "2026"
  "https://www.abc.net.au/news/2026-03-11/doongmabulla-springs-trial-proceeds-to-qld-supreme-court/106440126"
  Source.newsSource
  "Secondary reporting that the restored Doongmabulla Springs proceeding will proceed to trial; final trial merits/outcome remain open."
  Source.publicAttribution

highCourtTimberCreek2019 : Source.AttributedSource
highCourtTimberCreek2019 = Source.mkNoDOISource
  "High Court of Australia"
  "Northern Territory v Griffiths (Timber Creek compensation case) [2019] HCA 7"
  "High Court of Australia"
  "2019"
  "https://www.hcourt.gov.au/cases-and-judgments/judgments/judgments-1998-current/northern-territory-v-mr-griffiths-deceased-and-lorraine-jones-behalf-ngaliwurru-and-nungali-peoples"
  (Source.namedSourceKind "primary judicial authority")
  "Primary judicial authority for native-title compensation principles. Numeric summary values should be attributed to the judgment/orders or an identified reliable summary, not to the atlas itself."
  Source.publicAttribution

aiatsisTimberCreekSummary : Source.AttributedSource
aiatsisTimberCreekSummary = Source.mkNoDOISource
  "AIATSIS"
  "Northern Territory v Mr A. Griffiths (deceased) and Lorraine Jones on behalf of the Ngaliwurru and Nungali Peoples [2019] HCA 7"
  "AIATSIS Native Title and Traditional Ownership resource"
  "2019"
  "https://aiatsis.gov.au/ntpd-resource/1810"
  Source.institutionalSource
  "Institutional case summary recording the final orders: $320,250 economic loss, $910,100 interest and $1.3 million cultural loss, total $2,530,350. It remains a summary of the High Court authority, not an independent holding."
  Source.publicAttribution

ullmannVonStaden2024 : Source.AttributedSource
ullmannVonStaden2024 = Source.mkDOISource
  "Andreas J. Ullmann; Andreas von Staden"
  "A Room Full of 'Views': Introducing a New Dataset to Explore Compliance with the Decisions of the UN Human Rights Treaty Bodies' Individual Complaints Procedures"
  "Journal of Conflict Resolution 68(2-3), 534-561"
  "2024"
  "10.1177/00220027231160460"
  "https://journals.sagepub.com/doi/10.1177/00220027231160460"
  Source.academicArticleSource
  "Peer-reviewed treaty-body Views dataset covering published individual-complaint decisions 1979-2019. Reports overall compliance rates of about 19-39% depending definition/missing-value assumptions and a 0.23 mean for the strict full-compliance dummy. Billy (2022) is outside the dataset."
  Source.publicAttribution

hrcAustraliaConcludingObservations2017 : Source.AttributedSource
hrcAustraliaConcludingObservations2017 = Source.mkNoDOISource
  "United Nations Human Rights Committee"
  "Concluding observations on the sixth periodic report of Australia, CCPR/C/AUS/CO/6"
  "United Nations Human Rights Committee"
  "2017"
  "https://docstore.ohchr.org/SelfServices/FilesHandler.ashx"
  Source.institutionalSource
  "Primary treaty-body source recording Australia's good-faith consideration position and the Committee's concern about Australia's repeated failure to implement its Views. Qualitative institutional assessment, not a numeric Australia-specific rate."
  Source.publicAttribution

hrcFollowUpGuidelines2023 : Source.AttributedSource
hrcFollowUpGuidelines2023 = Source.mkNoDOISource
  "United Nations Human Rights Committee"
  "Guidelines on the procedure for follow-up to Views, CCPR/C/162"
  "United Nations Human Rights Committee"
  "2023"
  "https://docstore.ohchr.org/SelfServices/FilesHandler.ashx"
  Source.institutionalSource
  "Primary procedural source for follow-up status, closure and suspension rules. The five-year no-information suspension rule is an administrative follow-up rule; statistical right-censoring is a DASHI/model interpretation, not Committee terminology."
  Source.publicAttribution

australianHumanRightsCommissionUPR2025 : Source.AttributedSource
australianHumanRightsCommissionUPR2025 = Source.mkNoDOISource
  "Australian Human Rights Commission"
  "Australia's Fourth Universal Periodic Review: Commission submission"
  "Australian Human Rights Commission"
  "2025"
  "https://humanrights.gov.au/media/documents-files-PDFs/2025-09/The-Commissions-submission-to-Australias-Fourth-Universal-Periodic-Review_0.pdf"
  Source.institutionalSource
  "Separate-mechanism benchmark: of 177 supported UPR3 recommendations, 6% fully implemented, 86% partly and 7% not implemented. UPR is not the ICCPR Optional Protocol individual-communications regime and cannot be pooled as the same reference class without an explicit bridge."
  Source.publicAttribution

allSources : List Source.AttributedSource
allSources =
  nnttNationalMap2025
  ∷ aapNativeTitleFactcheck2025
  ∷ productivityCommissionClosingGapReview2024
  ∷ productivityCommissionADCR2026
  ∷ aiatsisPBCSurvey2021
  ∷ woodsEtAlPBCFunding2021
  ∷ abcJuukanFiveYears2025
  ∷ abcWanganJagalingouQCA2026
  ∷ abcWanganJagalingouTrial2026
  ∷ highCourtTimberCreek2019
  ∷ aiatsisTimberCreekSummary
  ∷ ullmannVonStaden2024
  ∷ hrcAustraliaConcludingObservations2017
  ∷ hrcFollowUpGuidelines2023
  ∷ australianHumanRightsCommissionUPR2025
  ∷ []

atlas : Source.AttributedSourceAtlas
atlas = Source.mkSourceAtlas
  "SensibLaw Country realised-repair / HRC calibration sources V02"
  "DASHI.Cognition.PNF.SensibLawCountryRealisedRepairSourceAtlasV02Exact"
  allSources
  "Source identities for native-title coverage/control, Closing the Gap power/outcome reporting, PBC resourcing, Juukan recurrence/protection, Wangan-Jagalingou litigation, Timber Creek compensation, UN treaty-body compliance reference classes and UPR triangulation. Each substantive proposition remains source- and consumer-bounded."

sourceCountIsFifteen : Source.sourceCount allSources ≡ 15
sourceCountIsFifteen = refl

atlasDoesNotCreateAuthority : Source.atlasCreatesAuthority atlas ≡ false
atlasDoesNotCreateAuthority = refl
