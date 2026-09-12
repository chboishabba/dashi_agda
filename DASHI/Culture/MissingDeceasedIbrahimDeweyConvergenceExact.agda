module DASHI.Culture.MissingDeceasedIbrahimDeweyConvergenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal
import DASHI.Culture.MissingDeceasedIbrahimInvestigativeParetoExact as Pareto

------------------------------------------------------------------------
-- IBRAHIM / DEWEY CONVERGENCE FOR SCIENTIST ACQUISITION
--
-- Thin crosswalk only. Ibrahim-style semantic traversal and Dewey shelving are
-- independent external routing coordinates. Agreement between them may raise
-- acquisition priority but cannot manufacture semantic edges, evidence
-- authority, person identity, same-object identity, custody or succession.
--
-- Ibrahim attribution:
-- Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First
-- Link Network", Journal of Computational Science 19 (2017), 21-30.
-- DOI 10.1016/j.jocs.2016.12.001; arXiv:1605.00309.
------------------------------------------------------------------------

record IbrahimDeweyConvergenceReceipt : Set where
  constructor ibrahim-dewey-convergence-receipt
  field
    lane : String
    paretoTarget : String
    ibrahimRoute : String
    deweyRoute : String
    qidCoordinates : String
    stableIdentifiers : String
    primaryObjectClass : String
    routesConvergeOnSameAcquisitionSurface : Bool
    convergenceRaisesSearchPriority : Bool
    convergenceCreatesSemanticEdge : Bool
    convergenceCreatesEvidenceAuthority : Bool
    exactPrimaryObjectStillRequired : Bool
    boundedReading : String

open IbrahimDeweyConvergenceReceipt public

amyIbrahimDeweyConvergence : IbrahimDeweyConvergenceReceipt
amyIbrahimDeweyConvergence = ibrahim-dewey-convergence-receipt
  "Amy Eskridge / POAMS"
  "Pareto.amyReleaseMetadataPareto"
  "technical report -> research/report administration -> STI/release metadata -> release-system archaeology"
  "530 Physics + NASA Subject Category 70; metadata/documentation traversal 025.3 / 005.7"
  "technical report Q3099732; research Q42240; NASA Q23548; MSFC Q618696"
  "NTRS 20205010911; NASA/TM-20205010911; M-1531; SAA8-1519855; NF-1676/STRIVES identity unresolved; legacy EDAA/NF-1676B retained as predecessor lineage"
  "primary NASA/MSFC STI compliance or release-authorisation object carrying the POAMS NF-1676/STRIVES approval identity and any migrated legacy EDAA lineage"
  true true false false true
  "Ibrahim and Dewey both route away from more POAMS topical science and toward report-series/release metadata. NASA's 2020 CIO annual report says STRIVES was fully adopted agency-wide by May 2020, NTRS transitioned by July and legacy STI applications were retired by August. POAMS was acquired by NTRS on 2020-12-01. The strongest expected approval namespace is therefore NF-1676/STRIVES-era release metadata; a legacy MSFC EDAA remains relevant only as predecessor/migration lineage unless a primary record proves otherwise."

rezaIbrahimDeweyConvergence : IbrahimDeweyConvergenceReceipt
rezaIbrahimDeweyConvergence = ibrahim-dewey-convergence-receipt
  "Monica Jacinto Reza / materials processing"
  "Pareto.rezaIdentityAndRolePareto"
  "patent -> intellectual property -> assignment/inventor identity; separate personnel branch"
  "346.048 intellectual property + 620 engineering"
  "patent Q253623; intellectual property Q131257; Monica Jacinto Q139385030"
  "US20030053926A1; US20040208777A1; AIAA 99-2754; AIAA SciTech 2023 Aerojet carrier; LASD 025-00905-1257-400"
  "primary patent/person identity record plus primary JPL/Caltech personnel record"
  true true false false true
  "Both routing systems privilege legal/IP identity records over secondary role repetition. AIAA 99-2754 is retained as the verified paper-number coordinate; a DOI is not promoted without an authoritative landing object. The primary AIAA SciTech 2023 carrier narrows the last paid pre-JPL state to Aerojet Rocketdyne, but does not itself pay the later Reza/JPL transition."

mccaslandIbrahimDeweyConvergence : IbrahimDeweyConvergenceReceipt
mccaslandIbrahimDeweyConvergence = ibrahim-dewey-convergence-receipt
  "William Neil McCasland / DBE Consulting"
  "Pareto.mccaslandEntityHistoryPareto"
  "company register -> company/legal entity"
  "338.7 enterprises + 650 management"
  "company register Q134611895; trade register Q1394657"
  "Albuquerque address 11039 Bridgepointe NE; jurisdictional legal-entity ID unresolved"
  "primary government company-register/entity-history record"
  true true false false true
  "Both routes converge on the jurisdictional entity record. Primary 2011/2017 carriers tie James Tegnelia and DBE Consulting to the 11039 Bridgepointe address, while current public mirrors contain other DBE-name/address surfaces and unrelated same-label firms. Biographies, addresses and name matching remain search leads until the New Mexico legal entity is identified exactly."

maiwaldIbrahimDeweyConvergence : IbrahimDeweyConvergenceReceipt
maiwaldIbrahimDeweyConvergence = ibrahim-dewey-convergence-receipt
  "Frank W. Maiwald / action spectroscopy"
  "Pareto.maiwaldDataPareto"
  "spectroscopy -> research data -> data/metadata -> repository/deposit"
  "543.5 spectroscopy + 540 chemistry; metadata traversal only"
  "spectroscopy Q483666; research data Q15809982; data Q42848; metadata Q180160; JPL Q189325 institution only"
  "10.1021/acs.jpca.4c03552; 10.26434/chemrxiv-2024-2tvc6; NTRS 13797709699197; 10.1021/acs.jpca.5c03141"
  "primary repository/deposit or instrument/data-management record"
  true true false false true
  "Both routes say that another publication has low marginal value. ACS exposes the supporting-information asset through Figshare-backed infrastructure, but the located SI contains calculated/derived material rather than an identified raw instrument dataset. The missing conclusion-paying object remains a deposit/instrument-data manifest tying raw and reduced spectra to poster/article/SI figures."

leblancIbrahimDeweyConvergence : IbrahimDeweyConvergenceReceipt
leblancIbrahimDeweyConvergence = ibrahim-dewey-convergence-receipt
  "Joshua LeBlanc / SNP I&C TechMat"
  "Pareto.leblancFreezePareto"
  "metadata -> version/freeze/governance manifestation"
  "621 applied physics + 629 engineering; metadata traversal only"
  "metadata Q180160; person QID unresolved"
  "NTRS 20250008475; WBS 658133.04.01.22.01.06; DOI 10.13182/NPICHMIT25-46370"
  "primary NASA version/freeze metadata or dated programme roster"
  true true false false true
  "The two routes converge on freeze/governance metadata because the public webinar is a post-loss manifestation that still preserves a pre-loss role label."

loureiroIbrahimDeweyConvergence : IbrahimDeweyConvergenceReceipt
loureiroIbrahimDeweyConvergence = ibrahim-dewey-convergence-receipt
  "Nuno F. Loureiro / student and resource succession"
  "Pareto.loureiroFormalSuccessionPareto"
  "metadata/administrative record -> advisor/repository/allocation governance"
  "530 physics; academic-administration metadata kept separate from scientific content"
  "Loureiro Q51287446"
  "10.1017/S002237782510113X; arXiv 2505.08983; 10.1103/j5p4-jj3d; DE-FG02-91ER54109; FES-ERCAP0026577"
  "primary MIT advisor/graduate-programme record plus primary repository/dataset record"
  true true false false true
  "Scientific continuation is already paid, so both routes converge on administrative succession rather than additional publication discovery."

------------------------------------------------------------------------
-- Explicit reuse of the generic DASHI traversal firewall.
------------------------------------------------------------------------

record IbrahimDeweyConvergenceBoundary : Set where
  constructor ibrahim-dewey-convergence-boundary
  field
    dashiTraversalPolicyReused : Bool
    deweyAdjacencyCreatesSemanticEdge : Bool
    qidIdentityCreatesProof : Bool
    ibrahimRouteCreatesTheoremImplication : Bool
    dualRouteAgreementCreatesAuthority : Bool
    dualRouteAgreementMayRaiseAcquisitionPriority : Bool
    sourceSpecificOwnerRemainsAuthoritative : Bool

open IbrahimDeweyConvergenceBoundary public

canonicalIbrahimDeweyConvergenceBoundary : IbrahimDeweyConvergenceBoundary
canonicalIbrahimDeweyConvergenceBoundary = ibrahim-dewey-convergence-boundary
  true false false false false true true
