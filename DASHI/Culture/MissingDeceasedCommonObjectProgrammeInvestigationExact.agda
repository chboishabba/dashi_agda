module DASHI.Culture.MissingDeceasedCommonObjectProgrammeInvestigationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedCommonObjectProgrammeDiscriminatorExact as Common

------------------------------------------------------------------------
-- FIRST OBJECT-FIRST INVESTIGATION FIXTURE
--
-- Current public evidence pays institutional/ecosystem overlap in several
-- places, but this fixture does not yet contain a literal common programme or
-- common object naming two of the retained twenty scientists.  That absence is
-- a search state, not a proof that no such programme exists.
------------------------------------------------------------------------

jplHicksMaiwaldInstitutionalReceipt : Common.CrossPersonProgrammeReceipt
jplHicksMaiwaldInstitutionalReceipt = Common.cross-person-programme-receipt
  "JPL institutional research ecosystem"
  "Michael David Hicks"
  "Frank W. Maiwald"
  "NASA Jet Propulsion Laboratory / California Institute of Technology"
  "JPL Hicks public science pages; JPL Principal designation listing Frank W. Maiwald; JPL SURP SP23012"
  Common.thematicAdjacency
  false
  "common employer does not pay a shared project, apparatus, work package, custody chain or event cause"

nudtChenFengInstitutionalReceipt : Common.CrossPersonProgrammeReceipt
nudtChenFengInstitutionalReceipt = Common.cross-person-programme-receipt
  "NUDT strategic research ecosystem"
  "Chen Shuming"
  "Feng Yanghe"
  "National University of Defense Technology"
  "NUDT Galaxy/Feiteng institutional history; NUDT systems-engineering young-talent task article"
  Common.thematicAdjacency
  false
  "same university and strategic mission do not pay one common programme or coordinated event cause"

nudtFengZhangInstitutionalReceipt : Common.CrossPersonProgrammeReceipt
nudtFengZhangInstitutionalReceipt = Common.cross-person-programme-receipt
  "NUDT strategic research ecosystem"
  "Feng Yanghe"
  "Zhang Daibing"
  "National University of Defense Technology"
  "NUDT Feng military-intelligence task article; NUDT Zhang Daibing snake-robot history"
  Common.thematicAdjacency
  false
  "military AI and unmanned-systems work at one university remain different technical objects absent a common task/work-package receipt"

rezaMcCaslandUnconfirmedLink : Common.CrossPersonProgrammeReceipt
rezaMcCaslandUnconfirmedLink = Common.cross-person-programme-receipt
  "AFRL / Mondaloy alleged linkage"
  "Monica Jacinto / Monica Reza"
  "William Neil McCasland"
  "public allegation of an AFRL-funded advanced-materials connection"
  "U.S. House Oversight 2026-04-20 DOE Missing Scientists Letter describes the direct link as unconfirmed public reporting; AFRL official history places McCasland as Space Vehicles director 2001-2004 and AFRL commander 2011-2013"
  Common.thematicAdjacency
  false
  "institutional AFRL overlap and later command authority do not pay a direct professional relationship or same Mondaloy work package"

ningAmyHuntsvilleAdjacency : Common.CrossPersonProgrammeReceipt
ningAmyHuntsvilleAdjacency = Common.cross-person-programme-receipt
  "Huntsville / Marshall gravity-propulsion research ecosystem"
  "Ning Li"
  "Amy Eskridge"
  "Huntsville/Marshall advanced-propulsion and gravity-modification ecosystem"
  "Ning Li's 1997 Physica C paper carries NASA Marshall/UAH affiliations; Amy's public programme is Huntsville-based, but no same programme identifier has been recovered"
  Common.thematicAdjacency
  false
  "geography and topical proximity do not pay a shared apparatus, contract, team, handoff or common programme"

fangMcCaslandDateCoincidence : Common.CrossPersonProgrammeReceipt
fangMcCaslandDateCoincidence = Common.cross-person-programme-receipt
  "cross-country date-coincidence control"
  "Fang Daining"
  "William Neil McCasland"
  "reported same calendar date, 2026-02-27"
  "event-date sources only"
  Common.thematicAdjacency
  false
  "same date across unrelated countries/institutions does not pay shared programme, operational action or cause"

currentCrossPersonReceipts : List Common.CrossPersonProgrammeReceipt
currentCrossPersonReceipts =
  jplHicksMaiwaldInstitutionalReceipt ∷
  nudtChenFengInstitutionalReceipt ∷
  nudtFengZhangInstitutionalReceipt ∷
  rezaMcCaslandUnconfirmedLink ∷
  ningAmyHuntsvilleAdjacency ∷
  fangMcCaslandDateCoincidence ∷ []

literalCrossPersonReceiptCount : Nat
literalCrossPersonReceiptCount = 0

institutionalOrThematicAdjacencyCount : Nat
institutionalOrThematicAdjacencyCount = 6

------------------------------------------------------------------------
-- Candidate discrimination states.
------------------------------------------------------------------------

longDurationAssessment : Common.HypothesisDiscriminationReceipt
longDurationAssessment = Common.hypothesis-discrimination-receipt
  "long-duration autonomous extreme-environment platform"
  Common.H1
  12 0 0
  "the same capability mix is ordinary across aerospace portfolios; no same-object cross-person requirement/specification has been located"
  "high capability fit; programme identity unpaid"
  false

highEnergyAssessment : Common.HypothesisDiscriminationReceipt
highEnergyAssessment = Common.hypothesis-discrimination-receipt
  "high-energy experimental/test infrastructure"
  Common.H1
  10 0 0
  "accelerators, materials, controls and diagnostics commonly coexist across large laboratories without a single hidden programme"
  "institutional/facility-family plausibility only; literal common object unpaid"
  false

advancedPropulsionAssessment : Common.HypothesisDiscriminationReceipt
advancedPropulsionAssessment = Common.hypothesis-discrimination-receipt
  "advanced propulsion / anomalous-field testbed"
  Common.H1
  7 0 0
  "Ning's published programme includes negative/null constraints; Amy technical authorship and cross-person apparatus identity remain unpaid"
  "speculative capability convergence only; no operational exotic-propulsion receipt"
  false

portfolioAssessment : Common.HypothesisDiscriminationReceipt
portfolioAssessment = Common.hypothesis-discrimination-receipt
  "strategic multi-object R&D portfolio"
  Common.H1
  20 0 0
  "shared strategic-sector exposure and multiple institutional clusters explain breadth without requiring one machine"
  "currently the least-invented broad model, but literal cross-person programme identity remains unpaid"
  false

currentAssessments : List Common.HypothesisDiscriminationReceipt
currentAssessments =
  longDurationAssessment ∷ highEnergyAssessment ∷ advancedPropulsionAssessment ∷ portfolioAssessment ∷ []

------------------------------------------------------------------------
-- Current hypothesis status.
------------------------------------------------------------------------

h0StillAdmissible : Bool
h0StillAdmissible = true

h1CurrentlyBestPaidByPublicEvidence : Bool
h1CurrentlyBestPaidByPublicEvidence = true

h2LiteralProgrammeReceiptPaid : Bool
h2LiteralProgrammeReceiptPaid = false

h3OperationalEvidencePaid : Bool
h3OperationalEvidencePaid = false

searchResidualCreatesKnownAbsence : Bool
searchResidualCreatesKnownAbsence = false

congressionalConcernPaysCommonCause : Bool
congressionalConcernPaysCommonCause = false

unconfirmedPublicReportingPaysDirectProfessionalLink : Bool
unconfirmedPublicReportingPaysDirectProfessionalLink = false

institutionalClusterPaysSameProgramme : Bool
institutionalClusterPaysSameProgramme = false

nextHighestAlphaAcquisition : String
nextHighestAlphaAcquisition =
  "search exact programme/contract/grant/facility/work-package identifiers that name two or more retained scientists/components before deepening thematic or temporal coincidence"
