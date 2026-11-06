module DASHI.Law.SensibLawWoogarooProponentEvidenceAdversarialAudit20261106Exact where

------------------------------------------------------------------------
-- EPBC 2019/8575: first-order source-arithmetic + all-domain evidence audit.
--
-- The proponent's source is primary for what the proponent ASSERTS, not
-- independent authority for the ecology, legal compliance, future benefit
-- or validity of its own score/model. Admissions against a positive claim
-- can constrain that claim without becoming independently verified fauna
-- observations. Source uncertainty and source contradiction are distinct.
--
-- Original attribution: Saunders Havill Group / Cherish (Springfield PD
-- and Mount Walker West A16), One Environment (Avonvale A15), BAAM (Esk),
-- QUT and QCC original submissions, Commonwealth original approval.
-- Reuses the earlier #1276 finite adversary rather than replacing it.
-- No Agda proof here constructs an ecological field result, Court filing,
-- decision-maker finding, confidence interval or official OAG recompute.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooOffsetSATAdversarial20261106Exact as SAT
import DASHI.Law.SensibLawWoogarooAdversarialLogicalTests20261028Exact as Prior

------------------------------------------------------------------------
-- A16: Table 45's component SUM contradicts its published AU4 TOTAL.
-- The surrounding narrative uses AU4 habitat-use 15 rather than the
-- table's 5, which would make the published total 40. We cannot choose
-- which original datum ought to control without the raw instrument.
------------------------------------------------------------------------

au1ComponentSum : Nat
au1ComponentSum = 10 + 5 + 0 + 5
au2ComponentSum : Nat
au2ComponentSum = 10 + 5 + 0 + 5
au3ComponentSum : Nat
au3ComponentSum = 10 + 15 + 10 + 5
au4ComponentSumInTable : Nat
au4ComponentSumInTable = 10 + 5 + 10 + 5
au4ComponentSumInProse : Nat
au4ComponentSumInProse = 10 + 15 + 10 + 5

au1ComponentsMatchPublished : au1ComponentSum ≡ 20
au1ComponentsMatchPublished = refl
au2ComponentsMatchPublished : au2ComponentSum ≡ 20
au2ComponentsMatchPublished = refl
au3ComponentsMatchPublished : au3ComponentSum ≡ 40
au3ComponentsMatchPublished = refl
au4TableComponentsSumTo30 : au4ComponentSumInTable ≡ 30
au4TableComponentsSumTo30 = refl
au4ProseComponentsSumTo40 : au4ComponentSumInProse ≡ 40
au4ProseComponentsSumTo40 = refl

au4TableCannotSumToPublished40 :
  au4ComponentSumInTable ≡ 40 → ⊥
au4TableCannotSumToPublished40 ()

au4PublishedTotal : Nat
au4PublishedTotal = 40

-- Exact weighted 4/70 species-stocking component numerators:
-- 30*4=120 versus 40*4=160. These are fractions of 70,
-- NOT an OAG offset percentage and NOT revised habitat-quality input.
au4ComponentWeightedNumerator : au4ComponentSumInTable * 4 ≡ 120
au4ComponentWeightedNumerator = refl
au4PublishedWeightedNumerator : au4PublishedTotal * 4 ≡ 160
au4PublishedWeightedNumerator = refl

------------------------------------------------------------------------
-- A16 Table 13: both non-remnant/low-use AU1 and AU2 are the ENTIRE
-- reported koala offset contribution; AU3 and AU4 have ZERO credited.
-- This does NOT establish that quality restoration cannot work.
------------------------------------------------------------------------

mwwKolaPercentHundredthsAU1 : Nat
mwwKolaPercentHundredthsAU1 = 1634
mwwKolaPercentHundredthsAU2 : Nat
mwwKolaPercentHundredthsAU2 = 3368
mwwKolaPercentHundredthsAU3 : Nat
mwwKolaPercentHundredthsAU3 = 0
mwwKolaPercentHundredthsAU4 : Nat
mwwKolaPercentHundredthsAU4 = 0

bothLowUseAUsExplainEntirePublishedKoalaCredit :
  mwwKolaPercentHundredthsAU1 + mwwKolaPercentHundredthsAU2 ≡ 5002
bothLowUseAUsExplainEntirePublishedKoalaCredit = refl

otherTwoAUsHaveNoPublishedKoalaCredit :
  mwwKolaPercentHundredthsAU3 + mwwKolaPercentHundredthsAU4 ≡ 0
otherTwoAUsHaveNoPublishedKoalaCredit = refl

allFourReportedKoalaCredit :
  mwwKolaPercentHundredthsAU1 + mwwKolaPercentHundredthsAU2 +
  mwwKolaPercentHundredthsAU3 + mwwKolaPercentHundredthsAU4 ≡ 5002
allFourReportedKoalaCredit = refl

mwwOffsetAreaInTenths :
  508 + 1047 + 620 + 81 ≡ 2256
mwwOffsetAreaInTenths = refl

------------------------------------------------------------------------
-- A16 Table 2 and main PD A26 expose a 0.98 ha cross-table mismatch
-- of the AU1 impact area (110.89 versus 111.87 ha). Do not erase it
-- through rounding: exact 0.98 ha, requiring distinct-map/version check.
------------------------------------------------------------------------

a16Table2ImpactAreaHundredths : 11089 + 1613 ≡ 12702
a16Table2ImpactAreaHundredths = refl

mainPDA26ImpactAreaHundredths : 11187 + 1613 ≡ 12800
mainPDA26ImpactAreaHundredths = refl

crossTableAreaDifferenceHundredths : 12702 + 98 ≡ 12800
crossTableAreaDifferenceHundredths = refl

------------------------------------------------------------------------
-- Mandatory review coordinates cover all MATERIAL EVIDENCE FAMILIES.
-- Each reported fact requires source, underlying data, scope, scoring,
-- outcome direction and external validation independently. This total
-- function is an AUDIT ROUTER, not a proof that every PD sentence was
-- extracted or that any item has passed independent review.
------------------------------------------------------------------------

data EvidenceFamily : Set where
  actionGeometry impactKoala impactFlyingFox impactSwiftParrot
    impactRegentHoneyeater : EvidenceFamily
  speciesOccurrence surveyDesign surveySpatialJoin : EvidenceFamily
  habitatCondition habitatConnectivity habitatPopulationFunction : EvidenceFamily
  offsetAreaAccounting qualityScoring futureHabitatValue
    futureTreeCounts : EvidenceFamily
  counterfactualRisk confidenceAssumptions ecologicalTimeLag
    ecologicalAdditionality : EvidenceFamily
  proposedMitigation retainedHabitat cumulativeFragmentation : EvidenceFamily
  legalSecurity declarationsRegistration commencementCompliance : EvidenceFamily
  financialAgreement landTenure commentResponses decisionReasons : EvidenceFamily

data AuditStage : Set where
  sourceReportedOnly : AuditStage
  directSourceArithmeticConflict : AuditStage
  exactSourceArithmeticChecked : AuditStage
  independentlyConfirmed : AuditStage
  legallyAdjudicated : AuditStage

record ProponentEvidenceReview : Set where
  constructor evidence-review
  field
    domain : EvidenceFamily
    sourcePointer : String
    stage : AuditStage
    exactQuestion : String
    corroboratedOutsideProponent : Bool
    independentlyVerifiedConservationBenefit : Bool
open ProponentEvidenceReview public

review : EvidenceFamily → ProponentEvidenceReview
review actionGeometry = evidence-review actionGeometry
  "PD A.i Table A26; A16 Table 2"
  directSourceArithmeticConflict
  "Why does the A16 AU sum yield 127.02 ha where the main PD yields 128.00 ha?"
  false false
review impactKoala = evidence-review impactKoala
  "PD A.i Table A26; Section 6.1" sourceReportedOnly
  "Do independent survey and mapped impacts support 128 ha / MHQA 6.78 and local habitat function?"
  false false
review impactFlyingFox = evidence-review impactFlyingFox
  "PD A.i Section 6.1" sourceReportedOnly
  "Do flowering resources, seasonality and observed use support the 7.47 FHA impact score?"
  false false
review impactSwiftParrot = evidence-review impactSwiftParrot
  "PD A.i Section 6.1" sourceReportedOnly
  "Are 9983 mapped preferred forage features independently accounted for?"
  false false
review impactRegentHoneyeater = evidence-review impactRegentHoneyeater
  "PD A.i Section 6.1" sourceReportedOnly
  "Are 9868 mapped preferred forage features independently accounted for?"
  false false
review speciesOccurrence = evidence-review speciesOccurrence
  "A15 Table 33; A16 Table 44; Esk A14" sourceReportedOnly
  "Site-level presence cannot by itself evidence use in each AU or a viable population."
  false false
review surveyDesign = evidence-review surveyDesign
  "A16 Sections 6.1.3 and 6.2.1" directSourceArithmeticConflict
  "Reconcile 5 SAT transect labels, selection, unsearched paddocks and detectability."
  false false
review surveySpatialJoin = evidence-review surveySpatialJoin
  "A16 App F; A15 App E" sourceReportedOnly
  "Match every GPS tree/SAT to actual AU/polygon; check propagated presence scope."
  false false
review habitatCondition = evidence-review habitatCondition
  "A16 Tables 41-42; A15 condition tables" sourceReportedOnly
  "Separate present food, shelter, hollow and forest maturity from generic vegetation scores."
  false false
review habitatConnectivity = evidence-review habitatConnectivity
  "A16 Table 43; PD landscape context" sourceReportedOnly
  "MWW 0/6 corridor score cannot establish replacement of Woogaroo connectivity."
  false false
review habitatPopulationFunction = evidence-review habitatPopulationFunction
  "A16 Table 45; A15 Table 34" sourceReportedOnly
  "A possible dispersal-source score does not measure local breeding or population persistence."
  false false
review offsetAreaAccounting = evidence-review offsetAreaAccounting
  "A16 Table 13; title / exclusion maps" exactSourceArithmeticChecked
  "All MWW koala percentage is credited by AU1 and AU2; verify exact boundaries."
  false false
review qualityScoring = evidence-review qualityScoring
  "A16 Table 45; Table 25 scoring rules" directSourceArithmeticConflict
  "AU4 has 30 points by components but published 40; determine actual model input."
  false false
review futureHabitatValue = evidence-review futureHabitatValue
  "A16 Tables 12-15; OAMP Appendix A" sourceReportedOnly
  "Distinguish year-20 forecast habitat score from demonstrated habitat function."
  false false
review futureTreeCounts = evidence-review futureTreeCounts
  "A16 Tables 47-51; A15 species OAG" sourceReportedOnly
  "Audit planting count, survival fraction, time to flowering and species use."
  false false
review counterfactualRisk = evidence-review counterfactualRisk
  "A16 Table 12; A15 OAG risk fields" sourceReportedOnly
  "Risk without/with offset both 0 percent; inspect evidence supporting risk baseline."
  false false
review confidenceAssumptions = evidence-review confidenceAssumptions
  "A16 Table 12" sourceReportedOnly
  "Independent calibration for 75 percent and 85 percent future quality confidence is required."
  false false
review ecologicalTimeLag = evidence-review ecologicalTimeLag
  "A16 Table 12, 20 years" sourceReportedOnly
  "Do 50 percent canopy and 70 percent canopy height recover species-specific mature function?"
  false false
review ecologicalAdditionality = evidence-review ecologicalAdditionality
  "A15 and A16 offset plans" sourceReportedOnly
  "Separate baseline conservation from additive works and pre-existing obligations."
  false false
review proposedMitigation = evidence-review proposedMitigation
  "PD Part A Section 5; approved Annexure A" sourceReportedOnly
  "Survey, fauna spotter, road and clearing controls are commitments not measured outcomes."
  false false
review retainedHabitat = evidence-review retainedHabitat
  "PD Part A retention plans" sourceReportedOnly
  "Test exact area and after-development functional connectivity, not only corridor width."
  false false
review cumulativeFragmentation = evidence-review cumulativeFragmentation
  "PD Item 4.6(c) response" sourceReportedOnly
  "Cumulative baseline is not necessarily a same-action marginal effect."
  false false
review legalSecurity = evidence-review legalSecurity
  "16 Oct 2026 Annexure A Conditions 24-27" sourceReportedOnly
  "Approved condition != a registered Queensland voluntary declaration."
  false false
review declarationsRegistration = evidence-review declarationsRegistration
  "Queensland section 19F instruments" sourceReportedOnly
  "Obtain date, actual legal title dealing, same registered polygons and parcel ID."
  false false
review commencementCompliance = evidence-review commencementCompliance
  "16 Oct 2026 Annexure A Conditions 48-69" sourceReportedOnly
  "Actual commencement, publications and field controls require original receipts."
  false false
review financialAgreement = evidence-review financialAgreement
  "PD Avonvale One Environment agreement statement" sourceReportedOnly
  "Contract mention != executed agreement, price, bank payment, or transfer."
  false false
review landTenure = evidence-review landTenure
  "PD Esk/MWW ownership statement; Titles QLD" sourceReportedOnly
  "Historical parcel name != current title, ownership or offset footprint."
  false false
review commentResponses = evidence-review commentResponses
  "Section 95B(2) notice" sourceReportedOnly
  "1786 comments announced != complete government-received comments and responses."
  false false
review decisionReasons = evidence-review decisionReasons
  "Signed approval 16 October 2026, s95C still open" sourceReportedOnly
  "Signed conditions != recorded advice-consideration or independently reviewed merits."
  false false

-- No admission to a higher authority level from a source or score alone.
data SourceAssertionIsIndependentEcologicalFinding : Set where
data NumericalScoreIsRealisedEcologicalOutcome : Set where
data OffsetConditionIsVerifiedPerformance : Set where

noSourcePromotion :
  SourceAssertionIsIndependentEcologicalFinding → ⊥
noSourcePromotion ()
noOutcomePromotion :
  NumericalScoreIsRealisedEcologicalOutcome → ⊥
noOutcomePromotion ()
noConditionPromotion :
  OffsetConditionIsVerifiedPerformance → ⊥
noConditionPromotion ()

-- The old SAT and legal adversarial engines remain canonical parent owners.
oldReportedSAT : SAT.SurveyReceipt
oldReportedSAT = SAT.mountWalkerReceipt
priorLegalHabitatCountermodel :
  Prior.ShortcutCountermodel
    DASHI.Law.SensibLawWoogarooEPBC8575PleadableGroundsPrecedentCut20261028Exact.actionBaselineError
priorLegalHabitatCountermodel = SAT.habitatGroundCountermodel
