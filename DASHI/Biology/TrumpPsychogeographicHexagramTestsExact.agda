module DASHI.Biology.TrumpPsychogeographicHexagramTestsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.DASHIYijingTernaryDivinationExact as Yijing
import DASHI.Biology.PsychogeographicHexagramObservationExact as Hex
import DASHI.Biology.TrumpPsychogeographicPolicyAtlasExact as Atlas

------------------------------------------------------------------------
-- Six-line policy observation.
--
-- The line scales are inherited from psychogeography:
--
--   1 body / footing
--   2 intimate locality / home / belonging
--   3 street threshold / movement
--   4 civic and legal interface
--   5 district and institutional organisation
--   6 historical and national horizon
--
-- Trits are typed here as directional observations:
--
--   negative : constraining, excluding, withdrawing or suppressing tendency
--   zero     : contested, unresolved, silenced, incommensurable or no typed meet
--   positive : mobilising, expanding, institutionalising or amplifying tendency
--
-- They are not moral scores.  In particular, positive does not mean good,
-- negative does not mean bad, and zero does not mean compromise.
------------------------------------------------------------------------

record SixLinePolicyProfile : Set where
  constructor sixLinePolicyProfile
  field
    bodyFootingLine : Triadic.KernelTrit
    intimateLocalityLine : Triadic.KernelTrit
    streetThresholdLine : Triadic.KernelTrit
    civicInterfaceLine : Triadic.KernelTrit
    districtOrganisationLine : Triadic.KernelTrit
    historicalHorizonLine : Triadic.KernelTrit

open SixLinePolicyProfile public

profileHexagram : SixLinePolicyProfile → Yijing.TernaryHexagram
profileHexagram p =
  bodyFootingLine p vcons
  intimateLocalityLine p vcons
  streetThresholdLine p vcons
  civicInterfaceLine p vcons
  districtOrganisationLine p vcons
  historicalHorizonLine p vcons
  vnil

n : Triadic.KernelTrit
n = Triadic.negativeTrit

z : Triadic.KernelTrit
z = Triadic.zeroTrit

p : Triadic.KernelTrit
p = Triadic.positiveTrit

canonicalPolicyProfile : Atlas.TrumpPolicyCase → SixLinePolicyProfile
canonicalPolicyProfile Atlas.immigrationRaidsMassDeportationCase =
  sixLinePolicyProfile n n n p p p
canonicalPolicyProfile Atlas.borderWallCase =
  sixLinePolicyProfile n z n p p p
canonicalPolicyProfile Atlas.januarySixCase =
  sixLinePolicyProfile p z p n z p
canonicalPolicyProfile Atlas.electionDenialCase =
  sixLinePolicyProfile z z p n p p
canonicalPolicyProfile Atlas.presidentialImmunityCase =
  sixLinePolicyProfile z z z p p p
canonicalPolicyProfile Atlas.unitaryExecutiveTheoryCase =
  sixLinePolicyProfile z z z p p p
canonicalPolicyProfile Atlas.christianNationalismInterfaceCase =
  sixLinePolicyProfile z p z p p p
canonicalPolicyProfile Atlas.tariffIndustrialPolicyCase =
  sixLinePolicyProfile z z z z p p
canonicalPolicyProfile Atlas.transPolicyCase =
  sixLinePolicyProfile n n z p p p
canonicalPolicyProfile Atlas.palestinePolicyCase =
  sixLinePolicyProfile n n n p p p
canonicalPolicyProfile Atlas.indigenousPolicyCase =
  sixLinePolicyProfile z n n p p p
canonicalPolicyProfile Atlas.administrativeStateRestructuringCase =
  sixLinePolicyProfile z z z p p p
canonicalPolicyProfile Atlas.palantirSurveillanceProcurementCase =
  sixLinePolicyProfile z n z p p z

caseHexagram : Atlas.TrumpPolicyCase → Yijing.TernaryHexagram
caseHexagram c = profileHexagram (canonicalPolicyProfile c)

------------------------------------------------------------------------
-- Coarse-observation tests.
------------------------------------------------------------------------

unitaryAndAdministrativeProfilesCoincide :
  caseHexagram Atlas.unitaryExecutiveTheoryCase
  ≡ caseHexagram Atlas.administrativeStateRestructuringCase
unitaryAndAdministrativeProfilesCoincide = refl

unitaryAndAdministrativeCasesRemainDistinct :
  ¬ (Atlas.unitaryExecutiveTheoryCase
     ≡ Atlas.administrativeStateRestructuringCase)
unitaryAndAdministrativeCasesRemainDistinct ()

immigrationAndPalestineProfilesCoincide :
  caseHexagram Atlas.immigrationRaidsMassDeportationCase
  ≡ caseHexagram Atlas.palestinePolicyCase
immigrationAndPalestineProfilesCoincide = refl

immigrationAndPalestineCasesRemainDistinct :
  ¬ (Atlas.immigrationRaidsMassDeportationCase
     ≡ Atlas.palestinePolicyCase)
immigrationAndPalestineCasesRemainDistinct ()

borderWallDiffersFromImmigrationAtOneLine :
  Hex.hexagramDifference
    (caseHexagram Atlas.borderWallCase)
    (caseHexagram Atlas.immigrationRaidsMassDeportationCase)
  ≡ 1
borderWallDiffersFromImmigrationAtOneLine = refl

transPolicyDiffersFromImmigrationAtOneLine :
  Hex.hexagramDifference
    (caseHexagram Atlas.transPolicyCase)
    (caseHexagram Atlas.immigrationRaidsMassDeportationCase)
  ≡ 1
transPolicyDiffersFromImmigrationAtOneLine = refl

------------------------------------------------------------------------
-- Observer-view test.
--
-- The inherited sign view can reverse an opposed observation without changing
-- the underlying trit.  Zero remains unresolved in both views.
------------------------------------------------------------------------

firstLine : Yijing.TernaryHexagram → Triadic.KernelTrit
firstLine (a vcons b vcons c vcons d vcons e vcons f vcons vnil) = a

borderWallFirstLineDirect :
  Yijing.observeYinYang Yijing.directView
    (firstLine (caseHexagram Atlas.borderWallCase))
  ≡ Yijing.yinObservation
borderWallFirstLineDirect = refl

borderWallFirstLineReversed :
  Yijing.observeYinYang Yijing.reversedView
    (firstLine (caseHexagram Atlas.borderWallCase))
  ≡ Yijing.yangObservation
borderWallFirstLineReversed = refl

tariffFirstLineUnresolvedInBothViews :
  Yijing.observeYinYang Yijing.directView
    (firstLine (caseHexagram Atlas.tariffIndustrialPolicyCase))
  ≡ Yijing.unresolvedObservation
  ×
  Yijing.observeYinYang Yijing.reversedView
    (firstLine (caseHexagram Atlas.tariffIndustrialPolicyCase))
  ≡ Yijing.unresolvedObservation
tariffFirstLineUnresolvedInBothViews = refl , refl

------------------------------------------------------------------------
-- Moving-line attention tests.
--
-- A moving mask changes the symbolic observation used to redirect attention.
-- It does not itself change policy, prove causation, predict an outcome or
-- authorise action.
------------------------------------------------------------------------

bodyAndCivicMask : Vec Bool 6
bodyAndCivicMask =
  true vcons
  false vcons
  false vcons
  true vcons
  false vcons
  false vcons
  vnil

civicAndHistoricalMask : Vec Bool 6
civicAndHistoricalMask =
  false vcons
  false vcons
  false vcons
  true vcons
  false vcons
  true vcons
  vnil

localityAndDistrictMask : Vec Bool 6
localityAndDistrictMask =
  false vcons
  true vcons
  false vcons
  false vcons
  true vcons
  false vcons
  vnil

record PolicyHexagramAttentionTest : Set where
  constructor policyHexagramAttentionTest
  field
    testCase : Atlas.TrumpPolicyCase
    initialHexagram : Yijing.TernaryHexagram
    movingMask : Vec Bool 6
    resultingHexagram : Yijing.TernaryHexagram
    attentionPrompt : String
    readingAuthority : Yijing.ReadingAuthority

open PolicyHexagramAttentionTest public

mkAttentionTest :
  Atlas.TrumpPolicyCase →
  Vec Bool 6 →
  String →
  PolicyHexagramAttentionTest
mkAttentionTest c mask prompt =
  policyHexagramAttentionTest
    c
    (caseHexagram c)
    mask
    (Yijing.applyMovingMask mask (caseHexagram c))
    prompt
    Yijing.associativeAuthority

immigrationRaidAttentionTest : PolicyHexagramAttentionTest
immigrationRaidAttentionTest =
  mkAttentionTest
    Atlas.immigrationRaidsMassDeportationCase
    bodyAndCivicMask
    "inspect how bodily exposure and the civic interface are coupled"

januarySixAttentionTest : PolicyHexagramAttentionTest
januarySixAttentionTest =
  mkAttentionTest
    Atlas.januarySixCase
    civicAndHistoricalMask
    "inspect how institutional breach, clemency and national memory reframe one another"

transPolicyAttentionTest : PolicyHexagramAttentionTest
transPolicyAttentionTest =
  mkAttentionTest
    Atlas.transPolicyCase
    bodyAndCivicMask
    "inspect translation from body classification into documents and institutional access"

palantirAttentionTest : PolicyHexagramAttentionTest
palantirAttentionTest =
  mkAttentionTest
    Atlas.palantirSurveillanceProcurementCase
    localityAndDistrictMask
    "inspect how intimate data becomes district-scale administrative capacity"

immigrationMovingTestChangesTwoLines :
  Hex.hexagramDifference
    (initialHexagram immigrationRaidAttentionTest)
    (resultingHexagram immigrationRaidAttentionTest)
  ≡ 2
immigrationMovingTestChangesTwoLines = refl

januarySixMovingTestChangesTwoLines :
  Hex.hexagramDifference
    (initialHexagram januarySixAttentionTest)
    (resultingHexagram januarySixAttentionTest)
  ≡ 2
januarySixMovingTestChangesTwoLines = refl

palantirMovingTestChangesTwoLines :
  Hex.hexagramDifference
    (initialHexagram palantirAttentionTest)
    (resultingHexagram palantirAttentionTest)
  ≡ 2
palantirMovingTestChangesTwoLines = refl

allAttentionTestsAssociative :
  readingAuthority immigrationRaidAttentionTest ≡ Yijing.associativeAuthority
  × readingAuthority januarySixAttentionTest ≡ Yijing.associativeAuthority
  × readingAuthority transPolicyAttentionTest ≡ Yijing.associativeAuthority
  × readingAuthority palantirAttentionTest ≡ Yijing.associativeAuthority
allAttentionTestsAssociative = refl , refl , refl , refl

record TrumpPsychogeographicHexagramBoundary : Set where
  constructor trumpPsychogeographicHexagramBoundary
  field
    tritPolarityIsMoralScore : Bool
    tritPolarityIsMoralScoreIsFalse :
      tritPolarityIsMoralScore ≡ false
    zeroMeansCentristCompromise : Bool
    zeroMeansCentristCompromiseIsFalse :
      zeroMeansCentristCompromise ≡ false
    sameHexagramMakesPolicyCasesEquivalent : Bool
    sameHexagramMakesPolicyCasesEquivalentIsFalse :
      sameHexagramMakesPolicyCasesEquivalent ≡ false
    movingMaskChangesExternalPolicy : Bool
    movingMaskChangesExternalPolicyIsFalse :
      movingMaskChangesExternalPolicy ≡ false
    associativeReadingPredictsPoliticalOutcome : Bool
    associativeReadingPredictsPoliticalOutcomeIsFalse :
      associativeReadingPredictsPoliticalOutcome ≡ false
    analystProfileIsEmpiricalMeasurement : Bool
    analystProfileIsEmpiricalMeasurementIsFalse :
      analystProfileIsEmpiricalMeasurement ≡ false

canonicalTrumpPsychogeographicHexagramBoundary :
  TrumpPsychogeographicHexagramBoundary
canonicalTrumpPsychogeographicHexagramBoundary =
  trumpPsychogeographicHexagramBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
