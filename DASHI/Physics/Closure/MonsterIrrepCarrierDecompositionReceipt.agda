module DASHI.Physics.Closure.MonsterIrrepCarrierDecompositionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.GravityVladimirovFrameReceipt as Gravity
import DASHI.Physics.Closure.HeckeCarrierVsCMSplittingReceipt as HeckeCM
import DASHI.Physics.Closure.MonsterMoonshineSSPQuotientControlReceipt
  as MonsterQuotient
import DASHI.Physics.Closure.SSP15CMFieldSplittingCorrectionReceipt as CM15
import DASHI.Physics.Closure.SSPSevenSevenOneFrameDecompositionReceipt
  as SSPFrame
import DASHI.Physics.Closure.YMMonsterQuotientEvidenceReceipt as YMT7

------------------------------------------------------------------------
-- Monster irrep / 15SSP carrier decomposition receipt.
--
-- This receipt records how the 194 Monster irreducible characters are used by
-- the 15-prime SSP carrier and the T_7 compression lane.  It also keeps two
-- arithmetic/moonshine guards explicit:
--
--   * the 15 SSP primes are the Ogg/supersingular prime support of the
--     carrier, not the only genus-zero McKay-Thompson classes;
--   * the semantic 7+7+1 atom split is not the literal Q(sqrt(-7))
--     split/inert partition, and p71 is split in Q(sqrt(-7)).
--
-- The receipt therefore records T_7 compression as evidence for a finite YM
-- entropy target and phase-completeness as evidence for Gate 3, without
-- claiming the Balaban bridge, the frame lower bound, or Clay promotion.

data MonsterIrrepCarrierDecompositionStatus : Set where
  monsterIrrepDecompositionRecorded_BalabanT7CompressionExplained_clayNotClaimed :
    MonsterIrrepCarrierDecompositionStatus

data MonsterIrrepDatum : Set where
  monsterIrrepCount194 :
    MonsterIrrepDatum

  monsterConjugacyClassCount194 :
    MonsterIrrepDatum

  sspPrimeCarrierCount15 :
    MonsterIrrepDatum

  nonCarrierClassRemainder179 :
    MonsterIrrepDatum

  sspCarrierIsPrimeLaneQuotient :
    MonsterIrrepDatum

canonicalMonsterIrrepData : List MonsterIrrepDatum
canonicalMonsterIrrepData =
  monsterIrrepCount194
  ∷ monsterConjugacyClassCount194
  ∷ sspPrimeCarrierCount15
  ∷ nonCarrierClassRemainder179
  ∷ sspCarrierIsPrimeLaneQuotient
  ∷ []

data MoonshineGuard : Set where
  ssp15AreOggSupersingularPrimeSupport :
    MoonshineGuard

  ssp15AreNotOnlyGenusZeroMcKayThompsonClasses :
    MoonshineGuard

  all194MonsterClassesHaveMcKayThompsonHauptmodulLane :
    MoonshineGuard

  nonCarrier179AreQuotientTailNotGenusPositiveClaim :
    MoonshineGuard

canonicalMoonshineGuards : List MoonshineGuard
canonicalMoonshineGuards =
  ssp15AreOggSupersingularPrimeSupport
  ∷ ssp15AreNotOnlyGenusZeroMcKayThompsonClasses
  ∷ all194MonsterClassesHaveMcKayThompsonHauptmodulLane
  ∷ nonCarrier179AreQuotientTailNotGenusPositiveClaim
  ∷ []

data T7CompressionDatum : Set where
  t7AOrderSeven :
    T7CompressionDatum

  t7Q2Coefficient204 :
    T7CompressionDatum

  t7Coefficient204SplitsAsOnePlus203 :
    T7CompressionDatum

  trivialCharacterContributionOne :
    T7CompressionDatum

  smallestNontrivialCharacterContribution203 :
    T7CompressionDatum

  t7GrowthRademacherExpFourPiSqrtDOverSqrtSeven :
    T7CompressionDatum

  jGrowthRademacherExpFourPiSqrtD :
    T7CompressionDatum

  t7CompressionControlsEffectiveC0 :
    T7CompressionDatum

canonicalT7CompressionData : List T7CompressionDatum
canonicalT7CompressionData =
  t7AOrderSeven
  ∷ t7Q2Coefficient204
  ∷ t7Coefficient204SplitsAsOnePlus203
  ∷ trivialCharacterContributionOne
  ∷ smallestNontrivialCharacterContribution203
  ∷ t7GrowthRademacherExpFourPiSqrtDOverSqrtSeven
  ∷ jGrowthRademacherExpFourPiSqrtD
  ∷ t7CompressionControlsEffectiveC0
  ∷ []

data CarrierRestrictionDatum : Set where
  restrictIrrepsToCyclicSubgroupGeneratedBy7A :
    CarrierRestrictionDatum

  cyclicSevenCharactersPsi0ThroughPsi6 :
    CarrierRestrictionDatum

  mirrorA7AmplitudeLaneRecorded :
    CarrierRestrictionDatum

  mirrorB7PhaseLaneRecorded :
    CarrierRestrictionDatum

  p71SplitsCompletelyInCyclotomicSevenBecauseOneModSeven :
    CarrierRestrictionDatum

  p71GenerationResolutionRoleRecorded :
    CarrierRestrictionDatum

canonicalCarrierRestrictionData : List CarrierRestrictionDatum
canonicalCarrierRestrictionData =
  restrictIrrepsToCyclicSubgroupGeneratedBy7A
  ∷ cyclicSevenCharactersPsi0ThroughPsi6
  ∷ mirrorA7AmplitudeLaneRecorded
  ∷ mirrorB7PhaseLaneRecorded
  ∷ p71SplitsCompletelyInCyclotomicSevenBecauseOneModSeven
  ∷ p71GenerationResolutionRoleRecorded
  ∷ []

data FractalNestingDatum : Set where
  monsterGradedPieceCarriesMonsterRepresentation :
    FractalNestingDatum

  eachDepthCarriesFifteenPrimeLaneActions :
    FractalNestingDatum

  nested15SSPDepthStructureRecorded :
    FractalNestingDatum

  threeDArchimedeanDensityPTo3D :
    FractalNestingDatum

canonicalFractalNestingData : List FractalNestingDatum
canonicalFractalNestingData =
  monsterGradedPieceCarriesMonsterRepresentation
  ∷ eachDepthCarriesFifteenPrimeLaneActions
  ∷ nested15SSPDepthStructureRecorded
  ∷ threeDArchimedeanDensityPTo3D
  ∷ []

data LemmaRelevance : Set where
  ymBalabanT7GrowthControlsKPEntropy :
    LemmaRelevance

  gate3PhaseCompletionRequiredForComplexCharacterResolution :
    LemmaRelevance

  nsNoDirectMonsterIrrepClosure :
    LemmaRelevance

canonicalLemmaRelevance : List LemmaRelevance
canonicalLemmaRelevance =
  ymBalabanT7GrowthControlsKPEntropy
  ∷ gate3PhaseCompletionRequiredForComplexCharacterResolution
  ∷ nsNoDirectMonsterIrrepClosure
  ∷ []

data ArithmeticCorrection : Set where
  sevenSevenOneIsSemanticNotLiteralCMSplitting :
    ArithmeticCorrection

  firstSevenAllSplitClaimRejected :
    ArithmeticCorrection

  secondSevenAllInertClaimRejected :
    ArithmeticCorrection

  p71QsqrtMinusSevenInertClaimRejected :
    ArithmeticCorrection

  p71CyclotomicSevenSplitRoleAccepted :
    ArithmeticCorrection

canonicalArithmeticCorrections : List ArithmeticCorrection
canonicalArithmeticCorrections =
  sevenSevenOneIsSemanticNotLiteralCMSplitting
  ∷ firstSevenAllSplitClaimRejected
  ∷ secondSevenAllInertClaimRejected
  ∷ p71QsqrtMinusSevenInertClaimRejected
  ∷ p71CyclotomicSevenSplitRoleAccepted
  ∷ []

data MonsterIrrepPromotion : Set where

monsterIrrepPromotionImpossibleHere :
  MonsterIrrepPromotion →
  ⊥
monsterIrrepPromotionImpossibleHere ()

monsterIrrepCount :
  Nat
monsterIrrepCount =
  194

monsterConjugacyClassCount :
  Nat
monsterConjugacyClassCount =
  194

sspPrimeCarrierCount :
  Nat
sspPrimeCarrierCount =
  15

nonCarrierClassRemainder :
  Nat
nonCarrierClassRemainder =
  179

t7Order :
  Nat
t7Order =
  7

t7Q2Coeff :
  Nat
t7Q2Coeff =
  204

trivialContribution :
  Nat
trivialContribution =
  1

smallestNontrivialContribution :
  Nat
smallestNontrivialContribution =
  203

smallestNontrivialIrrepDimension :
  Nat
smallestNontrivialIrrepDimension =
  196883

vNaturalJQ1Coefficient :
  Nat
vNaturalJQ1Coefficient =
  196884

p71Mod7 :
  Nat
p71Mod7 =
  1

t7CompressionStatement :
  String
t7CompressionStatement =
  "T_7 compression records 204 = 1 + 203 at the q^2 coefficient used by the YM evidence receipt, and growth c_7(d) ~ exp(4*pi*sqrt(d)/sqrt(7)) versus j-growth exp(4*pi*sqrt(d))."

moonshineGuardStatement :
  String
moonshineGuardStatement =
  "The 194 Monster classes index McKay-Thompson/Hauptmodul lanes; the 15 SSP primes are the separate Ogg/supersingular prime carrier support, so the 179 remainder is quotient bookkeeping, not a genus-positive partition."

gate3RelevanceStatement :
  String
gate3RelevanceStatement =
  "Gate 3 relevance: MirrorB7 phase data is required to resolve complex 7A character information; phase-blind dictionaries keep the inert/phase factor failing."

ymRelevanceStatement :
  String
ymRelevanceStatement =
  "YM relevance: T_7 growth is the intended quotient entropy for the KP sum, but the Balaban beta bridge and OS/Wightman package remain open."

nsBoundaryStatement :
  String
nsBoundaryStatement =
  "NS boundary: Monster irreps do not directly prove the PDE estimates; the H^{-1/2} obstruction and H^{11/8} route remain analytic."

record MonsterIrrepCarrierDecompositionReceipt : Setω where
  field
    status :
      MonsterIrrepCarrierDecompositionStatus

    statusIsCanonical :
      status
      ≡
      monsterIrrepDecompositionRecorded_BalabanT7CompressionExplained_clayNotClaimed

    monsterQuotientReceipt :
      MonsterQuotient.MonsterMoonshineSSPQuotientControlReceipt

    monsterQuotientStillOpen :
      MonsterQuotient.quotientEntropyBoundProvedHere
        monsterQuotientReceipt
      ≡
      false

    ymT7EvidenceReceipt :
      YMT7.YMMonsterQuotientEvidenceReceipt

    ymT7NoClay :
      YMT7.clayYMPromoted ymT7EvidenceReceipt ≡ false

    heckeVsCMReceipt :
      HeckeCM.HeckeCarrierVsCMSplittingReceipt

    heckeVsCMCorrectionActive :
      HeckeCM.notSamePartitionFlag heckeVsCMReceipt ≡ true

    cmSplittingReceipt :
      CM15.SSP15CMFieldSplittingCorrectionReceipt

    p71QsqrtMinusSevenSplit :
      CM15.p71SplittingClass cmSplittingReceipt ≡ CM15.split

    frameDecompositionReceipt :
      SSPFrame.SSPSevenSevenOneFrameDecompositionReceipt

    gate3UniformLowerBoundStillOpen :
      SSPFrame.uniformLowerBoundProved frameDecompositionReceipt ≡ false

    gravityReceipt :
      Gravity.GravityVladimirovFrameReceipt

    gravityNoPromotion :
      Gravity.gravityPredictionPromoted gravityReceipt ≡ false

    irrepData :
      List MonsterIrrepDatum

    irrepDataAreCanonical :
      irrepData ≡ canonicalMonsterIrrepData

    moonshineGuards :
      List MoonshineGuard

    moonshineGuardsAreCanonical :
      moonshineGuards ≡ canonicalMoonshineGuards

    t7CompressionData :
      List T7CompressionDatum

    t7CompressionDataAreCanonical :
      t7CompressionData ≡ canonicalT7CompressionData

    carrierRestrictionData :
      List CarrierRestrictionDatum

    carrierRestrictionDataAreCanonical :
      carrierRestrictionData ≡ canonicalCarrierRestrictionData

    fractalNestingData :
      List FractalNestingDatum

    fractalNestingDataAreCanonical :
      fractalNestingData ≡ canonicalFractalNestingData

    lemmaRelevance :
      List LemmaRelevance

    lemmaRelevanceIsCanonical :
      lemmaRelevance ≡ canonicalLemmaRelevance

    arithmeticCorrections :
      List ArithmeticCorrection

    arithmeticCorrectionsAreCanonical :
      arithmeticCorrections ≡ canonicalArithmeticCorrections

    irrepCount :
      Nat

    irrepCountIs194 :
      irrepCount ≡ monsterIrrepCount

    conjugacyClassCount :
      Nat

    conjugacyClassCountIs194 :
      conjugacyClassCount ≡ monsterConjugacyClassCount

    carrierPrimeCount :
      Nat

    carrierPrimeCountIs15 :
      carrierPrimeCount ≡ sspPrimeCarrierCount

    tailClassCount :
      Nat

    tailClassCountIs179 :
      tailClassCount ≡ nonCarrierClassRemainder

    t7ElementOrder :
      Nat

    t7ElementOrderIsSeven :
      t7ElementOrder ≡ t7Order

    t7Coefficient204 :
      Nat

    t7Coefficient204IsCanonical :
      t7Coefficient204 ≡ t7Q2Coeff

    t7Coefficient204Decomposition :
      Nat

    t7Coefficient204DecompositionIs204 :
      t7Coefficient204Decomposition
      ≡
      trivialContribution + smallestNontrivialContribution

    smallestIrrepDimension :
      Nat

    smallestIrrepDimensionIs196883 :
      smallestIrrepDimension ≡ smallestNontrivialIrrepDimension

    p71ModuloSeven :
      Nat

    p71ModuloSevenIsOne :
      p71ModuloSeven ≡ p71Mod7

    t7CompressionBoundary :
      String

    t7CompressionBoundaryIsCanonical :
      t7CompressionBoundary ≡ t7CompressionStatement

    moonshineGuardBoundary :
      String

    moonshineGuardBoundaryIsCanonical :
      moonshineGuardBoundary ≡ moonshineGuardStatement

    gate3RelevanceBoundary :
      String

    gate3RelevanceBoundaryIsCanonical :
      gate3RelevanceBoundary ≡ gate3RelevanceStatement

    ymRelevanceBoundary :
      String

    ymRelevanceBoundaryIsCanonical :
      ymRelevanceBoundary ≡ ymRelevanceStatement

    nsBoundary :
      String

    nsBoundaryIsCanonical :
      nsBoundary ≡ nsBoundaryStatement

    fifteenSSPAsCarrierQuotientRecorded :
      Bool

    fifteenSSPAsCarrierQuotientRecordedIsTrue :
      fifteenSSPAsCarrierQuotientRecorded ≡ true

    claim179HaveGenusPositiveMcKayThompsonSeries :
      Bool

    claim179HaveGenusPositiveMcKayThompsonSeriesIsFalse :
      claim179HaveGenusPositiveMcKayThompsonSeries ≡ false

    all194McKayThompsonHauptmodulLanesRecorded :
      Bool

    all194McKayThompsonHauptmodulLanesRecordedIsTrue :
      all194McKayThompsonHauptmodulLanesRecorded ≡ true

    firstSevenLiteralSplitClaim :
      Bool

    firstSevenLiteralSplitClaimIsFalse :
      firstSevenLiteralSplitClaim ≡ false

    secondSevenLiteralInertClaim :
      Bool

    secondSevenLiteralInertClaimIsFalse :
      secondSevenLiteralInertClaim ≡ false

    p71QsqrtMinusSevenInertClaim :
      Bool

    p71QsqrtMinusSevenInertClaimIsFalse :
      p71QsqrtMinusSevenInertClaim ≡ false

    p71CyclotomicSevenSplitRole :
      Bool

    p71CyclotomicSevenSplitRoleIsTrue :
      p71CyclotomicSevenSplitRole ≡ true

    ymBalabanBridgeProvedHere :
      Bool

    ymBalabanBridgeProvedHereIsFalse :
      ymBalabanBridgeProvedHere ≡ false

    gate3FrameBoundProvedHere :
      Bool

    gate3FrameBoundProvedHereIsFalse :
      gate3FrameBoundProvedHere ≡ false

    nsClayHelpClaimed :
      Bool

    nsClayHelpClaimedIsFalse :
      nsClayHelpClaimed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    gate3Promoted :
      Bool

    gate3PromotedIsFalse :
      gate3Promoted ≡ false

    terminalPromoted :
      Bool

    terminalPromotedIsFalse :
      terminalPromoted ≡ false

    promotions :
      List MonsterIrrepPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      MonsterIrrepPromotion →
      ⊥

open MonsterIrrepCarrierDecompositionReceipt public

canonicalMonsterIrrepCarrierDecompositionReceipt :
  MonsterIrrepCarrierDecompositionReceipt
canonicalMonsterIrrepCarrierDecompositionReceipt =
  record
    { status =
        monsterIrrepDecompositionRecorded_BalabanT7CompressionExplained_clayNotClaimed
    ; statusIsCanonical =
        refl
    ; monsterQuotientReceipt =
        MonsterQuotient.canonicalMonsterMoonshineSSPQuotientControlReceipt
    ; monsterQuotientStillOpen =
        refl
    ; ymT7EvidenceReceipt =
        YMT7.canonicalYMMonsterQuotientEvidenceReceipt
    ; ymT7NoClay =
        refl
    ; heckeVsCMReceipt =
        HeckeCM.canonicalHeckeCarrierVsCMSplittingReceipt
    ; heckeVsCMCorrectionActive =
        refl
    ; cmSplittingReceipt =
        CM15.canonicalSSP15CMFieldSplittingCorrectionReceipt
    ; p71QsqrtMinusSevenSplit =
        refl
    ; frameDecompositionReceipt =
        SSPFrame.canonicalSSPSevenSevenOneFrameDecompositionReceipt
    ; gate3UniformLowerBoundStillOpen =
        refl
    ; gravityReceipt =
        Gravity.canonicalGravityVladimirovFrameReceipt
    ; gravityNoPromotion =
        refl
    ; irrepData =
        canonicalMonsterIrrepData
    ; irrepDataAreCanonical =
        refl
    ; moonshineGuards =
        canonicalMoonshineGuards
    ; moonshineGuardsAreCanonical =
        refl
    ; t7CompressionData =
        canonicalT7CompressionData
    ; t7CompressionDataAreCanonical =
        refl
    ; carrierRestrictionData =
        canonicalCarrierRestrictionData
    ; carrierRestrictionDataAreCanonical =
        refl
    ; fractalNestingData =
        canonicalFractalNestingData
    ; fractalNestingDataAreCanonical =
        refl
    ; lemmaRelevance =
        canonicalLemmaRelevance
    ; lemmaRelevanceIsCanonical =
        refl
    ; arithmeticCorrections =
        canonicalArithmeticCorrections
    ; arithmeticCorrectionsAreCanonical =
        refl
    ; irrepCount =
        monsterIrrepCount
    ; irrepCountIs194 =
        refl
    ; conjugacyClassCount =
        monsterConjugacyClassCount
    ; conjugacyClassCountIs194 =
        refl
    ; carrierPrimeCount =
        sspPrimeCarrierCount
    ; carrierPrimeCountIs15 =
        refl
    ; tailClassCount =
        nonCarrierClassRemainder
    ; tailClassCountIs179 =
        refl
    ; t7ElementOrder =
        t7Order
    ; t7ElementOrderIsSeven =
        refl
    ; t7Coefficient204 =
        t7Q2Coeff
    ; t7Coefficient204IsCanonical =
        refl
    ; t7Coefficient204Decomposition =
        trivialContribution + smallestNontrivialContribution
    ; t7Coefficient204DecompositionIs204 =
        refl
    ; smallestIrrepDimension =
        smallestNontrivialIrrepDimension
    ; smallestIrrepDimensionIs196883 =
        refl
    ; p71ModuloSeven =
        p71Mod7
    ; p71ModuloSevenIsOne =
        refl
    ; t7CompressionBoundary =
        t7CompressionStatement
    ; t7CompressionBoundaryIsCanonical =
        refl
    ; moonshineGuardBoundary =
        moonshineGuardStatement
    ; moonshineGuardBoundaryIsCanonical =
        refl
    ; gate3RelevanceBoundary =
        gate3RelevanceStatement
    ; gate3RelevanceBoundaryIsCanonical =
        refl
    ; ymRelevanceBoundary =
        ymRelevanceStatement
    ; ymRelevanceBoundaryIsCanonical =
        refl
    ; nsBoundary =
        nsBoundaryStatement
    ; nsBoundaryIsCanonical =
        refl
    ; fifteenSSPAsCarrierQuotientRecorded =
        true
    ; fifteenSSPAsCarrierQuotientRecordedIsTrue =
        refl
    ; claim179HaveGenusPositiveMcKayThompsonSeries =
        false
    ; claim179HaveGenusPositiveMcKayThompsonSeriesIsFalse =
        refl
    ; all194McKayThompsonHauptmodulLanesRecorded =
        true
    ; all194McKayThompsonHauptmodulLanesRecordedIsTrue =
        refl
    ; firstSevenLiteralSplitClaim =
        false
    ; firstSevenLiteralSplitClaimIsFalse =
        refl
    ; secondSevenLiteralInertClaim =
        false
    ; secondSevenLiteralInertClaimIsFalse =
        refl
    ; p71QsqrtMinusSevenInertClaim =
        false
    ; p71QsqrtMinusSevenInertClaimIsFalse =
        refl
    ; p71CyclotomicSevenSplitRole =
        true
    ; p71CyclotomicSevenSplitRoleIsTrue =
        refl
    ; ymBalabanBridgeProvedHere =
        false
    ; ymBalabanBridgeProvedHereIsFalse =
        refl
    ; gate3FrameBoundProvedHere =
        false
    ; gate3FrameBoundProvedHereIsFalse =
        refl
    ; nsClayHelpClaimed =
        false
    ; nsClayHelpClaimedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; gate3Promoted =
        false
    ; gate3PromotedIsFalse =
        refl
    ; terminalPromoted =
        false
    ; terminalPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        monsterIrrepPromotionImpossibleHere
    }

monsterIrrepReceiptKeepsYMClayFalse :
  clayYangMillsPromoted canonicalMonsterIrrepCarrierDecompositionReceipt
  ≡
  false
monsterIrrepReceiptKeepsYMClayFalse =
  refl

monsterIrrepReceiptKeepsNSClayFalse :
  clayNavierStokesPromoted canonicalMonsterIrrepCarrierDecompositionReceipt
  ≡
  false
monsterIrrepReceiptKeepsNSClayFalse =
  refl

monsterIrrepReceiptRejectsGenusPositive179Claim :
  claim179HaveGenusPositiveMcKayThompsonSeries
    canonicalMonsterIrrepCarrierDecompositionReceipt
  ≡
  false
monsterIrrepReceiptRejectsGenusPositive179Claim =
  refl

monsterIrrepReceiptRecordsAll194HauptmodulLanes :
  all194McKayThompsonHauptmodulLanesRecorded
    canonicalMonsterIrrepCarrierDecompositionReceipt
  ≡
  true
monsterIrrepReceiptRecordsAll194HauptmodulLanes =
  refl

monsterIrrepReceiptRejectsP71QsqrtMinusSevenInert :
  p71QsqrtMinusSevenInertClaim
    canonicalMonsterIrrepCarrierDecompositionReceipt
  ≡
  false
monsterIrrepReceiptRejectsP71QsqrtMinusSevenInert =
  refl

monsterIrrepReceiptRecordsT7Split204 :
  t7Coefficient204Decomposition
    canonicalMonsterIrrepCarrierDecompositionReceipt
  ≡
  204
monsterIrrepReceiptRecordsT7Split204 =
  refl
