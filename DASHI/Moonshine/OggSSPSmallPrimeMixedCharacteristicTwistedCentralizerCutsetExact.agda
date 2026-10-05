module DASHI.Moonshine.OggSSPSmallPrimeMixedCharacteristicTwistedCentralizerCutsetExact where

------------------------------------------------------------------------
-- pB MIXED-CHARACTERISTIC TWISTED-CENTRALIZER CUTSET
--
-- SOURCE-BACKED CORNERS
--
-- (1) Carnahan generalized moonshine:
--     for every Monster element g, including 2B and 3B, the relevant twisted
--     data carry projective C_M(g)-actions and generalized-moonshine modular
--     traces.
--
-- (2) Dong--Li--Mason:
--     explicit 2B-twisted V^natural existence/uniqueness, projective
--     C_M(2B)-action, and Hauptmodul twisted traces.
--
-- (3) Franc--Mason:
--     the p-adic Moonshine VOA exists for every prime p; Monster action and
--     character map to Serre p-adic modular forms survive p-adic completion.
--
-- (4) Chen--Marks--Tyler:
--     the individual 2B and 3B Hauptmoduln exhibit small-prime p-adic
--     annihilation behavior; Appendix A records the numerical patterns
--       2B@2 : 11 -> 3,
--       3B@3 :  5 -> 2.
--
-- (5) Deligne--Rapoport / Igusa / modern wild-stack geometry:
--     the p=N bad-level supersingular local objects are available.
--
-- MISSING COMPATIBILITY
--
-- None of these sources proves that p-adically completing/localizing the SAME
-- pB-twisted generalized-moonshine object produces the bad-level Igusa local
-- term whose valuation is the independent Monster-local defect:
--
--     p=2 : 10,
--     p=3 :  2.
--
-- This file makes that one commuting-square theorem the terminal obligation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPSmallPrimeGeneralizedMoonshineCentralizerBridgeExact as GM
import DASHI.Moonshine.OggSSPSmallPrimePadicMoonshineScopeCutsetExact as PadicScope
import DASHI.Moonshine.OggSSP2B3BPadicHauptmodulBridgeExact as PBPadic
import DASHI.Moonshine.OggSSP2B3BPadicAnnihilationSlopeComparisonExact as Slope
import DASHI.Moonshine.OggSSPSmallPrimeArichetaIgusaBadLevelExtensionExact as Igusa
import DASHI.Moonshine.OggSSPSmallPrimeMonsterLocalCentralizerValuationExact as Local
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Typed prime/class lane.
------------------------------------------------------------------------

data PBTwistedLane : Set where
  lane2B lane3B : PBTwistedLane

lanePrime : PBTwistedLane -> Nat
lanePrime lane2B = 2
lanePrime lane3B = 3

laneDefect : PBTwistedLane -> Nat
laneDefect lane2B = Local.p2LocalCentralizerResidual
laneDefect lane3B = Local.p3LocalCentralizerResidual

laneObservedPadicIncrement : PBTwistedLane -> Nat
laneObservedPadicIncrement lane2B =
  Slope.eventualIncrement Slope.class2BAt2
laneObservedPadicIncrement lane3B =
  Slope.eventualIncrement Slope.class3BAt3

p2DefectIsTen :
  laneDefect lane2B ≡ 10
p2DefectIsTen = refl

p3DefectIsTwo :
  laneDefect lane3B ≡ 2
p3DefectIsTwo = refl

p2ObservedIncrementIsThree :
  laneObservedPadicIncrement lane2B ≡ 3
p2ObservedIncrementIsThree = refl

p3ObservedIncrementIsTwo :
  laneObservedPadicIncrement lane3B ≡ 2
p3ObservedIncrementIsTwo = refl

------------------------------------------------------------------------
-- 2. Source-backed corner receipts.
------------------------------------------------------------------------

generalizedMoonshineBoundary :
  GM.GeneralizedMoonshineCentralizerBridgeBoundary
generalizedMoonshineBoundary =
  GM.canonicalGeneralizedMoonshineCentralizerBridgeBoundary

padicMoonshineBoundary :
  PadicScope.SmallPrimePadicMoonshineScopeBoundary
padicMoonshineBoundary =
  PadicScope.canonicalSmallPrimePadicMoonshineScopeBoundary

classSpecificPadicBoundary :
  PBPadic.ClassSpecificPadicHauptmodulBridgeBoundary
classSpecificPadicBoundary =
  PBPadic.canonicalClassSpecificPadicHauptmodulBridgeBoundary

padicSlopeBoundary :
  Slope.PadicAnnihilationSlopeComparisonBoundary
padicSlopeBoundary =
  Slope.canonicalPadicAnnihilationSlopeComparisonBoundary

igusaBadLevelBoundary :
  Igusa.ArichetaIgusaBadLevelExtensionBoundary
igusaBadLevelBoundary =
  Igusa.canonicalArichetaIgusaBadLevelExtensionBoundary

------------------------------------------------------------------------
-- 3. The exact missing mixed-characteristic theorem.
------------------------------------------------------------------------

record PBTwistedPadicBadLevelLocalizationAuthority : Set₁ where
  field
    MixedCharacteristicObject : Set

    p2Object :
      MixedCharacteristicObject

    p3Object :
      MixedCharacteristicObject

    refinesGeneralizedMoonshinePBTwistedObject :
      Bool
    refinesGeneralizedMoonshinePBTwistedObjectIsTrue :
      refinesGeneralizedMoonshinePBTwistedObject ≡ true

    comesFromMonsterStableIntegralOrPadicCompletion :
      Bool
    comesFromMonsterStableIntegralOrPadicCompletionIsTrue :
      comesFromMonsterStableIntegralOrPadicCompletion ≡ true

    retainsPBLocalCentralizerAction :
      Bool
    retainsPBLocalCentralizerActionIsTrue :
      retainsPBLocalCentralizerAction ≡ true

    classSpecificTraceAgreesWithTwoBThreeBHauptmodul :
      Bool
    classSpecificTraceAgreesWithTwoBThreeBHauptmodulIsTrue :
      classSpecificTraceAgreesWithTwoBThreeBHauptmodul ≡ true

    localizesToBadLevelIgusaGeometry :
      Bool
    localizesToBadLevelIgusaGeometryIsTrue :
      localizesToBadLevelIgusaGeometry ≡ true

    compatibleWithFrickeAtkinLehnerAndPrimeSquareTower :
      Bool
    compatibleWithFrickeAtkinLehnerAndPrimeSquareTowerIsTrue :
      compatibleWithFrickeAtkinLehnerAndPrimeSquareTower ≡ true

    sourceNativeValuation :
      PBTwistedLane ->
      MixedCharacteristicObject ->
      Nat

    p2SourceNativeValuationIsTen :
      sourceNativeValuation lane2B p2Object ≡ 10

    p3SourceNativeValuationIsTwo :
      sourceNativeValuation lane3B p3Object ≡ 2

    p2ValuationRecognisesLocalCentralizerDefect :
      sourceNativeValuation lane2B p2Object
      ≡ laneDefect lane2B

    p3ValuationRecognisesLocalCentralizerDefect :
      sourceNativeValuation lane3B p3Object
      ≡ laneDefect lane3B

    valuationDefinedWithoutReadingTargetTenTwo :
      Bool
    valuationDefinedWithoutReadingTargetTenTwoIsTrue :
      valuationDefinedWithoutReadingTargetTenTwo ≡ true

open PBTwistedPadicBadLevelLocalizationAuthority public

data PBTwistedPadicBadLevelLocalizationAuthorityInhabited : Set where

pbTwistedPadicBadLevelLocalizationStillOpen :
  PBTwistedPadicBadLevelLocalizationAuthorityInhabited -> ⊥
pbTwistedPadicBadLevelLocalizationStillOpen ()

------------------------------------------------------------------------
-- 4. The p=3 CMT slope is a clue to the valuation, not an inhabitant.
------------------------------------------------------------------------

data NumericalP3SlopeMatchInhabitsLocalizationAuthority : Set where
data ComplexGeneralizedMoonshineAutomaticallyExtendsPadically : Set where
data AmbientPadicVOAAutomaticallyConstructsPBTwistedPadicSector : Set where
data IndividualHauptmodulPadicBehaviorCreatesTwistedCentralizerLocalization : Set where

p3SlopeMatchDoesNotInhabitLocalizationAuthority :
  NumericalP3SlopeMatchInhabitsLocalizationAuthority -> ⊥
p3SlopeMatchDoesNotInhabitLocalizationAuthority ()

complexGeneralizedMoonshineDoesNotAutomaticallyExtendPadically :
  ComplexGeneralizedMoonshineAutomaticallyExtendsPadically -> ⊥
complexGeneralizedMoonshineDoesNotAutomaticallyExtendPadically ()

ambientPadicVOADoesNotAutomaticallyConstructPBTwistedPadicSector :
  AmbientPadicVOAAutomaticallyConstructsPBTwistedPadicSector -> ⊥
ambientPadicVOADoesNotAutomaticallyConstructPBTwistedPadicSector ()

individualPadicHauptmodulDoesNotCreateLocalizationSquare :
  IndividualHauptmodulPadicBehaviorCreatesTwistedCentralizerLocalization -> ⊥
individualPadicHauptmodulDoesNotCreateLocalizationSquare ()

------------------------------------------------------------------------
-- 5. Attribution boundary.
------------------------------------------------------------------------

data CarnahanCreditedWithPadicBadLevelValuation : Set where
data FrancMasonCreditedWithPBTwistedLocalization : Set where
data CMTAppendixCreditedWithProofOfResidualTwo : Set where
data ArichetaCreditedWithPDividesLevelExtension : Set where

carnahanNotCreditedWithPadicBadLevelValuation :
  CarnahanCreditedWithPadicBadLevelValuation -> ⊥
carnahanNotCreditedWithPadicBadLevelValuation ()

francMasonNotCreditedWithPBTwistedLocalization :
  FrancMasonCreditedWithPBTwistedLocalization -> ⊥
francMasonNotCreditedWithPBTwistedLocalization ()

cmtAppendixNotCreditedWithProofOfResidualTwo :
  CMTAppendixCreditedWithProofOfResidualTwo -> ⊥
cmtAppendixNotCreditedWithProofOfResidualTwo ()

arichetaNotCreditedWithBadLevelExtension :
  ArichetaCreditedWithPDividesLevelExtension -> ⊥
arichetaNotCreditedWithBadLevelExtension ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record MixedCharacteristicTwistedCentralizerCutsetBoundary : Set where
  constructor mixed-characteristic-twisted-centralizer-cutset-boundary
  field
    pBTwistedCentralizerObjectClassicallySourced : Bool
    explicit2BTwistedSectorSourced : Bool
    ambientPadicMoonshineVOAAtEveryPrimeSourced : Bool
    individual2B3BHauptmodulPadicBehaviorSourced : Bool
    badLevelIgusaGeometrySourced : Bool
    p3ObservedPadicIncrementTwoRecorded : Bool
    p2ObservedPadicIncrementThreeRecorded : Bool
    mixedCharacteristicCompatibilitySquareSpecified : Bool
    mixedCharacteristicCompatibilitySquareInhabited : Bool
    p3NumericalSlopeMatchPromotedToTheorem : Bool
    attributionFirewallPreserved : Bool

canonicalMixedCharacteristicTwistedCentralizerCutsetBoundary :
  MixedCharacteristicTwistedCentralizerCutsetBoundary
canonicalMixedCharacteristicTwistedCentralizerCutsetBoundary =
  mixed-characteristic-twisted-centralizer-cutset-boundary
    true true true true true true true true false false true
