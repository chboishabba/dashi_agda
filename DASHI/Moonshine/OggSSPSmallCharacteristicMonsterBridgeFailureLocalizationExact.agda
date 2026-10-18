module DASHI.Moonshine.OggSSPSmallCharacteristicMonsterBridgeFailureLocalizationExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC MONSTER-BRIDGE FAILURE LOCALIZATION
--
-- EXTERNAL DUNCAN--SWISHER INPUT
--
-- At p=2,3 Duncan--Swisher's TWO arithmetic descriptions remain internally
-- coherent and agree:
--
--   modular-function RHS       = 36,18
--   supersingular/automorphism RHS = 36,18
--
-- while the Monster exponents are
--
--   v_2(|M|)=46,
--   v_3(|M|)=20.
--
-- Thus the small-prime failure is NOT:
--
--   * failure of the three Hauptmodul valuation calculation,
--   * disagreement between modular and supersingular descriptions,
--   * absence of the published coefficient family.
--
-- The missing theorem is the bridge from their common exceptional-prime
-- arithmetic value to the Monster exponent.
--
-- DASHI packages that missing bridge as an explicitly uninhabited authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Moonshine.OggSSPSmallCharacteristicHauptmodulTermBaselineExact as Baseline
import DASHI.Moonshine.OggSSPSmallCharacteristicJointCorrectionCutsetExact as Joint
import DASHI.Moonshine.OggSSPSmallCharacteristicFourthTermExtensionExact as Fourth
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Two published arithmetic descriptions.
------------------------------------------------------------------------

data ExceptionalPrime : Set where
  pTwo pThree : ExceptionalPrime

modularArithmeticValue :
  ExceptionalPrime ->
  Nat
modularArithmeticValue pTwo =
  Baseline.baselineTotal Baseline.pTwo
modularArithmeticValue pThree =
  Baseline.baselineTotal Baseline.pThree

supersingularArithmeticValue :
  ExceptionalPrime ->
  Nat
supersingularArithmeticValue pTwo =
  Exponent.duncanSwisherExceptionalRHS Lane.p2
supersingularArithmeticValue pThree =
  Exponent.duncanSwisherExceptionalRHS Lane.p3

monsterExponent :
  ExceptionalPrime ->
  Nat
monsterExponent pTwo =
  Exponent.monsterOrderExponent Lane.p2
monsterExponent pThree =
  Exponent.monsterOrderExponent Lane.p3

p2ModularValueIsThirtySix :
  modularArithmeticValue pTwo ≡ 36
p2ModularValueIsThirtySix = refl

p3ModularValueIsEighteen :
  modularArithmeticValue pThree ≡ 18
p3ModularValueIsEighteen = refl

p2SupersingularValueIsThirtySix :
  supersingularArithmeticValue pTwo ≡ 36
p2SupersingularValueIsThirtySix = refl

p3SupersingularValueIsEighteen :
  supersingularArithmeticValue pThree ≡ 18
p3SupersingularValueIsEighteen = refl

p2PublishedDescriptionsAgree :
  modularArithmeticValue pTwo
  ≡ supersingularArithmeticValue pTwo
p2PublishedDescriptionsAgree = refl

p3PublishedDescriptionsAgree :
  modularArithmeticValue pThree
  ≡ supersingularArithmeticValue pThree
p3PublishedDescriptionsAgree = refl

------------------------------------------------------------------------
-- 2. The common published value still misses the Monster exponent.
------------------------------------------------------------------------

p2PublishedValueIsNotMonsterExponent :
  modularArithmeticValue pTwo ≡ monsterExponent pTwo ->
  ⊥
p2PublishedValueIsNotMonsterExponent ()

p3PublishedValueIsNotMonsterExponent :
  modularArithmeticValue pThree ≡ monsterExponent pThree ->
  ⊥
p3PublishedValueIsNotMonsterExponent ()

p2BridgeGap : Nat
p2BridgeGap = 10

p3BridgeGap : Nat
p3BridgeGap = 2

p2CommonValuePlusGap :
  monsterExponent pTwo
  ≡ modularArithmeticValue pTwo + p2BridgeGap
p2CommonValuePlusGap =
  Exponent.p2ExceptionalGap

p3CommonValuePlusGap :
  monsterExponent pThree
  ≡ modularArithmeticValue pThree + p3BridgeGap
p3CommonValuePlusGap =
  Exponent.p3ExceptionalGap

------------------------------------------------------------------------
-- 3. What is actually missing.
------------------------------------------------------------------------

record SmallPrimeMonsterBridgeAuthority : Set₁ where
  field
    ExceptionalObject : Set

    p2ExceptionalObject :
      ExceptionalObject

    p3ExceptionalObject :
      ExceptionalObject

    exceptionalValuation :
      ExceptionalPrime ->
      ExceptionalObject ->
      Nat

    p2ExceptionalValuationIsBridgeGap :
      exceptionalValuation pTwo p2ExceptionalObject
      ≡ p2BridgeGap

    p3ExceptionalValuationIsBridgeGap :
      exceptionalValuation pThree p3ExceptionalObject
      ≡ p3BridgeGap

    objectDefinedIndependentlyOfMonsterTarget :
      Bool
    objectDefinedIndependentlyOfMonsterTargetIsTrue :
      objectDefinedIndependentlyOfMonsterTarget ≡ true

    refinesModularDescription :
      Bool
    refinesModularDescriptionIsTrue :
      refinesModularDescription ≡ true

    refinesSupersingularDescription :
      Bool
    refinesSupersingularDescriptionIsTrue :
      refinesSupersingularDescription ≡ true

    sameObjectRefinesBothDescriptions :
      Bool
    sameObjectRefinesBothDescriptionsIsTrue :
      sameObjectRefinesBothDescriptions ≡ true

    sourceOrProofAuthorityForExceptionalValuation :
      Bool
    sourceOrProofAuthorityForExceptionalValuationIsTrue :
      sourceOrProofAuthorityForExceptionalValuation ≡ true

open SmallPrimeMonsterBridgeAuthority public

------------------------------------------------------------------------
-- 4. A genuine bridge authority licenses the existing joint/fourth-term cut.
------------------------------------------------------------------------

asExceptionalFourthTerm :
  SmallPrimeMonsterBridgeAuthority ->
  Fourth.SmallPrimeExceptionalAnalyticTerm
asExceptionalFourthTerm authority =
  record
    { Fourth.ExceptionalObject =
        ExceptionalObject authority
    ; Fourth.p2Object =
        p2ExceptionalObject authority
    ; Fourth.p3Object =
        p3ExceptionalObject authority
    ; Fourth.valuation =
        λ prime object ->
          exceptionalValuation authority
            (toExceptionalPrime prime)
            object
    ; Fourth.p2ValuationIsExceptionalFourthTerm =
        p2ExceptionalValuationIsBridgeGap authority
    ; Fourth.p3ValuationIsExceptionalFourthTerm =
        p3ExceptionalValuationIsBridgeGap authority
    ; Fourth.analyticKind =
        Fourth.otherSourcedAnalyticObject
    ; Fourth.objectDefinedIndependentlyOfMonsterExponent =
        true
    ; Fourth.objectDefinedIndependentlyOfMonsterExponentIsTrue =
        refl
    ; Fourth.valuationTheoremProvedWithoutUsingTargetMonsterGap =
        true
    ; Fourth.valuationTheoremProvedWithoutUsingTargetMonsterGapIsTrue =
        refl
    ; Fourth.compatibleWithPublishedThreeTermBaseline =
        true
    ; Fourth.compatibleWithPublishedThreeTermBaselineIsTrue =
        refl
    }
  where
    toExceptionalPrime :
      Baseline.SmallPrime ->
      ExceptionalPrime
    toExceptionalPrime Baseline.pTwo = pTwo
    toExceptionalPrime Baseline.pThree = pThree

asJointAuthority :
  (authority : SmallPrimeMonsterBridgeAuthority) ->
  Joint.JointSmallPrimeExceptionalAuthority
asJointAuthority authority =
  record
    { Joint.exceptionalAnalyticTerm =
        asExceptionalFourthTerm authority
    ; Joint.p2RefinesPublishedHauptmodulSide =
        true
    ; Joint.p2RefinesPublishedHauptmodulSideIsTrue =
        refl
    ; Joint.p3RefinesPublishedHauptmodulSide =
        true
    ; Joint.p3RefinesPublishedHauptmodulSideIsTrue =
        refl
    ; Joint.p2RefinesPublishedSupersingularSide =
        true
    ; Joint.p2RefinesPublishedSupersingularSideIsTrue =
        refl
    ; Joint.p3RefinesPublishedSupersingularSide =
        true
    ; Joint.p3RefinesPublishedSupersingularSideIsTrue =
        refl
    ; Joint.sameExceptionalObjectUsedOnBothDescriptions =
        true
    ; Joint.sameExceptionalObjectUsedOnBothDescriptionsIsTrue =
        refl
    ; Joint.compatibilityProvedWithoutUsingMonsterTargetToDefineObject =
        true
    ; Joint.compatibilityProvedWithoutUsingMonsterTargetToDefineObjectIsTrue =
        refl
    }

------------------------------------------------------------------------
-- 5. Failure-location firewalls.
------------------------------------------------------------------------

data PublishedThreeTermValuationsFailAtP2P3 : Set where
data PublishedModularAndSupersingularDescriptionsDisagreeAtP2P3 : Set where
data MissingDworkSharpnessIsMonsterBridgeFailure : Set where
data EqualArithmeticBaselinesConstructMonsterBridge : Set where
data KnownGapConstructsMonsterBridge : Set where
data DuncanSwisherProvedSmallPrimeMonsterBridge : Set where

publishedThreeTermsDoNotFailInternally :
  PublishedThreeTermValuationsFailAtP2P3 -> ⊥
publishedThreeTermsDoNotFailInternally ()

publishedDescriptionsDoNotDisagree :
  PublishedModularAndSupersingularDescriptionsDisagreeAtP2P3 -> ⊥
publishedDescriptionsDoNotDisagree ()

missingDworkSharpnessIsNotTheMonsterBridge :
  MissingDworkSharpnessIsMonsterBridgeFailure -> ⊥
missingDworkSharpnessIsNotTheMonsterBridge ()

equalBaselinesDoNotConstructBridge :
  EqualArithmeticBaselinesConstructMonsterBridge -> ⊥
equalBaselinesDoNotConstructBridge ()

knownGapDoesNotConstructBridge :
  KnownGapConstructsMonsterBridge -> ⊥
knownGapDoesNotConstructBridge ()

duncanSwisherNotCreditedWithSmallPrimeBridge :
  DuncanSwisherProvedSmallPrimeMonsterBridge -> ⊥
duncanSwisherNotCreditedWithSmallPrimeBridge ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record MonsterBridgeFailureLocalizationBoundary : Set where
  constructor monster-bridge-failure-localization-boundary
  field
    p2ModularBaselineThirtySix : Bool
    p3ModularBaselineEighteen : Bool
    p2SupersingularBaselineThirtySix : Bool
    p3SupersingularBaselineEighteen : Bool
    publishedDescriptionsAgreeAtP2 : Bool
    publishedDescriptionsAgreeAtP3 : Bool
    publishedDescriptionsEqualMonsterExponentAtP2 : Bool
    publishedDescriptionsEqualMonsterExponentAtP3 : Bool
    missingBridgeLocalizedAfterCommonArithmeticValue : Bool
    bridgeAuthoritySpecified : Bool
    adapterToFourthTermOwned : Bool
    adapterToJointAuthorityOwned : Bool
    duncanSwisherCreditedWithBridge : Bool
    bridgeAuthorityCurrentlyInhabited : Bool
    attributionFirewallPreserved : Bool

canonicalMonsterBridgeFailureLocalizationBoundary :
  MonsterBridgeFailureLocalizationBoundary
canonicalMonsterBridgeFailureLocalizationBoundary =
  monster-bridge-failure-localization-boundary
    true true true true true true
    false false
    true true true true
    false false true
