module DASHI.Moonshine.OggSSPSmallPrimeMonsterLocalCentralizerValuationExact where

------------------------------------------------------------------------
-- SMALL-PRIME MONSTER LOCAL-CENTRALIZER VALUATION
--
-- EXTERNAL MONSTER-LOCAL INPUT
--
-- Standard ATLAS / GAP character-table data:
--
--   C_M(2B) has shape 2^(1+24).Co1,
--   |Co1|_2 = 2^21,
--
-- so
--
--   v2(|C_M(2B)|) = 25 + 21 = 46.
--
-- Standard 3-local data:
--
--   C_M(3B) has shape 3^(1+12).2Suz,
--   |Suz|_3 = 3^7,
--
-- so
--
--   v3(|C_M(3B)|) = 13 + 7 = 20.
--
-- DASHI CONSEQUENCE
--
-- The exceptional residuals no longer need to be defined by subtracting the
-- published Duncan--Swisher value from the TOTAL Monster order.  They are also
-- exactly the defects between the Duncan--Swisher small-prime arithmetic
-- baseline and independently standard Monster LOCAL CENTRALIZER valuations:
--
--   46 - 36 = 10,
--   20 - 18 =  2.
--
-- FIREWALL
--
-- This does NOT prove that the bad-level Igusa/inertia object is the 2B/3B
-- centralizer, nor that its analytic valuation is the difference above.
-- It supplies a strictly better independent Monster-side recognition target.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat using (_-_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPSmallCharacteristicMonsterBridgeFailureLocalizationExact as Bridge
import DASHI.Moonshine.OggSSPSmallCharacteristicHauptmodulTermBaselineExact as Baseline
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source ledger.
------------------------------------------------------------------------

monster2BCentralizerSource : Source.AttributedSource
monster2BCentralizerSource =
  Source.mkNoDOISource
    "GAP Character Table Library / ATLAS of Finite Groups"
    "Character table information for 2^1+24.Co1"
    "CTblLib / ATLAS"
    ""
    "https://www.math.rwth-aachen.de/homes/Thomas.Breuer/ctbllib/ctbltoc/data/2%5E1%2B24.Co1.html"
    Source.institutionalSource
    "standard Monster 2B-centralizer source: group shape 2^(1+24).Co1 and exact order with 2-primary factor 2^46"
    Source.publicAttribution

co1Source : Source.AttributedSource
co1Source =
  Source.mkNoDOISource
    "ATLAS of Finite Group Representations"
    "Conway group Co1"
    "ATLAS"
    ""
    "https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Co1/"
    Source.institutionalSource
    "exact order |Co1| = 2^21 * 3^9 * 5^4 * 7^2 * 11 * 13 * 23"
    Source.publicAttribution

monster3BCentralizerSource : Source.AttributedSource
monster3BCentralizerSource =
  Source.mkNoDOISource
    "ATLAS / standard Monster local subgroup data"
    "Monster 3B centralizer"
    "ATLAS / CCN local data"
    ""
    "https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M/"
    Source.institutionalSource
    "standard 3B centralizer shape 3^(1+12).2Suz; the extra outer .2 belongs to the 3B normalizer rather than changing the 3-primary valuation"
    Source.publicAttribution

suzukiSource : Source.AttributedSource
suzukiSource =
  Source.mkNoDOISource
    "ATLAS of Finite Group Representations"
    "Suzuki sporadic group Suz"
    "ATLAS"
    ""
    "https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Suz/"
    Source.institutionalSource
    "exact order |Suz| = 2^13 * 3^7 * 5^2 * 7 * 11 * 13"
    Source.publicAttribution

localCentralizerSourceAtlas : Source.AttributedSourceAtlas
localCentralizerSourceAtlas =
  Source.mkSourceAtlas
    "Monster small-prime local-centralizer valuation atlas"
    "DASHI.Moonshine.OggSSPSmallPrimeMonsterLocalCentralizerValuationExact"
    (monster2BCentralizerSource
      ∷ co1Source
      ∷ monster3BCentralizerSource
      ∷ suzukiSource
      ∷ [])
    "external sources own local subgroup shapes and group orders; DASHI owns only the valuation subtraction/cross-weld to the Duncan--Swisher baseline"

------------------------------------------------------------------------
-- 2. p=2 local valuation.
------------------------------------------------------------------------

p2ExtraspecialTwoExponent : Nat
p2ExtraspecialTwoExponent = 25

co1TwoExponent : Nat
co1TwoExponent = 21

p2LocalCentralizerTwoExponent : Nat
p2LocalCentralizerTwoExponent =
  p2ExtraspecialTwoExponent + co1TwoExponent

p2LocalCentralizerExponentIsFortySix :
  p2LocalCentralizerTwoExponent ≡ 46
p2LocalCentralizerExponentIsFortySix = refl

p2DuncanSwisherBaseline : Nat
p2DuncanSwisherBaseline =
  Baseline.baselineTotal Baseline.pTwo

p2LocalCentralizerResidual : Nat
p2LocalCentralizerResidual =
  p2LocalCentralizerTwoExponent - p2DuncanSwisherBaseline

p2LocalCentralizerResidualIsTen :
  p2LocalCentralizerResidual ≡ 10
p2LocalCentralizerResidualIsTen = refl

------------------------------------------------------------------------
-- 3. p=3 local valuation.
------------------------------------------------------------------------

p3ExtraspecialThreeExponent : Nat
p3ExtraspecialThreeExponent = 13

suzukiThreeExponent : Nat
suzukiThreeExponent = 7

p3LocalCentralizerThreeExponent : Nat
p3LocalCentralizerThreeExponent =
  p3ExtraspecialThreeExponent + suzukiThreeExponent

p3LocalCentralizerExponentIsTwenty :
  p3LocalCentralizerThreeExponent ≡ 20
p3LocalCentralizerExponentIsTwenty = refl

p3DuncanSwisherBaseline : Nat
p3DuncanSwisherBaseline =
  Baseline.baselineTotal Baseline.pThree

p3LocalCentralizerResidual : Nat
p3LocalCentralizerResidual =
  p3LocalCentralizerThreeExponent - p3DuncanSwisherBaseline

p3LocalCentralizerResidualIsTwo :
  p3LocalCentralizerResidual ≡ 2
p3LocalCentralizerResidualIsTwo = refl

------------------------------------------------------------------------
-- 4. Exact agreement with the existing bridge-gap coordinates.
------------------------------------------------------------------------

p2LocalResidualAgreesWithBridgeGap :
  p2LocalCentralizerResidual ≡ Bridge.p2BridgeGap
p2LocalResidualAgreesWithBridgeGap = refl

p3LocalResidualAgreesWithBridgeGap :
  p3LocalCentralizerResidual ≡ Bridge.p3BridgeGap
p3LocalResidualAgreesWithBridgeGap = refl

------------------------------------------------------------------------
-- 5. Stronger target type.
--
-- A future modular/geometric bridge should recognise the relevant LOCAL
-- centralizer p-primary structure, not merely reproduce the total Monster
-- exponent as an unstructured Nat.
------------------------------------------------------------------------

data MonsterLocalPrime : Set where
  monsterTwo monsterThree : MonsterLocalPrime

localCentralizerExponent :
  MonsterLocalPrime ->
  Nat
localCentralizerExponent monsterTwo =
  p2LocalCentralizerTwoExponent
localCentralizerExponent monsterThree =
  p3LocalCentralizerThreeExponent

publishedArithmeticBaseline :
  MonsterLocalPrime ->
  Nat
publishedArithmeticBaseline monsterTwo =
  p2DuncanSwisherBaseline
publishedArithmeticBaseline monsterThree =
  p3DuncanSwisherBaseline

localCentralizerDefect :
  MonsterLocalPrime ->
  Nat
localCentralizerDefect monsterTwo =
  p2LocalCentralizerResidual
localCentralizerDefect monsterThree =
  p3LocalCentralizerResidual

record MonsterLocalCentralizerRecognitionAuthority : Set₁ where
  field
    ExceptionalGeometricObject : Set

    p2Object :
      ExceptionalGeometricObject

    p3Object :
      ExceptionalGeometricObject

    geometricValuation :
      MonsterLocalPrime ->
      ExceptionalGeometricObject ->
      Nat

    p2RecognisesLocalCentralizerDefect :
      geometricValuation monsterTwo p2Object
      ≡
      localCentralizerDefect monsterTwo

    p3RecognisesLocalCentralizerDefect :
      geometricValuation monsterThree p3Object
      ≡
      localCentralizerDefect monsterThree

    objectDefinedWithoutMonsterOrderTarget :
      Bool
    objectDefinedWithoutMonsterOrderTargetIsTrue :
      objectDefinedWithoutMonsterOrderTarget ≡ true

    sourceOrProofAuthorityForGeometricValuation :
      Bool
    sourceOrProofAuthorityForGeometricValuationIsTrue :
      sourceOrProofAuthorityForGeometricValuation ≡ true

    sameObjectRefinesDuncanSwisherArithmetic :
      Bool
    sameObjectRefinesDuncanSwisherArithmeticIsTrue :
      sameObjectRefinesDuncanSwisherArithmetic ≡ true

    sameObjectRecognisesMonsterLocalCentralizer :
      Bool
    sameObjectRecognisesMonsterLocalCentralizerIsTrue :
      sameObjectRecognisesMonsterLocalCentralizer ≡ true

open MonsterLocalCentralizerRecognitionAuthority public

------------------------------------------------------------------------
-- 6. Firewalls.
------------------------------------------------------------------------

data LocalCentralizerValuationProvesModularBridge : Set where
data EqualDefectIdentifiesGeometricObjectWithCentralizer : Set where
data AtlasLocalDataAttributedDASHICorrection : Set where
data LocalCentralizerAuthorityAlreadyInhabited : Set where

localCentralizerValuationDoesNotProveModularBridge :
  LocalCentralizerValuationProvesModularBridge -> ⊥
localCentralizerValuationDoesNotProveModularBridge ()

equalDefectDoesNotIdentifyObjects :
  EqualDefectIdentifiesGeometricObjectWithCentralizer -> ⊥
equalDefectDoesNotIdentifyObjects ()

atlasNotCreditedWithDASHICorrection :
  AtlasLocalDataAttributedDASHICorrection -> ⊥
atlasNotCreditedWithDASHICorrection ()

localCentralizerRecognitionStillOpen :
  LocalCentralizerAuthorityAlreadyInhabited -> ⊥
localCentralizerRecognitionStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record SmallPrimeMonsterLocalCentralizerBoundary : Set where
  constructor small-prime-monster-local-centralizer-boundary
  field
    monster2BCentralizerExternallySourced : Bool
    co1TwoExponentTwentyOneExternallySourced : Bool
    monster3BCentralizerExternallySourced : Bool
    suzukiThreeExponentSevenExternallySourced : Bool
    p2LocalCentralizerExponentFortySixExact : Bool
    p3LocalCentralizerExponentTwentyExact : Bool
    p2LocalDefectTenExact : Bool
    p3LocalDefectTwoExact : Bool
    localDefectsAgreeWithExistingBridgeGaps : Bool
    targetDefinedWithoutTotalMonsterOrderSubtraction : Bool
    modularGeometricRecognitionProved : Bool
    sameObjectIdentificationClaimed : Bool
    attributionFirewallPreserved : Bool

canonicalSmallPrimeMonsterLocalCentralizerBoundary :
  SmallPrimeMonsterLocalCentralizerBoundary
canonicalSmallPrimeMonsterLocalCentralizerBoundary =
  small-prime-monster-local-centralizer-boundary
    true true true true
    true true true true true true
    false false true
