module DASHI.Moonshine.OggSSPSmallCharacteristicMonsterLocalCentralizerResidualExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC MONSTER LOCAL-CENTRALIZER RESIDUAL
--
-- SOURCE-NATIVE LOCAL GROUPS
--
-- 2B:
--   C_M(2B) = 2^(1+24).Co1.
--   The 2-part is 2^25 * 2^21 = 2^46.
--
-- 3B:
--   C_M(3B) = 3^(1+12).2.Suz.
--   The 3-part is 3^13 * 3^7 = 3^20.
--
-- Thus the full Monster 2- and 3-adic exponents are already visible in the
-- corresponding local centralizers.  Equivalently, the 2B and 3B class sizes
-- are prime to 2 and 3 respectively.
--
-- CROSS-WELD WITH DUNCAN--SWISHER / DWORK
--
-- Duncan--Swisher continuation:
--
--   p=2 : 36 = 25 + 11
--   p=3 : 18 = 13 +  5.
--
-- Full local-centralizer exponents:
--
--   p=2 : 46 = 25 + 21
--   p=3 : 20 = 13 +  7.
--
-- Hence the exceptional gaps localize entirely in the quotient sporadic
-- factors after the extraspecial p-core is paid:
--
--   10 = 21 - 11   (Co1 quotient p-part residual)
--    2 =  7 -  5   (Suz quotient p-part residual).
--
-- The numbers 11 and 5 are independently visible as the constant numerators
-- in Dwork's small-prime principal-part bounds:
--
--   2 ord_2 A_n >= 11 + 13 n,
--   2 ord_3 A_n >=  5 +  7 n.
--
-- This module proves the arithmetic decompositions.  It does NOT prove that
-- the Dwork intercept is a quotient-centralizer valuation, nor that quotient
-- residuals cause the Monster correction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Moonshine.OggSSPSmallCharacteristicExceptionalJCollisionExact as Collision
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution
import DASHI.Wikimedia.IbrahimMonster3BInertiaPhaseResolutionProducerSnowballExact as ThreeB

------------------------------------------------------------------------
-- 1. Attributed local-group sources.
------------------------------------------------------------------------

monsterCharacterVerification : Source.AttributedSource
monsterCharacterVerification =
  Source.mkNoDOISource
    "Thomas Breuer, Kay Magaard, and Robert A. Wilson"
    "Verification of the conjugacy classes and ordinary character table of the Monster"
    "Journal of Algebra / author preprint and published verification"
    "2025"
    "https://www.sciencedirect.com/science/article/pii/S002186932500571X"
    Source.academicArticleSource
    "source for the two Monster involution centralizers, including C_M(2B)=2^(1+24).Co1; used only for the local-group structure and not for the DASHI residual cross-weld"
    Source.publicAttribution

atlasCo1 : Source.AttributedSource
atlasCo1 =
  Source.mkNoDOISource
    "ATLAS of Finite Group Representations contributors"
    "ATLAS: Conway group Co1"
    "ATLAS web database"
    "current"
    "https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Co1/"
    (Source.namedSourceKind "finite-group atlas database")
    "records |Co1|=2^21*3^9*5^4*7^2*11*13*23; computational/reference source for the exact 2-adic quotient exponent 21"
    Source.publicAttribution

barracloughWilson : Source.AttributedSource
barracloughWilson =
  Source.mkDOISource
    "R. W. Barraclough and R. A. Wilson"
    "The Character Table of a Maximal Subgroup of the Monster"
    "LMS Journal of Computation and Mathematics 10, 161-175"
    "2007"
    "10.1112/S1461157000001352"
    "https://doi.org/10.1112/S1461157000001352"
    Source.academicArticleSource
    "primary source for N(3B)=3^(1+12).2.Suz:2 and the centralizer/inertia subgroup 3^(1+12).2.Suz; used for local 3B structure, not for the DASHI valuation residual interpretation"
    Source.publicAttribution

atlasSuz : Source.AttributedSource
atlasSuz =
  Source.mkNoDOISource
    "ATLAS of Finite Groups / Encyclopedia of Mathematics"
    "Suzuki sporadic group order"
    "finite simple group reference"
    "current reference"
    "https://encyclopediaofmath.org/wiki/Suzuki_sporadic_group"
    Source.academicBookSource
    "records |Suz|=2^13*3^7*5^2*7*11*13; used for the exact 3-adic quotient exponent 7"
    Source.publicAttribution

monsterLocalCentralizerAtlas : Source.AttributedSourceAtlas
monsterLocalCentralizerAtlas =
  Source.mkSourceAtlas
    "Monster exceptional-prime local-centralizer atlas"
    "DASHI.Moonshine.OggSSPSmallCharacteristicMonsterLocalCentralizerResidualExact"
    (monsterCharacterVerification ∷ atlasCo1 ∷ barracloughWilson ∷ atlasSuz ∷ [])
    "separates sourced 2B/3B local-group structures and quotient orders from the repository cross-module comparison with Duncan--Swisher and Dwork"

------------------------------------------------------------------------
-- 2. Exact p-core and quotient exponents.
------------------------------------------------------------------------

data ExceptionalMonsterPrime : Set where
  p2 p3 : ExceptionalMonsterPrime

extraspecialCoreExponent :
  ExceptionalMonsterPrime ->
  Nat
extraspecialCoreExponent p2 = 25  -- 1 + 24
extraspecialCoreExponent p3 = 13  -- 1 + 12

sporadicQuotientExponent :
  ExceptionalMonsterPrime ->
  Nat
sporadicQuotientExponent p2 = 21  -- v_2(|Co1|)
sporadicQuotientExponent p3 = 7   -- v_3(|Suz|)

localCentralizerExponent :
  ExceptionalMonsterPrime ->
  Nat
localCentralizerExponent p =
  extraspecialCoreExponent p + sporadicQuotientExponent p

p2LocalCentralizerExponentIsFortySix :
  localCentralizerExponent p2 ≡ 46
p2LocalCentralizerExponentIsFortySix = refl

p3LocalCentralizerExponentIsTwenty :
  localCentralizerExponent p3 ≡ 20
p3LocalCentralizerExponentIsTwenty = refl

p2LocalCentralizerMatchesMonsterExponent :
  localCentralizerExponent p2
  ≡ Exponent.monsterOrderExponent Lane.p2
p2LocalCentralizerMatchesMonsterExponent = refl

p3LocalCentralizerMatchesMonsterExponent :
  localCentralizerExponent p3
  ≡ Exponent.monsterOrderExponent Lane.p3
p3LocalCentralizerMatchesMonsterExponent = refl

------------------------------------------------------------------------
-- 3. Duncan--Swisher continuation split after paying the same p-core.
------------------------------------------------------------------------

dworkInterceptNumerator :
  ExceptionalMonsterPrime ->
  Nat
dworkInterceptNumerator p2 = 11
dworkInterceptNumerator p3 = 5

continuationFromCoreAndIntercept :
  ExceptionalMonsterPrime ->
  Nat
continuationFromCoreAndIntercept p =
  extraspecialCoreExponent p + dworkInterceptNumerator p

p2ContinuationSplit :
  continuationFromCoreAndIntercept p2
  ≡ Exponent.duncanSwisherExceptionalRHS Lane.p2
p2ContinuationSplit = refl

p3ContinuationSplit :
  continuationFromCoreAndIntercept p3
  ≡ Exponent.duncanSwisherExceptionalRHS Lane.p3
p3ContinuationSplit = refl

------------------------------------------------------------------------
-- 4. Quotient residuals.
------------------------------------------------------------------------

quotientResidual :
  ExceptionalMonsterPrime ->
  Nat
quotientResidual p2 = 10
quotientResidual p3 = 2

p2QuotientExponentSplitsInterceptPlusResidual :
  sporadicQuotientExponent p2
  ≡ dworkInterceptNumerator p2 + quotientResidual p2
p2QuotientExponentSplitsInterceptPlusResidual = refl

p3QuotientExponentSplitsInterceptPlusResidual :
  sporadicQuotientExponent p3
  ≡ dworkInterceptNumerator p3 + quotientResidual p3
p3QuotientExponentSplitsInterceptPlusResidual = refl

p2ResidualMatchesMonsterGap :
  Exponent.monsterOrderExponent Lane.p2
  ≡ Exponent.duncanSwisherExceptionalRHS Lane.p2 + quotientResidual p2
p2ResidualMatchesMonsterGap =
  Exponent.p2ExceptionalGap

p3ResidualMatchesMonsterGap :
  Exponent.monsterOrderExponent Lane.p3
  ≡ Exponent.duncanSwisherExceptionalRHS Lane.p3 + quotientResidual p3
p3ResidualMatchesMonsterGap =
  Exponent.p3ExceptionalGap

------------------------------------------------------------------------
-- 5. Dwork small-prime principal-part numerator shape.
--
-- Dwork's original stronger estimates give:
--
--   p=2 : 2 ord A_n >= 11 + 13 n
--   p=3 : 2 ord A_n >=  5 +  7 n.
--
-- We record only the integer coefficient surface here.  The analytic
-- inequality itself remains source authority until separately formalized.
------------------------------------------------------------------------

dworkSlopeNumerator :
  ExceptionalMonsterPrime ->
  Nat
dworkSlopeNumerator p2 = 13
dworkSlopeNumerator p3 = 7

p2DworkInterceptIsContinuationBeyondCore :
  Exponent.duncanSwisherExceptionalRHS Lane.p2
  ≡ extraspecialCoreExponent p2 + dworkInterceptNumerator p2
p2DworkInterceptIsContinuationBeyondCore = refl

p3DworkInterceptIsContinuationBeyondCore :
  Exponent.duncanSwisherExceptionalRHS Lane.p3
  ≡ extraspecialCoreExponent p3 + dworkInterceptNumerator p3
p3DworkInterceptIsContinuationBeyondCore = refl

p3DworkSlopeEqualsSuzThreeExponent :
  dworkSlopeNumerator p3
  ≡ sporadicQuotientExponent p3
p3DworkSlopeEqualsSuzThreeExponent = refl

------------------------------------------------------------------------
-- 6. Non-promotion boundary.
------------------------------------------------------------------------

data DworkInterceptIsCentralizerQuotientValuation : Set where
data QuotientResidualCausesMonsterCorrection : Set where
data LocalCentralizerEqualityExplainsMoonshine : Set where
data P3SlopeEqualityCreatesSameObjectSuzukiRecognition : Set where

dworkInterceptNotYetCentralizerQuotientValuation :
  DworkInterceptIsCentralizerQuotientValuation -> ⊥
dworkInterceptNotYetCentralizerQuotientValuation ()

quotientResidualCausalityStillOpen :
  QuotientResidualCausesMonsterCorrection -> ⊥
quotientResidualCausalityStillOpen ()

localCentralizerEqualityDoesNotExplainMoonshine :
  LocalCentralizerEqualityExplainsMoonshine -> ⊥
localCentralizerEqualityDoesNotExplainMoonshine ()

p3SlopeEqualityDoesNotCreateSuzukiRecognition :
  P3SlopeEqualityCreatesSameObjectSuzukiRecognition -> ⊥
p3SlopeEqualityDoesNotCreateSuzukiRecognition ()

------------------------------------------------------------------------
-- 7. Existing 3B source-native lane remains separate.
------------------------------------------------------------------------

threeBInertiaFrontier :
  ThreeB.InertiaPhaseResolutionFrontier
threeBInertiaFrontier =
  ThreeB.currentPhaseResolutionProducerReceipt
    |> λ _ -> ThreeB.currentInertiaPhaseResolutionFrontier
  where
    infixl 0 _|>_
    _|>_ : ∀ {A B : Set} -> A -> (A -> B) -> B
    x |> f = f x

------------------------------------------------------------------------
-- 8. Status.
------------------------------------------------------------------------

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record MonsterLocalCentralizerResidualBoundary : Set where
  constructor monster-local-centralizer-residual-boundary
  field
    p2CentralizerStructureSourced : Bool
    p3CentralizerStructureSourced : Bool
    co1TwoExponentTwentyOneSourced : Bool
    suzThreeExponentSevenSourced : Bool
    p2LocalCentralizerPaysFullMonsterExponent : Bool
    p3LocalCentralizerPaysFullMonsterExponent : Bool
    p2ContinuationPaysSameCorePlusEleven : Bool
    p3ContinuationPaysSameCorePlusFive : Bool
    p2ResidualLocalizesToCo1QuotientTen : Bool
    p3ResidualLocalizesToSuzQuotientTwo : Bool
    dworkInterceptIdentifiedWithGroupValuation : Bool
    quotientResidualMechanismProved : Bool
    localCentralizerEqualityExplainsMoonshine : Bool

canonicalMonsterLocalCentralizerResidualBoundary :
  MonsterLocalCentralizerResidualBoundary
canonicalMonsterLocalCentralizerResidualBoundary =
  monster-local-centralizer-residual-boundary
    true true true true
    true true true true
    true true
    false false false
