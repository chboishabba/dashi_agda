module DASHI.Moonshine.OggSSPSmallCharacteristicMathieuQuotientResidualExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC MATHIEU QUOTIENT RESIDUAL
--
-- SOURCE-BACKED LOCAL SUBGROUPS
--
-- 2B local quotient:
--
--   C_M(2B) = 2^(1+24).Co1
--   Co1 contains the standard maximal subgroup 2^11:M24.
--
-- Hence, at the level of 2-adic orders,
--
--   v_2(Co1) = 21 = 11 + 10
--
-- with v_2(M24)=10.
--
-- 3B local quotient:
--
--   C_M(3B) = 3^(1+12).2.Suz
--   Suz contains the standard maximal subgroup 3^5:M11.
--
-- Hence, at the level of 3-adic orders,
--
--   v_3(Suz) = 7 = 5 + 2
--
-- with v_3(M11)=2.
--
-- CROSS-WELD
--
-- Dwork's small-prime principal-part bounds have constant numerators
--
--   11 (p=2), 5 (p=3),
--
-- while Duncan--Swisher's continuation is
--
--   36 = 25 + 11
--   18 = 13 +  5.
--
-- The exact Monster exponents are
--
--   46 = 25 + 11 + 10
--   20 = 13 +  5 +  2.
--
-- Therefore the exceptional Monster gaps are exactly
--
--   R_2 = v_2(|M24|) = 10
--   R_3 = v_3(|M11|) =  2.
--
-- Attribution firewall:
-- the subgroup structures and group orders are source-backed;
-- the identification of the Dwork intercepts with the elementary-abelian
-- radicals, and the interpretation of the omitted Mathieu p-parts as the
-- arithmetic Monster correction, are DASHI cross-module inferences.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Moonshine.OggSSPSmallCharacteristicMonsterLocalCentralizerResidualExact as Local
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source atlas for the nested local subgroups.
------------------------------------------------------------------------

atlasCo1Maximal : Source.AttributedSource
atlasCo1Maximal =
  Source.mkNoDOISource
    "ATLAS of Finite Group Representations contributors"
    "Co1 maximal subgroup 2^11:M24"
    "ATLAS web database"
    "current"
    "https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Co1/"
    (Source.namedSourceKind "finite-group atlas database")
    "source-backed local subgroup structure Co1 >= 2^11:M24 and order data; does not state the Dwork/Monster residual cross-weld"
    Source.publicAttribution

atlasM24 : Source.AttributedSource
atlasM24 =
  Source.mkNoDOISource
    "ATLAS of Finite Group Representations contributors"
    "Mathieu group M24 order"
    "ATLAS web database"
    "current"
    "https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M24/"
    (Source.namedSourceKind "finite-group atlas database")
    "records the order of M24 and hence v_2(|M24|)=10; used only for finite-group arithmetic"
    Source.publicAttribution

atlasSuzMaximal : Source.AttributedSource
atlasSuzMaximal =
  Source.mkNoDOISource
    "ATLAS of Finite Group Representations contributors"
    "Suz maximal subgroup 3^5:M11"
    "ATLAS web database"
    "current"
    "https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Suz/"
    (Source.namedSourceKind "finite-group atlas database")
    "source-backed local subgroup structure Suz >= 3^5:M11 and order data; does not state the Dwork/Monster residual cross-weld"
    Source.publicAttribution

atlasM11 : Source.AttributedSource
atlasM11 =
  Source.mkNoDOISource
    "ATLAS of Finite Group Representations contributors"
    "Mathieu group M11 order"
    "ATLAS web database"
    "current"
    "https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M11/"
    (Source.namedSourceKind "finite-group atlas database")
    "records the order of M11 and hence v_3(|M11|)=2; used only for finite-group arithmetic"
    Source.publicAttribution

mathieuQuotientResidualSourceAtlas : Source.AttributedSourceAtlas
mathieuQuotientResidualSourceAtlas =
  Source.mkSourceAtlas
    "small-characteristic Mathieu quotient residual atlas"
    "DASHI.Moonshine.OggSSPSmallCharacteristicMathieuQuotientResidualExact"
    (atlasCo1Maximal ∷ atlasM24 ∷ atlasSuzMaximal ∷ atlasM11 ∷ [])
    "source-backed nested maximal subgroups and finite-group orders; Dwork-intercept and Monster-gap recognition remains a DASHI cross-module inference"

------------------------------------------------------------------------
-- 2. Exact nested p-adic exponent data.
------------------------------------------------------------------------

data SmallPrime : Set where
  p2 p3 : SmallPrime

quotientSporadicExponent :
  SmallPrime ->
  Nat
quotientSporadicExponent p2 = 21
quotientSporadicExponent p3 = 7

localRadicalExponent :
  SmallPrime ->
  Nat
localRadicalExponent p2 = 11
localRadicalExponent p3 = 5

mathieuQuotientExponent :
  SmallPrime ->
  Nat
mathieuQuotientExponent p2 = 10
mathieuQuotientExponent p3 = 2

p2Co1Split :
  quotientSporadicExponent p2
  ≡
  localRadicalExponent p2 + mathieuQuotientExponent p2
p2Co1Split = refl

p3SuzSplit :
  quotientSporadicExponent p3
  ≡
  localRadicalExponent p3 + mathieuQuotientExponent p3
p3SuzSplit = refl

------------------------------------------------------------------------
-- 3. Dwork intercept alignment.
------------------------------------------------------------------------

p2DworkInterceptMatchesLocalRadicalExponent :
  Local.dworkInterceptNumerator Local.p2
  ≡
  localRadicalExponent p2
p2DworkInterceptMatchesLocalRadicalExponent = refl

p3DworkInterceptMatchesLocalRadicalExponent :
  Local.dworkInterceptNumerator Local.p3
  ≡
  localRadicalExponent p3
p3DworkInterceptMatchesLocalRadicalExponent = refl

------------------------------------------------------------------------
-- 4. Monster residual = Mathieu p-part at the Nat surface.
------------------------------------------------------------------------

p2MathieuExponentIsMonsterGap :
  mathieuQuotientExponent p2 ≡ 10
p2MathieuExponentIsMonsterGap = refl

p3MathieuExponentIsMonsterGap :
  mathieuQuotientExponent p3 ≡ 2
p3MathieuExponentIsMonsterGap = refl

p2MonsterExponentNestedSplit :
  Exponent.monsterOrderExponent Lane.p2
  ≡
  Local.extraspecialCoreExponent Local.p2
  + localRadicalExponent p2
  + mathieuQuotientExponent p2
p2MonsterExponentNestedSplit = refl

p3MonsterExponentNestedSplit :
  Exponent.monsterOrderExponent Lane.p3
  ≡
  Local.extraspecialCoreExponent Local.p3
  + localRadicalExponent p3
  + mathieuQuotientExponent p3
p3MonsterExponentNestedSplit = refl

p2DuncanSwisherContinuationStopsBeforeMathieu :
  Exponent.duncanSwisherExceptionalRHS Lane.p2
  ≡
  Local.extraspecialCoreExponent Local.p2
  + localRadicalExponent p2
p2DuncanSwisherContinuationStopsBeforeMathieu = refl

p3DuncanSwisherContinuationStopsBeforeMathieu :
  Exponent.duncanSwisherExceptionalRHS Lane.p3
  ≡
  Local.extraspecialCoreExponent Local.p3
  + localRadicalExponent p3
p3DuncanSwisherContinuationStopsBeforeMathieu = refl

------------------------------------------------------------------------
-- 5. Recognition firewalls.
------------------------------------------------------------------------

data DworkInterceptIsRadicalOrderTheorem : Set where
data MonsterGapIsMathieuQuotientMechanism : Set where
data NestedSubgroupArithmeticExplainsMoonshine : Set where
data MathieuExponentCreatesSameObjectWithGeometricSectorCarrier : Set where

dworkInterceptRadicalRecognitionStillOpen :
  DworkInterceptIsRadicalOrderTheorem -> ⊥
dworkInterceptRadicalRecognitionStillOpen ()

mathieuQuotientMechanismStillOpen :
  MonsterGapIsMathieuQuotientMechanism -> ⊥
mathieuQuotientMechanismStillOpen ()

nestedSubgroupArithmeticDoesNotYetExplainMoonshine :
  NestedSubgroupArithmeticExplainsMoonshine -> ⊥
nestedSubgroupArithmeticDoesNotYetExplainMoonshine ()

mathieuExponentDoesNotCreateGeometricSameObject :
  MathieuExponentCreatesSameObjectWithGeometricSectorCarrier -> ⊥
mathieuExponentDoesNotCreateGeometricSameObject ()

------------------------------------------------------------------------
-- 6. Status.
------------------------------------------------------------------------

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record MathieuQuotientResidualBoundary : Set where
  constructor mathieu-quotient-residual-boundary
  field
    co1ContainsTwoElevenM24Sourced : Bool
    suzContainsThreeFiveM11Sourced : Bool
    m24TwoExponentTenSourced : Bool
    m11ThreeExponentTwoSourced : Bool
    co1TwentyOneSplitsElevenPlusTen : Bool
    suzSevenSplitsFivePlusTwo : Bool
    dworkInterceptsMatchRadicalExponentsNumerically : Bool
    p2MonsterGapMatchesM24Exponent : Bool
    p3MonsterGapMatchesM11Exponent : Bool
    fullMonsterExponentNestedSplitsExact : Bool
    dworkRadicalSameObjectRecognitionPaid : Bool
    mathieuQuotientCorrectionMechanismPaid : Bool
    geometricSectorSameObjectRecognitionPaid : Bool

canonicalMathieuQuotientResidualBoundary :
  MathieuQuotientResidualBoundary
canonicalMathieuQuotientResidualBoundary =
  mathieu-quotient-residual-boundary
    true true true true
    true true true true true true
    false false false
