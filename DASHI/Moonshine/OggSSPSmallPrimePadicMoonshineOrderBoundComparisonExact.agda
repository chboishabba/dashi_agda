module DASHI.Moonshine.OggSSPSmallPrimePadicMoonshineOrderBoundComparisonExact where

------------------------------------------------------------------------
-- CMT p-ADIC MOONSHINE ORDER-BOUND COMPARISON AT p=2,3
--
-- EXTERNAL SOURCE
--
-- Chen--Marks--Tyler, Proposition 5.2 (conditional on their Conjecture 4.2):
-- if G has p-adic moonshine, then the q-adic valuation of |G| is bounded by
-- the table entry r.  On the diagonal q=p:
--
--     p=2 : v_2(|G|) <= 46
--     p=3 : v_3(|G|) <= 21.
--
-- These are GROUP-ORDER UPPER BOUNDS derived from integrality of the trivial
-- character multiplicity across the candidate p-adically annihilated
-- Hauptmodul set.  They are NOT fourth-term local valuations.
--
-- DASHI COMPARISON
--
-- Monster exponents:
--     v_2(|M|)=46, v_3(|M|)=20.
--
-- Duncan--Swisher exceptional three-term baselines:
--     p=2 : 36
--     p=3 : 18.
--
-- Hence:
--     p=2 : 46 = 36 + 10  (exactly the Monster-local residual)
--     p=3 : 21 = 18 + 3, while 20 = 18 + 2.
--
-- This is a high-value asymmetry:
--   * at p=2 the CMT diagonal bound numerically saturates the Monster exponent
--     and its excess over the Duncan--Swisher baseline is exactly ten;
--   * at p=3 the same construction overshoots the Monster exponent by one.
--
-- No theorem below promotes the conditional CMT bound to a Monster valuation
-- theorem, or identifies its p=2 excess with the local fourth-term mechanism.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Moonshine.OggSSPSmallPrimeMonsterLocalCentralizerValuationExact as Local
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source attribution.
------------------------------------------------------------------------

chenMarksTyler : Source.AttributedSource
chenMarksTyler =
  Source.mkDOISource
    "Ryan C. Chen, Samuel Marks, and Matthew Tyler"
    "p-adic Properties of Hauptmoduln with Applications to Moonshine"
    "SIGMA 15 (2019), 033"
    "2019"
    "10.3842/SIGMA.2019.033"
    "https://doi.org/10.3842/SIGMA.2019.033"
    Source.academicArticleSource
    "Proposition 5.2, assuming Conjecture 4.2, gives group-order valuation upper bounds for groups with p-adic moonshine; diagonal entries are 46 at p=q=2 and 21 at p=q=3. Used only as a conditional analytic envelope, not as a Monster-local fourth-term theorem"
    Source.publicAttribution

cmtOrderBoundAtlas : Source.AttributedSourceAtlas
cmtOrderBoundAtlas =
  Source.mkSourceAtlas
    "CMT p-adic moonshine diagonal order-bound comparison"
    "DASHI.Moonshine.OggSSPSmallPrimePadicMoonshineOrderBoundComparisonExact"
    (chenMarksTyler ∷ [])
    "Chen--Marks--Tyler own the conditional p-adic moonshine order bounds; DASHI owns the comparison with Monster exponents, Duncan--Swisher baselines, and the independent 10/2 residuals"

------------------------------------------------------------------------
-- 2. Exact sourced diagonal table entries.
------------------------------------------------------------------------

data SmallPrime : Set where
  pTwo pThree : SmallPrime

cmtDiagonalOrderBound :
  SmallPrime ->
  Nat
cmtDiagonalOrderBound pTwo = 46
cmtDiagonalOrderBound pThree = 21

cmtP2DiagonalBoundIsFortySix :
  cmtDiagonalOrderBound pTwo ≡ 46
cmtP2DiagonalBoundIsFortySix = refl

cmtP3DiagonalBoundIsTwentyOne :
  cmtDiagonalOrderBound pThree ≡ 21
cmtP3DiagonalBoundIsTwentyOne = refl

------------------------------------------------------------------------
-- 3. Independent Monster / Duncan--Swisher coordinates.
------------------------------------------------------------------------

monsterExponent :
  SmallPrime ->
  Nat
monsterExponent pTwo =
  Exponent.monsterOrderExponent Lane.p2
monsterExponent pThree =
  Exponent.monsterOrderExponent Lane.p3

duncanSwisherBaseline :
  SmallPrime ->
  Nat
duncanSwisherBaseline pTwo =
  Exponent.duncanSwisherExceptionalRHS Lane.p2
duncanSwisherBaseline pThree =
  Exponent.duncanSwisherExceptionalRHS Lane.p3

monsterLocalResidual :
  SmallPrime ->
  Nat
monsterLocalResidual pTwo =
  Local.p2LocalCentralizerResidual
monsterLocalResidual pThree =
  Local.p3LocalCentralizerResidual

p2MonsterExponentIsFortySix :
  monsterExponent pTwo ≡ 46
p2MonsterExponentIsFortySix = refl

p3MonsterExponentIsTwenty :
  monsterExponent pThree ≡ 20
p3MonsterExponentIsTwenty = refl

p2BaselineIsThirtySix :
  duncanSwisherBaseline pTwo ≡ 36
p2BaselineIsThirtySix = refl

p3BaselineIsEighteen :
  duncanSwisherBaseline pThree ≡ 18
p3BaselineIsEighteen = refl

------------------------------------------------------------------------
-- 4. p=2: exact numerical saturation.
------------------------------------------------------------------------

p2CMTBoundNumericallyEqualsMonsterExponent :
  cmtDiagonalOrderBound pTwo
  ≡ monsterExponent pTwo
p2CMTBoundNumericallyEqualsMonsterExponent = refl

p2CMTBoundSplitsAsBaselinePlusLocalResidual :
  cmtDiagonalOrderBound pTwo
  ≡ duncanSwisherBaseline pTwo + monsterLocalResidual pTwo
p2CMTBoundSplitsAsBaselinePlusLocalResidual = refl

------------------------------------------------------------------------
-- 5. p=3: exact one-unit overshoot.
------------------------------------------------------------------------

p3CMTBoundIsMonsterExponentPlusOne :
  cmtDiagonalOrderBound pThree
  ≡ monsterExponent pThree + 1
p3CMTBoundIsMonsterExponentPlusOne = refl

p3CMTBoundIsBaselinePlusThree :
  cmtDiagonalOrderBound pThree
  ≡ duncanSwisherBaseline pThree + 3
p3CMTBoundIsBaselinePlusThree = refl

p3CMTBoundIsNotBaselinePlusLocalResidual :
  cmtDiagonalOrderBound pThree
  ≡ duncanSwisherBaseline pThree + monsterLocalResidual pThree
  ->
  ⊥
p3CMTBoundIsNotBaselinePlusLocalResidual ()

------------------------------------------------------------------------
-- 6. Attribution / applicability firewalls.
------------------------------------------------------------------------

data CMTConjecture42DischargedHere : Set where
data MonsterProvedToHaveCMTTwoAdicMoonshineHere : Set where
data MonsterProvedToHaveCMTThreeAdicMoonshineHere : Set where
data P2NumericalSaturationProvesFourthTermMechanism : Set where
data P3OneUnitOvershootMayBeRemovedByTargetFitting : Set where
data CMTDiagonalBoundIsLocalExceptionalValuation : Set where

cmtConjecture42NotDischargedHere :
  CMTConjecture42DischargedHere -> ⊥
cmtConjecture42NotDischargedHere ()

monsterTwoAdicApplicabilityNotProvedHere :
  MonsterProvedToHaveCMTTwoAdicMoonshineHere -> ⊥
monsterTwoAdicApplicabilityNotProvedHere ()

monsterThreeAdicApplicabilityNotProvedHere :
  MonsterProvedToHaveCMTThreeAdicMoonshineHere -> ⊥
monsterThreeAdicApplicabilityNotProvedHere ()

p2SaturationDoesNotProveFourthTermMechanism :
  P2NumericalSaturationProvesFourthTermMechanism -> ⊥
p2SaturationDoesNotProveFourthTermMechanism ()

p3OvershootCannotBeRemovedByTargetFitting :
  P3OneUnitOvershootMayBeRemovedByTargetFitting -> ⊥
p3OvershootCannotBeRemovedByTargetFitting ()

cmtOrderBoundIsNotPromotedToLocalExceptionalValuation :
  CMTDiagonalBoundIsLocalExceptionalValuation -> ⊥
cmtOrderBoundIsNotPromotedToLocalExceptionalValuation ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record PadicMoonshineOrderBoundComparisonBoundary : Set where
  constructor padic-moonshine-order-bound-comparison-boundary
  field
    cmtProposition52Sourced : Bool
    cmtConjecture42ConditionalityRecorded : Bool
    p2DiagonalBoundFortySixSourced : Bool
    p3DiagonalBoundTwentyOneSourced : Bool
    p2BoundNumericallySaturatesMonster : Bool
    p2BoundExcessOverBaselineIsTen : Bool
    p3BoundOvershootsMonsterByOne : Bool
    p3BoundExcessOverBaselineIsThree : Bool
    p3BoundExcessEqualsMonsterResidualTwo : Bool
    cmtBoundPromotedToFourthTermValuation : Bool
    monsterPadicMoonshineApplicabilityProvedHere : Bool
    attributionFirewallPreserved : Bool

canonicalPadicMoonshineOrderBoundComparisonBoundary :
  PadicMoonshineOrderBoundComparisonBoundary
canonicalPadicMoonshineOrderBoundComparisonBoundary =
  padic-moonshine-order-bound-comparison-boundary
    true true true true true true true true false false false true
