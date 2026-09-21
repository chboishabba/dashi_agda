{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R429TraceEntropyBudgetRound442Exact where

------------------------------------------------------------------------
-- B / ROUND442: 8^d ROOTED-TRACE ENTROPY × 16^-d RESERVE = 2^-d
--
-- Round441 proves the literal R429 depth-d shell contains at most 8^d domains
-- once the canonical injective rooted-trace encoding is supplied.  This file
-- pays the numerical part of CMP116 (1.26)--(1.28):
--
--       |S_d| <= 8^d
--       residual_d <= 16^-d
--       --------------------------------
--       |S_d| residual_d <= 2^-d.
--
-- The finite geometric sum is therefore uniformly bounded.  No source-specific
-- Yang--Mills estimate appears below; the remaining physical input is only the
-- R429 rooted-trace encoding plus the source statement that enough tree decay
-- can be reserved to dominate 16^-d.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Integer.Base using (+_)
import Data.List.Base as List using (length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _/_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Trace
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanYM4ROperationEntropyShellExact as Shell
import DASHI.Physics.YangMills.BalabanCMP116R429RootedTraceCountingRound441Exact as R441
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalFourStageR406Round429Exact as R429

eightQ oneSixteenth : ℚ
eightQ = + 8 / 1
oneSixteenth = + 1 / 16

rationalPower : ℚ → Nat → ℚ
rationalPower base zero = 1ℚ
rationalPower base (suc depth) =
  base * rationalPower base depth

oneSixteenthPower : Nat → ℚ
oneSixteenthPower = rationalPower oneSixteenth

------------------------------------------------------------------------
-- Nat -> rational arithmetic for the exact word count.
------------------------------------------------------------------------

oneNonnegative : 0ℚ ≤ 1ℚ
oneNonnegative = ℚP.0≤∣p∣ 1ℚ

natAsRationalNonnegative : ∀ n → 0ℚ ≤ Shell.natAsRational n
natAsRationalNonnegative zero = ℚP.≤-refl
natAsRationalNonnegative (suc n) =
  ℚP.+-mono-≤ oneNonnegative (natAsRationalNonnegative n)

natAsRationalAdd : ∀ m n →
  Shell.natAsRational (m + n)
  ≡ Shell.natAsRational m + Shell.natAsRational n
natAsRationalAdd zero n =
  sym (ℚP.+-identityˡ (Shell.natAsRational n))
natAsRationalAdd (suc m) n
  rewrite natAsRationalAdd m n =
  ℚRing.solve-∀ (Shell.natAsRational m) (Shell.natAsRational n)

natAsRationalMul : ∀ m n →
  Shell.natAsRational (m * n)
  ≡ Shell.natAsRational m * Shell.natAsRational n
natAsRationalMul zero n =
  sym (ℚP.*-zeroˡ (Shell.natAsRational n))
natAsRationalMul (suc m) n
  rewrite natAsRationalAdd n (m * n)
        | natAsRationalMul m n =
  ℚRing.solve-∀ (Shell.natAsRational m) (Shell.natAsRational n)

natAsRationalMonotone :
  ∀ {left right} →
  left ≤ right →
  Shell.natAsRational left ≤ Shell.natAsRational right
natAsRationalMonotone {zero} {right} z≤n =
  natAsRationalNonnegative right
natAsRationalMonotone {suc left} {suc right} (s≤s order) =
  ℚP.+-mono-≤ ℚP.≤-refl (natAsRationalMonotone order)

natAsRationalEight : Shell.natAsRational Trace.eight ≡ eightQ
natAsRationalEight = ℚRing.solve []

natAsRationalPow8 : ∀ depth →
  Shell.natAsRational (Trace.pow8 depth)
  ≡ rationalPower eightQ depth
natAsRationalPow8 zero = ℚRing.solve []
natAsRationalPow8 (suc depth)
  rewrite natAsRationalMul Trace.eight (Trace.pow8 depth)
        | natAsRationalEight
        | natAsRationalPow8 depth =
  refl

------------------------------------------------------------------------
-- Exact entropy/suppression identity.
------------------------------------------------------------------------

eightTimesOneSixteenthIsHalf :
  eightQ * oneSixteenth ≡ Geo.half
eightTimesOneSixteenthIsHalf = ℚRing.solve []

eightPowerTimesSixteenthPowerIsHalfPower : ∀ depth →
  rationalPower eightQ depth * oneSixteenthPower depth
  ≡ Geo.halfPower depth
eightPowerTimesSixteenthPowerIsHalfPower zero =
  ℚRing.solve []
eightPowerTimesSixteenthPowerIsHalfPower (suc depth) =
  let
    regroup :
      (eightQ * rationalPower eightQ depth)
        * (oneSixteenth * oneSixteenthPower depth)
      ≡
      Geo.half
        * (rationalPower eightQ depth * oneSixteenthPower depth)
    regroup =
      subst
        (λ coefficient →
          (eightQ * rationalPower eightQ depth)
            * (oneSixteenth * oneSixteenthPower depth)
          ≡
          coefficient
            * (rationalPower eightQ depth * oneSixteenthPower depth))
        eightTimesOneSixteenthIsHalf
        (ℚRing.solve-∀
          (rationalPower eightQ depth)
          (oneSixteenthPower depth))
  in
  trans regroup
    (cong
      (Geo.half *_)
      (eightPowerTimesSixteenthPowerIsHalfPower depth))

oneSixteenthNonnegative : 0ℚ ≤ oneSixteenth
oneSixteenthNonnegative =
  let
    instance
      oneSixteenthNN : NonNegative oneSixteenth
      oneSixteenthNN = ℚP.normalize-nonNeg 1 16
  in
  ℚP.nonNegative⁻¹ oneSixteenth

oneSixteenthPowerNonnegative : ∀ depth →
  0ℚ ≤ oneSixteenthPower depth
oneSixteenthPowerNonnegative zero = oneNonnegative
oneSixteenthPowerNonnegative (suc depth) =
  let
    instance
      baseNN : NonNegative oneSixteenth
      baseNN = nonNegative oneSixteenthNonnegative
      tailNN : NonNegative (oneSixteenthPower depth)
      tailNN = nonNegative (oneSixteenthPowerNonnegative depth)
  in
  ℚP.nonNegative⁻¹
    (oneSixteenth * oneSixteenthPower depth)

record R429TraceEntropyReserve
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base}
    {domainTreeDistance : R429.Domain fourStage → Nat}
    (encoding :
      R441.R429RootedTraceShellEncoding
        fourStage domainTreeDistance)
    : Set₁ where
  field
    residualEntropyWeight : Nat → ℚ
    residualEntropyWeightNonnegative :
      ∀ depth → 0ℚ ≤ residualEntropyWeight depth

    sourceDecayReservesOneSixteenthPerTraceStep :
      ∀ depth →
      residualEntropyWeight depth
      ≤ oneSixteenthPower depth

open R429TraceEntropyReserve public

shellEntropyPaymentBelowHalfPower :
  ∀ {Measure TestObservable dataSet extension base fourStage domainTreeDistance}
    {encoding :
      R441.R429RootedTraceShellEncoding
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage domainTreeDistance}
    (reserve : R429TraceEntropyReserve encoding)
    depth →
  Shell.natAsRational
      (List.length (R441.domainsAtDepth encoding depth))
    * residualEntropyWeight reserve depth
  ≤ Geo.halfPower depth
shellEntropyPaymentBelowHalfPower {encoding = encoding} reserve depth =
  let
    countNatBound =
      R441.domainShellCardinalityBelowEightPower encoding depth

    countBound0 :
      Shell.natAsRational
        (List.length (R441.domainsAtDepth encoding depth))
      ≤
      Shell.natAsRational (Trace.pow8 depth)
    countBound0 = natAsRationalMonotone countNatBound

    countBound :
      Shell.natAsRational
        (List.length (R441.domainsAtDepth encoding depth))
      ≤ rationalPower eightQ depth
    countBound =
      subst
        (λ upper →
          Shell.natAsRational
            (List.length (R441.domainsAtDepth encoding depth))
          ≤ upper)
        (natAsRationalPow8 depth)
        countBound0

    productBound :
      Shell.natAsRational
          (List.length (R441.domainsAtDepth encoding depth))
        * residualEntropyWeight reserve depth
      ≤
      rationalPower eightQ depth * oneSixteenthPower depth
    productBound =
      ℚP.*-mono-≤
        (natAsRationalNonnegative
          (List.length (R441.domainsAtDepth encoding depth)))
        countBound
        (residualEntropyWeightNonnegative reserve depth)
        (sourceDecayReservesOneSixteenthPerTraceStep reserve depth)
  in
  subst
    (λ upper →
      Shell.natAsRational
          (List.length (R441.domainsAtDepth encoding depth))
        * residualEntropyWeight reserve depth
      ≤ upper)
    (eightPowerTimesSixteenthPowerIsHalfPower depth)
    productBound

round442EightOverSixteenArithmeticLevel : ProofLevel
round442EightOverSixteenArithmeticLevel = machineChecked

round442R429ShellEntropyBudgetCompilerLevel : ProofLevel
round442R429ShellEntropyBudgetCompilerLevel = machineChecked

-- Remaining B3b source content is now:
--   * inhabit R441's canonical R429 trace/depth partition;
--   * prove the source tree decay can reserve at least 16^-d on this trace.
-- The shell entropy payment itself is theorem output.
literalRound442SourceDecayReserveLevel : ProofLevel
literalRound442SourceDecayReserveLevel = conditional
