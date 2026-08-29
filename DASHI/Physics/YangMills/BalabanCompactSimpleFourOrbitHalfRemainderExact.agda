module DASHI.Physics.YangMills.BalabanCompactSimpleFourOrbitHalfRemainderExact where

------------------------------------------------------------------------
-- ROUND86: FOUR JOINT LITERAL ORBIT ENCLOSURES -> ALL-GROUP POSITIVE BETA
--
-- PRIMARY / METHOD SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud,
-- "Introduction to Interval Analysis", SIAM, 2009.
-- DOI: 10.1137/1.9780898717716.
--
-- David J. Gross and Frank Wilczek,
-- "Ultraviolet Behavior of Non-Abelian Gauge Theories",
-- Physical Review Letters 30 (1973), 1343--1346.
-- DOI: 10.1103/PhysRevLett.30.1343.
--
-- H. David Politzer,
-- "Reliable Perturbative Results for Strong Interactions?",
-- Physical Review Letters 30 (1973), 1346--1349.
-- DOI: 10.1103/PhysRevLett.30.1346.
--
-- MATHEMATICAL ROLE
--
-- Existing code proves that the literal regular Brillouin contribution is the
-- sum of four JOINT hypercubic orbit sums.  Round85 proves every classified
-- compact-simple universal coefficient is at least 11/12.  Therefore we can
-- choose the deliberately wide common radius 1/2 and compile the four physical
-- interval evaluations directly into the existing group-parametric beta theorem.
--
-- For each RG step it is enough to certify
--
--   l_i <= S_i <= u_i,  i=1..4,
--   -1/2 <= l_1+l_2+l_3+l_4,
--    u_1+u_2+u_3+u_4 <= 1/2,
--
-- for the SAME literal evaluator.  Finite ordered-ring algebra then yields
--
--   |S_1+S_2+S_3+S_4| <= 1/2 < 11/12 <= C_A(G) 11/24,
--
-- and constructs Bałaban's `UniformBetaEnclosure` for every classified simple
-- Lie type.  Thus no aggregation/margin theorem remains after the four joint
-- physical interval enclosures.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _≤_; -_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanCompactSimpleOneLoopRemainderBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanCompactSimpleUniversalBetaFloorExact as Universal
import DASHI.Physics.YangMills.CompactSimpleClassificationAdjointCasimirExact as Classified
import DASHI.Physics.YangMills.CompactSimpleClassification as Class
import DASHI.Physics.YangMills.BalabanTopDownOneLoopRemainderBudgetExact as SU2Budget

record FourOrbitStepEnclosure : Set₁ where
  field
    orbit1 orbit2 orbit3 orbit4 : ℚ
    lower1 lower2 lower3 lower4 : ℚ
    upper1 upper2 upper3 upper4 : ℚ

    lower1Valid : lower1 ≤ orbit1
    lower2Valid : lower2 ≤ orbit2
    lower3Valid : lower3 ≤ orbit3
    lower4Valid : lower4 ≤ orbit4

    upper1Valid : orbit1 ≤ upper1
    upper2Valid : orbit2 ≤ upper2
    upper3Valid : orbit3 ≤ upper3
    upper4Valid : orbit4 ≤ upper4

    totalLowerInsideHalf :
      - SU2Budget.half ≤ lower1 + lower2 + lower3 + lower4
    totalUpperInsideHalf :
      upper1 + upper2 + upper3 + upper4 ≤ SU2Budget.half

open FourOrbitStepEnclosure public

orbitTotal : FourOrbitStepEnclosure → ℚ
orbitTotal dataSet =
  orbit1 dataSet + orbit2 dataSet + orbit3 dataSet + orbit4 dataSet

fourLowerBoundsAdd :
  (dataSet : FourOrbitStepEnclosure) →
  lower1 dataSet + lower2 dataSet + lower3 dataSet + lower4 dataSet
  ≤ orbitTotal dataSet
fourLowerBoundsAdd dataSet =
  ℚP.+-mono-≤
    (ℚP.+-mono-≤
      (ℚP.+-mono-≤ (lower1Valid dataSet) (lower2Valid dataSet))
      (lower3Valid dataSet))
    (lower4Valid dataSet)

fourUpperBoundsAdd :
  (dataSet : FourOrbitStepEnclosure) →
  orbitTotal dataSet
  ≤ upper1 dataSet + upper2 dataSet + upper3 dataSet + upper4 dataSet
fourUpperBoundsAdd dataSet =
  ℚP.+-mono-≤
    (ℚP.+-mono-≤
      (ℚP.+-mono-≤ (upper1Valid dataSet) (upper2Valid dataSet))
      (upper3Valid dataSet))
    (upper4Valid dataSet)

orbitTotalLowerHalf :
  (dataSet : FourOrbitStepEnclosure) →
  - SU2Budget.half ≤ orbitTotal dataSet
orbitTotalLowerHalf dataSet =
  ℚP.≤-trans
    (totalLowerInsideHalf dataSet)
    (fourLowerBoundsAdd dataSet)

orbitTotalUpperHalf :
  (dataSet : FourOrbitStepEnclosure) →
  orbitTotal dataSet ≤ SU2Budget.half
orbitTotalUpperHalf dataSet =
  ℚP.≤-trans
    (fourUpperBoundsAdd dataSet)
    (totalUpperInsideHalf dataSet)

record LiteralFourOrbitBetaTrajectory
    (trajectory : Flow.SourceNormalizedCouplingTrajectory) : Set₁ where
  field
    stepOrbitEnclosure : Nat → FourOrbitStepEnclosure
    betaIsUniversalPlusFourOrbitRegular : ∀ step →
      Flow.beta trajectory (suc step)
      ≡ Budget.universalScalarCoefficient
          * Classified.classificationAdjointCasimir Class.su2Type
        + orbitTotal (stepOrbitEnclosure step)

open LiteralFourOrbitBetaTrajectory public

record ClassifiedGroupFourOrbitBetaTrajectory
    (lieType : Class.SimpleLieType)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory) : Set₁ where
  field
    stepOrbitEnclosure : Nat → FourOrbitStepEnclosure
    betaIsGroupUniversalPlusRegular : ∀ step →
      Flow.beta trajectory (suc step)
      ≡ Budget.groupUniversalCoefficient
          Classified.classificationStrictCasimirCarrier lieType
        + orbitTotal (stepOrbitEnclosure step)

open ClassifiedGroupFourOrbitBetaTrajectory public

fourOrbitHalfRemainderEnclosure :
  ∀ {lieType trajectory} →
  ClassifiedGroupFourOrbitBetaTrajectory lieType trajectory →
  Budget.CompactSimpleRegularRemainderEnclosure
    Classified.classificationStrictCasimirCarrier lieType trajectory
fourOrbitHalfRemainderEnclosure {lieType = lieType} dataSet = record
  { Budget.CompactSimpleRegularRemainderEnclosure.radius = SU2Budget.half
  ; Budget.CompactSimpleRegularRemainderEnclosure.radiusNonnegative =
      SU2Budget.halfNonnegative
  ; Budget.CompactSimpleRegularRemainderEnclosure.radiusBelowUniversal =
      Universal.uniformRemainderBelowEveryCompactSimpleCoefficient
        SU2Budget.half lieType SU2Budget.halfBelowElevenTwelfths
  ; Budget.CompactSimpleRegularRemainderEnclosure.regularRemainder =
      λ step → orbitTotal (stepOrbitEnclosure dataSet step)
  ; Budget.CompactSimpleRegularRemainderEnclosure.betaIsUniversalPlusRegular =
      betaIsGroupUniversalPlusRegular dataSet
  ; Budget.CompactSimpleRegularRemainderEnclosure.regularLower =
      λ step → orbitTotalLowerHalf (stepOrbitEnclosure dataSet step)
  ; Budget.CompactSimpleRegularRemainderEnclosure.regularUpper =
      λ step → orbitTotalUpperHalf (stepOrbitEnclosure dataSet step)
  }

fourLiteralOrbitEnclosuresGiveUniformPositiveBeta :
  ∀ {lieType trajectory} →
  ClassifiedGroupFourOrbitBetaTrajectory lieType trajectory →
  Flow.UniformBetaEnclosure trajectory
fourLiteralOrbitEnclosuresGiveUniformPositiveBeta dataSet =
  Budget.compactSimpleRemainderGivesUniformPositiveBeta
    (fourOrbitHalfRemainderEnclosure dataSet)

fourOrbitIntervalAggregationLevel : ProofLevel
fourOrbitIntervalAggregationLevel = machineChecked

fourOrbitHalfToAllGroupPositiveBetaLevel : ProofLevel
fourOrbitHalfToAllGroupPositiveBetaLevel = machineChecked

-- Remaining literal L1 work after this theorem:
--
--   (a) construct the SAME Wilson + reduced-FP + Haar Ward scalar/evaluator;
--   (b) prove its colour factorization gives C_A times the universal scalar;
--   (c) rigorously evaluate the FOUR JOINT regular orbit sums so their total
--       interval lies inside [-1/2,1/2].
--
-- There is no fifth finite aggregation/margin lemma after those evaluations.
physicalLiteralFourJointOrbitHalfEnclosuresLevel : ProofLevel
physicalLiteralFourJointOrbitHalfEnclosuresLevel = conditional
