module DASHI.Physics.YangMills.BalabanCompactSimpleOneLoopRemainderBudgetExact where

------------------------------------------------------------------------
-- ROUND79: GROUP-PARAMETRIC TOP-DOWN ASYMPTOTIC-FREEDOM BUDGET
--
-- PRIMARY SOURCES
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
-- R. Dashen and D. J. Gross,
-- "Relationship between lattice and continuum definitions of the gauge-theory
-- coupling", Physical Review D 23 (1981), 2340--2348.
-- DOI: 10.1103/PhysRevD.23.2340.
--
-- Anthony W. Knapp,
-- "Lie Groups Beyond an Introduction", second edition, Birkhauser, 2002.
-- DOI: 10.1007/978-1-4757-2453-0.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Round79's SU(2) budget is not intrinsically SU(2).  The universal scalar
-- coefficient is 11/24 and the pure-gauge colour dependence is C_A.  For every
-- compact simple group with C_A>0, define
--
--       b_G = C_A * 11/24.
--
-- If the SAME literal Wilson/FP/Haar regular remainder obeys
--
--       -R_G <= r_n <= R_G,       R_G < b_G,
--
-- then beta_n = b_G+r_n has the uniform strictly-positive lower bound
-- b_G-R_G.  This is exactly the source hypothesis needed by the existing
-- Bałaban coupling telescope; no group-by-group narrow numerical beta interval
-- is required.
--
-- The hard physical boundary remains what it should be: prove the literal
-- one-loop colour contraction is C_A times the universal scalar, prove C_A>0
-- for the compact-simple package, and enclose the actual regular remainder.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_; _/_; -_; positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanCompactSimpleCasimirOrbitFactorizationExact as Casimir

universalScalarCoefficient : ℚ
universalScalarCoefficient = + 11 / 24

universalScalarCoefficientPositive : 0ℚ < universalScalarCoefficient
universalScalarCoefficientPositive = ℚP.positive⁻¹ universalScalarCoefficient

record StrictCompactSimpleCasimirCarrier (GaugeGroup : Set) : Set₁ where
  field
    carrier : Casimir.CompactSimpleCasimirCarrier GaugeGroup
    adjointCasimirPositive : ∀ group →
      0ℚ < Casimir.adjointCasimir carrier group
open StrictCompactSimpleCasimirCarrier public

groupUniversalCoefficient :
  ∀ {GaugeGroup} → StrictCompactSimpleCasimirCarrier GaugeGroup →
  GaugeGroup → ℚ
groupUniversalCoefficient strict group =
  Casimir.adjointCasimir (carrier strict) group * universalScalarCoefficient

groupUniversalCoefficientPositive :
  ∀ {GaugeGroup}
    (strict : StrictCompactSimpleCasimirCarrier GaugeGroup) group →
  0ℚ < groupUniversalCoefficient strict group
groupUniversalCoefficientPositive strict group =
  let
    ca = Casimir.adjointCasimir (carrier strict) group
    scaled :
      universalScalarCoefficient * 0ℚ
      < universalScalarCoefficient * ca
    scaled =
      let instance scalarPositive = positive universalScalarCoefficientPositive
      in ℚP.*-monoʳ-<-pos universalScalarCoefficient
           (adjointCasimirPositive strict group)
  in
  subst₂ _<_
    (ℚRing.solve-∀ universalScalarCoefficient)
    (ℚRing.solve-∀ universalScalarCoefficient ca)
    scaled

record CompactSimpleRegularRemainderEnclosure
    {GaugeGroup : Set}
    (strict : StrictCompactSimpleCasimirCarrier GaugeGroup)
    (group : GaugeGroup)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory) : Set where
  field
    radius : ℚ
    radiusNonnegative : 0ℚ ≤ radius
    radiusBelowUniversal : radius < groupUniversalCoefficient strict group

    regularRemainder : Nat → ℚ

    betaIsUniversalPlusRegular : ∀ step →
      Flow.beta trajectory (suc step)
      ≡ groupUniversalCoefficient strict group + regularRemainder step

    regularLower : ∀ step → - radius ≤ regularRemainder step
    regularUpper : ∀ step → regularRemainder step ≤ radius

open CompactSimpleRegularRemainderEnclosure public

groupBetaLower :
  ∀ {GaugeGroup} {strict : StrictCompactSimpleCasimirCarrier GaugeGroup}
    {group trajectory} →
  CompactSimpleRegularRemainderEnclosure strict group trajectory → ℚ
groupBetaLower {strict = strict} {group = group} dataSet =
  groupUniversalCoefficient strict group - radius dataSet

groupBetaUpper :
  ∀ {GaugeGroup} {strict : StrictCompactSimpleCasimirCarrier GaugeGroup}
    {group trajectory} →
  CompactSimpleRegularRemainderEnclosure strict group trajectory → ℚ
groupBetaUpper {strict = strict} {group = group} dataSet =
  groupUniversalCoefficient strict group + radius dataSet

groupBetaLowerPositive :
  ∀ {GaugeGroup} {strict : StrictCompactSimpleCasimirCarrier GaugeGroup}
    {group trajectory}
    (dataSet : CompactSimpleRegularRemainderEnclosure strict group trajectory) →
  0ℚ < groupBetaLower dataSet
groupBetaLowerPositive {strict = strict} {group = group} dataSet =
  let
    b = groupUniversalCoefficient strict group
    r = radius dataSet
    shifted : r + (- r) < b + (- r)
    shifted = ℚP.+-mono-<-≤ (radiusBelowUniversal dataSet) ℚP.≤-refl
  in
  subst₂ _<_
    (ℚRing.solve-∀ r)
    (ℚRing.solve-∀ b r)
    shifted

groupBetaStepLower :
  ∀ {GaugeGroup} {strict : StrictCompactSimpleCasimirCarrier GaugeGroup}
    {group trajectory}
    (dataSet : CompactSimpleRegularRemainderEnclosure strict group trajectory)
    step →
  groupBetaLower dataSet ≤ Flow.beta trajectory (suc step)
groupBetaStepLower {strict = strict} {group = group} dataSet step =
  let
    b = groupUniversalCoefficient strict group
    r = radius dataSet
    shifted = ℚP.+-mono-≤ ℚP.≤-refl (regularLower dataSet step)
    normalized : b - r ≤ b + regularRemainder dataSet step
    normalized = subst
      (λ left → left ≤ b + regularRemainder dataSet step)
      (ℚRing.solve-∀ b r)
      shifted
  in
  subst
    (λ right → groupBetaLower dataSet ≤ right)
    (sym (betaIsUniversalPlusRegular dataSet step))
    normalized

groupBetaStepUpper :
  ∀ {GaugeGroup} {strict : StrictCompactSimpleCasimirCarrier GaugeGroup}
    {group trajectory}
    (dataSet : CompactSimpleRegularRemainderEnclosure strict group trajectory)
    step →
  Flow.beta trajectory (suc step) ≤ groupBetaUpper dataSet
groupBetaStepUpper dataSet step =
  subst
    (λ left → left ≤ groupBetaUpper dataSet)
    (betaIsUniversalPlusRegular dataSet step)
    (ℚP.+-mono-≤ ℚP.≤-refl (regularUpper dataSet step))

compactSimpleRemainderGivesUniformPositiveBeta :
  ∀ {GaugeGroup} {strict : StrictCompactSimpleCasimirCarrier GaugeGroup}
    {group trajectory}
    (dataSet : CompactSimpleRegularRemainderEnclosure strict group trajectory) →
  Flow.UniformBetaEnclosure trajectory
compactSimpleRemainderGivesUniformPositiveBeta dataSet = record
  { Flow.UniformBetaEnclosure.betaLower = groupBetaLower dataSet
  ; Flow.UniformBetaEnclosure.betaUpper = groupBetaUpper dataSet
  ; Flow.UniformBetaEnclosure.betaLowerNonnegative =
      ℚP.<⇒≤ (groupBetaLowerPositive dataSet)
  ; Flow.UniformBetaEnclosure.betaLowerBelow = groupBetaStepLower dataSet
  ; Flow.UniformBetaEnclosure.betaBelowUpper = groupBetaStepUpper dataSet
  }

compactSimpleTopDownBetaBudgetLevel : ProofLevel
compactSimpleTopDownBetaBudgetLevel = machineChecked

literalCompactSimpleCasimirFactorizedRemainderLevel : ProofLevel
literalCompactSimpleCasimirFactorizedRemainderLevel = conditional
