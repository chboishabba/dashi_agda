module DASHI.Physics.YangMills.BalabanTopDownOneLoopRemainderBudgetExact where

------------------------------------------------------------------------
-- ROUND79: CLAY-TOP-DOWN ONE-LOOP REMAINDER BUDGET
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
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- The literal scalar package already proves that the universal SU(2)
-- inverse-coupling logarithmic coefficient is exactly 11/12.  The four-orbit
-- Bishop calculation therefore only has to control the regular matching term.
--
-- Top-down, the weakest requirement for asymptotic freedom is simply
--
--     beta_n = 11/12 + r_n,
--     -R <= r_n <= R,
--     R < 11/12.
--
-- Then every source beta lies in the explicit uniform interval
--
--     11/12 - R <= beta_n <= 11/12 + R,
--
-- whose lower endpoint is strictly positive.  This file packages that result
-- directly as Bałaban's existing `UniformBetaEnclosure`, so no narrower
-- historical interval is mathematically required just to enter the source
-- positive-beta trajectory.
--
-- A deliberately generous concrete certificate is R=1/2, giving
--
--     5/12 <= beta_n <= 17/12.
--
-- Thus a four-orbit enclosure inside [-1/2,+1/2] would already suffice for the
-- sign/tube part of the UV construction.  Whether the actual literal regular
-- term fits this interval is analytic work, not asserted here.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _≤_; _<_; _/_; -_; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanSU2OneLoopNormalizationSanityExact as Sanity

record SU2RegularRemainderEnclosure
    (trajectory : Flow.SourceNormalizedCouplingTrajectory) : Set where
  field
    radius : ℚ
    radiusNonnegative : 0ℚ ≤ radius
    radiusBelowUniversal : radius < Sanity.su2InverseCouplingCoefficient

    regularRemainder : Nat → ℚ

    betaIsUniversalPlusRegular : ∀ step →
      Flow.beta trajectory (suc step)
      ≡ Sanity.su2InverseCouplingCoefficient + regularRemainder step

    regularLower : ∀ step → - radius ≤ regularRemainder step
    regularUpper : ∀ step → regularRemainder step ≤ radius

open import Agda.Builtin.Nat using (Nat; suc)
open SU2RegularRemainderEnclosure public

betaLowerFromRemainderRadius :
  ∀ {trajectory} → SU2RegularRemainderEnclosure trajectory → ℚ
betaLowerFromRemainderRadius dataSet =
  Sanity.su2InverseCouplingCoefficient - radius dataSet

betaUpperFromRemainderRadius :
  ∀ {trajectory} → SU2RegularRemainderEnclosure trajectory → ℚ
betaUpperFromRemainderRadius dataSet =
  Sanity.su2InverseCouplingCoefficient + radius dataSet

betaLowerStrictlyPositive :
  ∀ {trajectory} (dataSet : SU2RegularRemainderEnclosure trajectory) →
  0ℚ < betaLowerFromRemainderRadius dataSet
betaLowerStrictlyPositive dataSet =
  subst
    (λ right → 0ℚ < right)
    (ℚRing.solve-∀ Sanity.su2InverseCouplingCoefficient (radius dataSet))
    (ℚP.+-monoʳ-<
      (- radius dataSet)
      (radiusBelowUniversal dataSet))

betaStepLower :
  ∀ {trajectory} (dataSet : SU2RegularRemainderEnclosure trajectory) step →
  betaLowerFromRemainderRadius dataSet
  ≤ Flow.beta trajectory (suc step)
betaStepLower {trajectory} dataSet step =
  let
    shifted = ℚP.+-mono-≤ ℚP.≤-refl (regularLower dataSet step)
    normalized :
      Sanity.su2InverseCouplingCoefficient - radius dataSet
      ≤ Sanity.su2InverseCouplingCoefficient + regularRemainder dataSet step
    normalized = subst
      (λ left → left ≤
        Sanity.su2InverseCouplingCoefficient + regularRemainder dataSet step)
      (ℚRing.solve-∀ Sanity.su2InverseCouplingCoefficient (radius dataSet))
      shifted
  in
  subst
    (λ right → betaLowerFromRemainderRadius dataSet ≤ right)
    (sym (betaIsUniversalPlusRegular dataSet step))
    normalized

betaStepUpper :
  ∀ {trajectory} (dataSet : SU2RegularRemainderEnclosure trajectory) step →
  Flow.beta trajectory (suc step)
  ≤ betaUpperFromRemainderRadius dataSet
betaStepUpper {trajectory} dataSet step =
  let
    shifted = ℚP.+-mono-≤ ℚP.≤-refl (regularUpper dataSet step)
    normalized :
      Sanity.su2InverseCouplingCoefficient + regularRemainder dataSet step
      ≤ Sanity.su2InverseCouplingCoefficient + radius dataSet
    normalized = shifted
  in
  subst
    (λ left → left ≤ betaUpperFromRemainderRadius dataSet)
    (betaIsUniversalPlusRegular dataSet step)
    normalized

remainderEnclosureGivesUniformPositiveBeta :
  ∀ {trajectory} (dataSet : SU2RegularRemainderEnclosure trajectory) →
  Flow.UniformBetaEnclosure trajectory
remainderEnclosureGivesUniformPositiveBeta dataSet = record
  { Flow.UniformBetaEnclosure.betaLower = betaLowerFromRemainderRadius dataSet
  ; Flow.UniformBetaEnclosure.betaUpper = betaUpperFromRemainderRadius dataSet
  ; Flow.UniformBetaEnclosure.betaLowerNonnegative =
      ℚP.<⇒≤ (betaLowerStrictlyPositive dataSet)
  ; Flow.UniformBetaEnclosure.betaLowerBelow = betaStepLower dataSet
  ; Flow.UniformBetaEnclosure.betaBelowUpper = betaStepUpper dataSet
  }

------------------------------------------------------------------------
-- A wide concrete target: |regular| <= 1/2 gives beta in [5/12,17/12].
------------------------------------------------------------------------

half fiveTwelfths seventeenTwelfths : ℚ
half = + 1 / 2
fiveTwelfths = + 5 / 12
seventeenTwelfths = + 17 / 12

halfNonnegative : 0ℚ ≤ half
halfNonnegative = ℚP.nonNegative⁻¹ half

halfBelowElevenTwelfths : half < Sanity.su2InverseCouplingCoefficient
halfBelowElevenTwelfths =
  let
    instance
      positiveDifference : Positive (Sanity.su2InverseCouplingCoefficient - half)
      positiveDifference = ℚP.normalize-pos 5 12
  in
  subst
    (λ selected → half < selected)
    (sym (ℚRing.solve []))
    (ℚP.+-monoˡ-< half (ℚP.positive⁻¹ (Sanity.su2InverseCouplingCoefficient - half)))

halfRadiusLowerExact :
  Sanity.su2InverseCouplingCoefficient - half ≡ fiveTwelfths
halfRadiusLowerExact = ℚRing.solve []

halfRadiusUpperExact :
  Sanity.su2InverseCouplingCoefficient + half ≡ seventeenTwelfths
halfRadiusUpperExact = ℚRing.solve []

topDownOneLoopRemainderBudgetLevel : ProofLevel
topDownOneLoopRemainderBudgetLevel = machineChecked

-- Physical boundary: construct the SAME literal Wilson+FP+Haar scalar and prove
-- its history-dependent regular term lies in some radius R<11/12.  R=1/2 is a
-- convenient wide target, not a claim about the actual value.
literalRegularRemainderInsideAdmissibleRadiusLevel : ProofLevel
literalRegularRemainderInsideAdmissibleRadiusLevel = conditional
