module DASHI.Physics.YangMills.BalabanP33RelaxedRadiusQuaternionL1DefectExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Turn the repository's literal relaxed radius
--
--       N(q) <= 4 rho^2,    rho = 1/8192,
--
-- for the quaternion defect q = U^{-1}-1 into a square-root-free component
-- estimate.  Since every coordinate square is bounded by N(q), each absolute
-- coordinate is at most 2 rho = 1/4096.  Therefore
--
--       |q0|+|q1|+|q2|+|q3| <= 1/1024.
--
-- This gives a rational upper bound on the SU(2) matrix operator defect because
-- the operator norm of the corresponding 2x2 quaternion matrix is bounded by
-- its Euclidean norm and hence by its coordinate l1 norm.  The latter final
-- representation identification is kept separate; all radius arithmetic here
-- is on the literal physical rational quaternion.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; ∣_∣; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanStrongCouplingLiteralQuaternionScalarBudgetExact as Strong

componentBudget quaternionL1Budget : ℚ
componentBudget = + 1 / 4096
quaternionL1Budget = + 1 / 1024

componentBudgetSquareIsRelaxedRadius :
  componentBudget * componentBudget ≡ Relaxed.fourRhoSquare
componentBudgetSquareIsRelaxedRadius = ℚRing.solve []

q1SquareBelowNormSq : ∀ q0 q1 q2 q3 →
  q1 * q1 ≤ Norm.normSq (Q.quat q0 q1 q2 q3)
q1SquareBelowNormSq q0 q1 q2 q3 =
  let
    others : 0ℚ ≤ q0 * q0 + q2 * q2 + q3 * q3
    others = FiniteL2.addNonnegative
      (FiniteL2.addNonnegative
        (FiniteL2.squareNonnegative q0)
        (FiniteL2.squareNonnegative q2))
      (FiniteL2.squareNonnegative q3)
    raw : q1 * q1 ≤ q1 * q1 + (q0 * q0 + q2 * q2 + q3 * q3)
    raw = subst
      (λ lower → lower ≤ q1 * q1 + (q0 * q0 + q2 * q2 + q3 * q3))
      (ℚP.+-identityʳ (q1 * q1))
      (ℚP.+-monoʳ-≤ (q1 * q1) others)
  in
  subst
    (λ upper → q1 * q1 ≤ upper)
    (ℚRing.solve-∀ q0 q1 q2 q3)
    raw

q2SquareBelowNormSq : ∀ q0 q1 q2 q3 →
  q2 * q2 ≤ Norm.normSq (Q.quat q0 q1 q2 q3)
q2SquareBelowNormSq q0 q1 q2 q3 =
  let
    others : 0ℚ ≤ q0 * q0 + q1 * q1 + q3 * q3
    others = FiniteL2.addNonnegative
      (FiniteL2.addNonnegative
        (FiniteL2.squareNonnegative q0)
        (FiniteL2.squareNonnegative q1))
      (FiniteL2.squareNonnegative q3)
    raw : q2 * q2 ≤ q2 * q2 + (q0 * q0 + q1 * q1 + q3 * q3)
    raw = subst
      (λ lower → lower ≤ q2 * q2 + (q0 * q0 + q1 * q1 + q3 * q3))
      (ℚP.+-identityʳ (q2 * q2))
      (ℚP.+-monoʳ-≤ (q2 * q2) others)
  in
  subst
    (λ upper → q2 * q2 ≤ upper)
    (ℚRing.solve-∀ q0 q1 q2 q3)
    raw

q3SquareBelowNormSq : ∀ q0 q1 q2 q3 →
  q3 * q3 ≤ Norm.normSq (Q.quat q0 q1 q2 q3)
q3SquareBelowNormSq q0 q1 q2 q3 =
  let
    others : 0ℚ ≤ q0 * q0 + q1 * q1 + q2 * q2
    others = FiniteL2.addNonnegative
      (FiniteL2.addNonnegative
        (FiniteL2.squareNonnegative q0)
        (FiniteL2.squareNonnegative q1))
      (FiniteL2.squareNonnegative q2)
    raw : q3 * q3 ≤ q3 * q3 + (q0 * q0 + q1 * q1 + q2 * q2)
    raw = subst
      (λ lower → lower ≤ q3 * q3 + (q0 * q0 + q1 * q1 + q2 * q2))
      (ℚP.+-identityʳ (q3 * q3))
      (ℚP.+-monoʳ-≤ (q3 * q3) others)
  in
  subst
    (λ upper → q3 * q3 ≤ upper)
    (ℚRing.solve-∀ q0 q1 q2 q3)
    raw

absoluteComponentBelowBudget :
  ∀ component normSquare →
  component * component ≤ normSquare →
  normSquare ≤ Relaxed.fourRhoSquare →
  ∣ component ∣ ≤ componentBudget
absoluteComponentBelowBudget component normSquare componentBelow radius =
  let
    absSquare : ∣ component ∣ * ∣ component ∣ ≡ component * component
    absSquare = Schur.absoluteSquareExact component

    squareBound :
      ∣ component ∣ * ∣ component ∣
      ≤ componentBudget * componentBudget
    squareBound =
      subst
        (λ lower → lower ≤ componentBudget * componentBudget)
        (sym absSquare)
        (subst
          (λ upper → component * component ≤ upper)
          (sym componentBudgetSquareIsRelaxedRadius)
          (ℚP.≤-trans componentBelow radius))
  in
  Strong.nonnegativeSquareReflectsOrder
    ∣ component ∣ componentBudget
    (ℚP.0≤∣p∣ component)
    (ℚP.nonNegative⁻¹ componentBudget)
    squareBound

quaternionDefectL1 : Q.RationalQuaternion → ℚ
quaternionDefectL1 (Q.quat q0 q1 q2 q3) =
  ∣ q0 ∣ + ∣ q1 ∣ + ∣ q2 ∣ + ∣ q3 ∣

relaxedNormSqImpliesQuaternionL1Budget :
  ∀ value →
  Norm.normSq value ≤ Relaxed.fourRhoSquare →
  quaternionDefectL1 value ≤ quaternionL1Budget
relaxedNormSqImpliesQuaternionL1Budget
    value@(Q.quat q0 q1 q2 q3) radius =
  let
    b0 = absoluteComponentBelowBudget
      q0 (Norm.normSq value)
      (Norm.scalarPartSquareBelowNormSq value) radius
    b1 = absoluteComponentBelowBudget
      q1 (Norm.normSq value)
      (q1SquareBelowNormSq q0 q1 q2 q3) radius
    b2 = absoluteComponentBelowBudget
      q2 (Norm.normSq value)
      (q2SquareBelowNormSq q0 q1 q2 q3) radius
    b3 = absoluteComponentBelowBudget
      q3 (Norm.normSq value)
      (q3SquareBelowNormSq q0 q1 q2 q3) radius
    all = ℚP.+-mono-≤
      (ℚP.+-mono-≤ (ℚP.+-mono-≤ b0 b1) b2) b3
  in
  subst
    (λ upper → quaternionDefectL1 value ≤ upper)
    (ℚRing.solve [] :
      componentBudget + componentBudget + componentBudget + componentBudget
      ≡ quaternionL1Budget)
    all

p33RelaxedRadiusComponentBoundLevel : ProofLevel
p33RelaxedRadiusComponentBoundLevel = machineChecked

p33RelaxedRadiusQuaternionL1DefectLevel : ProofLevel
p33RelaxedRadiusQuaternionL1DefectLevel = machineChecked
