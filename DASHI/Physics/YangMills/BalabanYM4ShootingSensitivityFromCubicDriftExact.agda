module DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact where

------------------------------------------------------------------------
-- ROW A, CONTRACTION GATE:
--   UNIFORM COUPLING-DERIVATIVE BOUND + CUBIC DRIFT TELESCOPE
--   ==> CUMULATIVE SHOOTING SENSITIVITY q < 1 (cutoff-independent)
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I.", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- In u = g^{-2}, |dg/du| = g^3/2.  Hence a uniform coupling derivative
-- |d beta_j/dg| <= L gives shell sensitivity <= (L/2)g_j^3.  The cubic
-- telescope supplies b_* sum g_j^3 <= 2 gamma uniformly in the cutoff, so
-- cumulative sensitivity <= L gamma / b_*.  Therefore L gamma < b_* gives
-- a strict shooting contraction for every finite cutoff.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; 1ℚ; ∣_∣; _+_; _*_; -_; _-_; _/_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)
open import Relation.Nullary.Decidable using (toWitness)

import DASHI.Physics.YangMills.BalabanYM4CubicCouplingDriftTelescopeExact as Cubic
open Cubic using
  (twoℚ; halfℚ; sumCubes; mul-nonNeg; scaleˡ-nonNeg; transport-≤)

open +-*-Solver

sum₀ : (Nat → ℚ) → Nat → ℚ
sum₀ f zero = 0ℚ
sum₀ f (suc n) = sum₀ f n + f n

shootingDifference :
  ∀ (target x y : ℚ) → (target + x) - (target + y) ≡ x - y
shootingDifference target x y =
  solve 3 (λ t p q → (t :+ p) :- (t :+ q) := p :- q) refl target x y

shootingContraction :
  ∀ {q : ℚ} (target : ℚ) (history : ℚ → ℚ) →
  (∀ u v → ∣ history u - history v ∣ ≤ q * ∣ u - v ∣) →
  ∀ u v → ∣ (target + history u) - (target + history v) ∣ ≤ q * ∣ u - v ∣
shootingContraction {q} target history lipschitz u v =
  subst (λ z → ∣ z ∣ ≤ q * ∣ u - v ∣)
    (sym (shootingDifference target (history u) (history v)))
    (lipschitz u v)

sum-mono : ∀ {f h} → (∀ j → f j ≤ h j) → ∀ K → sum₀ f K ≤ sum₀ h K
sum-mono termwise zero = ℚP.≤-refl
sum-mono termwise (suc n) = ℚP.+-mono-≤ (sum-mono termwise n) (termwise n)

sum-scale : ∀ (c : ℚ) (f : Nat → ℚ) K → sum₀ (λ j → c * f j) K ≡ c * sum₀ f K
sum-scale c f zero = sym (ℚP.*-zeroʳ c)
sum-scale c f (suc n) =
  trans (cong (_+ c * f n) (sum-scale c f n))
    (sym (ℚP.*-distribˡ-+ c (sum₀ f n) (f n)))

sum-cubes-agree :
  ∀ (g : Nat → ℚ) K → sum₀ (λ j → g j * g j * g j) K ≡ sumCubes g K
sum-cubes-agree g zero = refl
sum-cubes-agree g (suc n) = cong (_+ (g n * g n * g n)) (sum-cubes-agree g n)

record CumulativeSensitivityData (cutoff : Nat) : Set where
  field
    marginConstant derivativeBound tubeWidth : ℚ
    coupling sensitivity : Nat → ℚ
    marginPositive : 0ℚ < marginConstant
    derivativeNonNegative : 0ℚ ≤ derivativeBound
    cubicSumBound :
      ∀ K → K ℕ.≤ cutoff →
      marginConstant * sumCubes coupling K ≤ twoℚ * tubeWidth
    sensitivityCubic :
      ∀ j → sensitivity j
        ≤ (halfℚ * derivativeBound) * (coupling j * coupling j * coupling j)
    contractionGate : derivativeBound * tubeWidth < marginConstant

module Sensitivity {cutoff : Nat} (d : CumulativeSensitivityData cutoff) where
  open CumulativeSensitivityData d

  halfSlopeNonNegative : 0ℚ ≤ halfℚ * derivativeBound
  halfSlopeNonNegative =
    mul-nonNeg (ℚP.nonNegative⁻¹ halfℚ) derivativeNonNegative

  cumulativeSensitivityCubic :
    ∀ K → sum₀ sensitivity K
      ≤ (halfℚ * derivativeBound) * sumCubes coupling K
  cumulativeSensitivityCubic K =
    ℚP.≤-trans (sum-mono sensitivityCubic K)
      (ℚP.≤-reflexive
        (trans
          (sum-scale (halfℚ * derivativeBound)
            (λ j → coupling j * coupling j * coupling j) K)
          (cong ((halfℚ * derivativeBound) *_) (sum-cubes-agree coupling K))))

  scaledCumulativeSensitivity :
    ∀ K → K ℕ.≤ cutoff →
    marginConstant * sum₀ sensitivity K ≤ derivativeBound * tubeWidth
  scaledCumulativeSensitivity K K≤cutoff =
    ℚP.≤-trans
      (scaleˡ-nonNeg (ℚP.<⇒≤ marginPositive) (cumulativeSensitivityCubic K))
      (transport-≤ (sym regroup) collapse
        (scaleˡ-nonNeg halfSlopeNonNegative (cubicSumBound K K≤cutoff)))
    where
      regroup :
        marginConstant * ((halfℚ * derivativeBound) * sumCubes coupling K)
        ≡ (halfℚ * derivativeBound) * (marginConstant * sumCubes coupling K)
      regroup = solve 3
        (λ b c s → b :* (c :* s) := c :* (b :* s))
        refl marginConstant (halfℚ * derivativeBound) (sumCubes coupling K)

      collapse :
        (halfℚ * derivativeBound) * (twoℚ * tubeWidth)
        ≡ derivativeBound * tubeWidth
      collapse = solve 2
        (λ l t → (con halfℚ :* l) :* (con twoℚ :* t) := l :* t)
        refl derivativeBound tubeWidth

  cumulativeSensitivityBelowOne :
    ∀ K → K ℕ.≤ cutoff → sum₀ sensitivity K < 1ℚ
  cumulativeSensitivityBelowOne K K≤cutoff =
    ℚP.*-cancelˡ-<-nonNeg marginConstant
      {{nonNegative (ℚP.<⇒≤ marginPositive)}}
      (subst (λ z → marginConstant * sum₀ sensitivity K < z)
        (sym (ℚP.*-identityʳ marginConstant))
        (ℚP.≤-<-trans (scaledCumulativeSensitivity K K≤cutoff) contractionGate))

  shootingContractionConstantBelowOne :
    ∀ K → K ℕ.≤ cutoff → (target : ℚ) (history : ℚ → ℚ) →
    (∀ u v → ∣ history u - history v ∣ ≤ sum₀ sensitivity K * ∣ u - v ∣) →
    (∀ u v → ∣ (target + history u) - (target + history v) ∣
      ≤ sum₀ sensitivity K * ∣ u - v ∣)
    × (sum₀ sensitivity K < 1ℚ)
  shootingContractionConstantBelowOne K K≤cutoff target history lipschitz =
    shootingContraction {q = sum₀ sensitivity K} target history lipschitz
      , cumulativeSensitivityBelowOne K K≤cutoff

module GateWitness where
  open Cubic.PositiveMarginWitness using (witnessCoupling; witnessFlow)
  module WitnessFlow = Cubic.Flow witnessFlow

  witnessTube : ℚ
  witnessTube = + 1 / 2

  witnessDerivative : ℚ
  witnessDerivative = + 2 / 1

  witnessSensitivity : Nat → ℚ
  witnessSensitivity j =
    (halfℚ * witnessDerivative)
      * (witnessCoupling j * witnessCoupling j * witnessCoupling j)

  tubeBound : ∀ K → witnessCoupling K - witnessCoupling 0 ≤ witnessTube
  tubeBound zero = toWitness {a? = ((+ 1 / 2) - (+ 1 / 2)) ℚP.≤? witnessTube} _
  tubeBound (suc _) = toWitness {a? = (1ℚ - (+ 1 / 2)) ℚP.≤? witnessTube} _

  witnessData : CumulativeSensitivityData 1
  witnessData = record
    { marginConstant = + 3 / 1
    ; derivativeBound = witnessDerivative
    ; tubeWidth = witnessTube
    ; coupling = witnessCoupling
    ; sensitivity = witnessSensitivity
    ; marginPositive = toWitness {a? = 0ℚ ℚP.<? (+ 3 / 1)} _
    ; derivativeNonNegative = toWitness {a? = 0ℚ ℚP.≤? witnessDerivative} _
    ; cubicSumBound = λ K K≤1 →
        WitnessFlow.cubicSumInTube (toWitness {a? = 0ℚ ℚP.≤? (+ 3 / 1)} _) tubeBound K K≤1
    ; sensitivityCubic = λ _ → ℚP.≤-refl
    ; contractionGate =
        toWitness {a? = (witnessDerivative * witnessTube) ℚP.<? (+ 3 / 1)} _
    }

  open Sensitivity witnessData

  witnessBelowOne : sum₀ witnessSensitivity 1 < 1ℚ
  witnessBelowOne = cumulativeSensitivityBelowOne 1 ℕP.≤-refl
