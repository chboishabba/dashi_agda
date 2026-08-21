module DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact where

------------------------------------------------------------------------
-- ROW A, CONTRACTION GATE:
--   UNIFORM COUPLING-DERIVATIVE BOUND  +  CUBIC DRIFT TELESCOPE
--   ==>  CUMULATIVE SHOOTING SENSITIVITY  q < 1  (cutoff-independent)
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I.", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- WHAT THIS MODULE CONTAINS.
--
--   (a) THE SHOOTING-MAP TRANSFER.  Bałaban's tuning problem is a fixed point
--       problem for the shooting map
--
--            T_K(u)  =  u_R + B_K(u),
--
--       where u_R is the prescribed physical target and B_K accumulates the
--       beta history.  The target cancels identically from differences, so a
--       cumulative-beta Lipschitz bound transfers verbatim:
--
--            |B_K(u) - B_K(v)| <= q |u - v|
--         ==> |T_K(u) - T_K(v)| <= q |u - v|.
--
--   (b) WHERE A CUTOFF-UNIFORM q < 1 CAN COME FROM.  In the shooting variable
--       u = g^{-2} one has |dg/du| = g^3/2, so a uniform coupling-derivative
--       bound |d beta_j / d g| <= L gives the per-shell sensitivity estimate
--
--            |d beta_j / d u|  <=  (L/2) g_j^3.
--
--       The telescope of
--       `DASHI.Physics.YangMills.BalabanYM4CubicCouplingDriftTelescopeExact`
--       bounds sum_j g_j^3 by 2 gamma / b_* uniformly in the cutoff, whence
--
--            sum_{j<K} |d beta_j / d u|  <=  L gamma / b_* ,
--
--       and this module proves the resulting sharp gate: if
--
--            L gamma  <  b_*
--
--       then the cumulative sensitivity is *strictly below 1* for every K,
--       i.e. the shooting map of (a) is a strict contraction with a constant
--       independent of the cutoff.
--
-- WHAT IS *NOT* PROVED.  The two analytic inputs — the uniform derivative
-- constant L for the literal beta law, and the positive inverse-square margin
-- b_* for the literal constrained Gaussian determinant — are open.  Row A
-- therefore stays open and the frozen research count stays at 4.
--
-- Exact rational arithmetic; no postulate, no hole, no receipt.  Checked with
-- `agda --safe`.
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
open import Relation.Binary.PropositionalEquality
  using (sym; trans; cong; subst)
open import Relation.Nullary.Decidable using (toWitness)

open import DASHI.Physics.YangMills.BalabanYM4LinearInteractionBetaMarginExact
  using (sum₀)
import DASHI.Physics.YangMills.BalabanYM4CubicCouplingDriftTelescopeExact as Cubic
open Cubic
  using (twoℚ; halfℚ; sumCubes; mul-nonNeg; scaleˡ-nonNeg; transport-≤)

open +-*-Solver

------------------------------------------------------------------------
-- (a) The shooting map inherits any cumulative-beta contraction constant
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Finite-sum helpers
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- (b) The cutoff-independent contraction gate  L gamma < b_*
------------------------------------------------------------------------

record CumulativeSensitivityData (cutoff : Nat) : Set where
  field
    marginConstant   : ℚ
    derivativeBound  : ℚ
    tubeWidth        : ℚ
    coupling         : Nat → ℚ
    sensitivity      : Nat → ℚ

    marginPositive        : 0ℚ < marginConstant
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
        (trans (sum-scale (halfℚ * derivativeBound)
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
      regroup =
        solve 3
          (λ b c s → b :* (c :* s) := c :* (b :* s))
          refl marginConstant (halfℚ * derivativeBound) (sumCubes coupling K)

      collapse :
        (halfℚ * derivativeBound) * (twoℚ * tubeWidth)
          ≡ derivativeBound * tubeWidth
      collapse =
        solve 2
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

------------------------------------------------------------------------
-- (c) Non-vacuity witness
------------------------------------------------------------------------

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
    ; cubicSumBound = λ K K≤1 → WitnessFlow.cubicSumInTube tubeBound K K≤1
    ; sensitivityCubic = λ _ → ℚP.≤-refl
    ; contractionGate =
        toWitness {a? = (witnessDerivative * witnessTube) ℚP.<? (+ 3 / 1)} _
    }

  open Sensitivity witnessData

  witnessBelowOne : sum₀ witnessSensitivity 1 < 1ℚ
  witnessBelowOne = cumulativeSensitivityBelowOne 1 ℕP.≤-refl
