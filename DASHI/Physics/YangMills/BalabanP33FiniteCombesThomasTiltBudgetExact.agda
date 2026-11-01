module DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasTiltBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Peter D. Hislop,
-- "Lectures on Random Schrödinger Operators", Contemporary Mathematics 476
-- (2008), 41--131.
-- DOI: 10.1090/conm/476/09307.
--
-- DASHI CONTRIBUTION
--
-- Prove the finite row-budget estimate used in the conjugation proof.  If
--
--   K_D(x,y) = D(x) K(x,y) D^{-1}(y)
--
-- and every supported entry obeys
--
--   |D(x)D^{-1}(y)-1| <= a,
--
-- then the exact tilt defect E=K_D-K satisfies
--
--   sum_y |E(x,y)| <= a sum_y |K(x,y)|.
--
-- This is the standard Combes--Thomas perturbation estimate, proved here by
-- literal finite-list induction rather than hidden in an operator-norm socket.
-- At the P33 coercivity floor delta=1/32, the admissible half-gap tilt budget is
-- delta/2=1/64 and the classical tilted-resolvent majorant is 2/delta=64.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasConjugationExact as CT

------------------------------------------------------------------------
-- Absolute row masses.
------------------------------------------------------------------------

absoluteRowMass :
  ∀ {Site : Set} →
  List Site → CT.Matrix Site → Site → ℚ
absoluteRowMass sites kernel left =
  CT.sumRational sites (λ right → ∣ kernel left right ∣)

tiltDefectAbsoluteRowMass :
  ∀ {Site : Set} →
  List Site →
  (weight inverseWeight : Site → ℚ) →
  CT.Matrix Site → Site → ℚ
tiltDefectAbsoluteRowMass sites weight inverseWeight kernel left =
  absoluteRowMass sites
    (CT.diagonalTiltDefect weight inverseWeight kernel)
    left

------------------------------------------------------------------------
-- Entrywise factorization and bound.
------------------------------------------------------------------------

tiltDefectFactorization :
  ∀ {Site : Set}
    (weight inverseWeight : Site → ℚ)
    (kernel : CT.Matrix Site)
    (left right : Site) →
  CT.diagonalTiltDefect weight inverseWeight kernel left right
  ≡ (weight left * inverseWeight right - (+ 1 / 1))
      * kernel left right
tiltDefectFactorization
    weight inverseWeight kernel left right =
  ℚRing.solve []

tiltDefectAbsoluteFactorization :
  ∀ {Site : Set}
    (weight inverseWeight : Site → ℚ)
    (kernel : CT.Matrix Site)
    (left right : Site) →
  ∣ CT.diagonalTiltDefect weight inverseWeight kernel left right ∣
  ≡ ∣ weight left * inverseWeight right - (+ 1 / 1) ∣
      * ∣ kernel left right ∣
tiltDefectAbsoluteFactorization
    weight inverseWeight kernel left right =
  trans
    (cong ∣_∣
      (tiltDefectFactorization
        weight inverseWeight kernel left right))
    (ℚP.∣p*q∣≡∣p∣*∣q∣
      (weight left * inverseWeight right - (+ 1 / 1))
      (kernel left right))
  where
    open import Relation.Binary.PropositionalEquality using (cong)

tiltDefectEntryAbsoluteBound :
  ∀ {Site : Set}
    (weight inverseWeight : Site → ℚ)
    (kernel : CT.Matrix Site)
    (distortion : ℚ)
    (left right : Site) →
  ∣ weight left * inverseWeight right - (+ 1 / 1) ∣
    ≤ distortion →
  ∣ CT.diagonalTiltDefect weight inverseWeight kernel left right ∣
    ≤ distortion * ∣ kernel left right ∣
tiltDefectEntryAbsoluteBound
    weight inverseWeight kernel distortion left right ratioBound =
  let
    instance
      kernelAbsNN : NonNegative ∣ kernel left right ∣
      kernelAbsNN = ℚP.∣-∣-nonNeg (kernel left right)

    scaled =
      ℚP.*-monoʳ-≤-nonNeg
        ∣ kernel left right ∣ ratioBound
  in
  subst
    (λ lower → lower ≤ distortion * ∣ kernel left right ∣)
    (sym
      (tiltDefectAbsoluteFactorization
        weight inverseWeight kernel left right))
    scaled

------------------------------------------------------------------------
-- Finite summation of the entrywise tilt estimate.
------------------------------------------------------------------------

sumScale :
  ∀ {Site : Set}
    (sites : List Site)
    (scale : ℚ)
    (value : Site → ℚ) →
  CT.sumRational sites (λ site → scale * value site)
  ≡ scale * CT.sumRational sites value
sumScale [] scale value = ℚRing.solve []
sumScale (site ∷ sites) scale value
  rewrite sumScale sites scale value =
  ℚRing.solve []

sumPointwiseBelow :
  ∀ {Site : Set}
    (sites : List Site)
    (left right : Site → ℚ) →
  (∀ site → left site ≤ right site) →
  CT.sumRational sites left ≤ CT.sumRational sites right
sumPointwiseBelow [] left right pointwise = ℚP.≤-refl
sumPointwiseBelow (site ∷ sites) left right pointwise =
  ℚP.+-mono-≤
    (pointwise site)
    (sumPointwiseBelow sites left right pointwise)

tiltDefectRowMassBound :
  ∀ {Site : Set}
    (sites : List Site)
    (weight inverseWeight : Site → ℚ)
    (kernel : CT.Matrix Site)
    (distortion : ℚ) →
  (∀ left right →
    ∣ weight left * inverseWeight right - (+ 1 / 1) ∣
      ≤ distortion) →
  ∀ left →
  tiltDefectAbsoluteRowMass
    sites weight inverseWeight kernel left
  ≤ distortion * absoluteRowMass sites kernel left
tiltDefectRowMassBound
    sites weight inverseWeight kernel distortion ratioBound left =
  subst
    (λ upper →
      tiltDefectAbsoluteRowMass
        sites weight inverseWeight kernel left
      ≤ upper)
    (sumScale sites distortion (λ right → ∣ kernel left right ∣))
    (sumPointwiseBelow
      sites
      (λ right →
        ∣ CT.diagonalTiltDefect
            weight inverseWeight kernel left right ∣)
      (λ right → distortion * ∣ kernel left right ∣)
      (λ right →
        tiltDefectEntryAbsoluteBound
          weight inverseWeight kernel distortion left right
          (ratioBound left right)))

tiltDefectRowBelowBudget :
  ∀ {Site : Set}
    (sites : List Site)
    (weight inverseWeight : Site → ℚ)
    (kernel : CT.Matrix Site)
    (distortion rowMass budget : ℚ) →
  0ℚ ≤ distortion →
  (∀ left right →
    ∣ weight left * inverseWeight right - (+ 1 / 1) ∣
      ≤ distortion) →
  (∀ left → absoluteRowMass sites kernel left ≤ rowMass) →
  distortion * rowMass ≤ budget →
  ∀ left →
  tiltDefectAbsoluteRowMass
    sites weight inverseWeight kernel left
  ≤ budget
tiltDefectRowBelowBudget
    sites weight inverseWeight kernel distortion rowMass budget
    distortionNonnegative ratioBound rowBound scalarBudget left =
  let
    instance
      distortionNN : NonNegative distortion
      distortionNN = ℚ.nonNegative distortionNonnegative
  in
  ℚP.≤-trans
    (tiltDefectRowMassBound
      sites weight inverseWeight kernel distortion ratioBound left)
    (ℚP.≤-trans
      (ℚP.*-monoˡ-≤-nonNeg distortion (rowBound left))
      scalarBudget)

------------------------------------------------------------------------
-- Exact P33 gap calibration.
------------------------------------------------------------------------

p33SpectralGap p33HalfGap p33TiltedResolventMajorant : ℚ
p33SpectralGap = + 1 / 32
p33HalfGap = + 1 / 64
p33TiltedResolventMajorant = + 64 / 1

p33HalfGapIsHalf :
  (+ 2 / 1) * p33HalfGap ≡ p33SpectralGap
p33HalfGapIsHalf = ℚRing.solve []

p33TiltedResolventMajorantIsTwoOverGap :
  p33TiltedResolventMajorant * p33SpectralGap ≡ + 2 / 1
p33TiltedResolventMajorantIsTwoOverGap = ℚRing.solve []

p33TiltDefectBelowHalfGap :
  ∀ {Site : Set}
    (sites : List Site)
    (weight inverseWeight : Site → ℚ)
    (kernel : CT.Matrix Site)
    (distortion rowMass : ℚ) →
  0ℚ ≤ distortion →
  (∀ left right →
    ∣ weight left * inverseWeight right - (+ 1 / 1) ∣
      ≤ distortion) →
  (∀ left → absoluteRowMass sites kernel left ≤ rowMass) →
  distortion * rowMass ≤ p33HalfGap →
  ∀ left →
  tiltDefectAbsoluteRowMass
    sites weight inverseWeight kernel left
  ≤ p33HalfGap
p33TiltDefectBelowHalfGap =
  tiltDefectRowBelowBudget

finiteCombesThomasTiltEntryLevel : ProofLevel
finiteCombesThomasTiltEntryLevel = machineChecked

finiteCombesThomasTiltRowBudgetLevel : ProofLevel
finiteCombesThomasTiltRowBudgetLevel = machineChecked

p33CombesThomasGapCalibrationLevel : ProofLevel
p33CombesThomasGapCalibrationLevel = machineChecked
