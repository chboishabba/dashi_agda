module DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasResponseLocalityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jean-Michel Combes and Lawrence Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Convert the repository's literal physical Combes--Thomas kernel estimate
-- into the response estimate actually needed by RG1d.  For a source s,
--
--   delta A(root) = sum_y G(root,y) s(y)
--
-- and the already-proved Green bound gives
--
--   |delta A(root)|
--     <= 64 sum_y t^d(root,y) |s(y)|.
--
-- If s is supported only where the geometric weight is <= q_R, this becomes
--
--   |delta A(root)| <= 64 q_R ||s||_1.
--
-- Thus the nonlinear-background locality problem is reduced to (i) the exact
-- response identity coming from differentiating the selected minimizer and
-- (ii) a support statement for the remote perturbation.  The Green decay is
-- consumed on the actual source support, not replaced by a global norm bound.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33CombesThomasCoercivitySurvivalExact as Survival
import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasPromotionExact as CT

Source : Set
Source = Physical.PhysicalSU2Coordinate4 → ℚ

weightedSourceL1 :
  ∀ {hessian}
    (geometry : CT.PhysicalCombesThomasGeometry hessian) →
    Source → ℚ
weightedSourceL1 geometry source =
  Sums.sumRational Physical.physicalSU2Coordinates4
    (λ target → CT.physicalWeight geometry target * ∣ source target ∣)

sourceL1 : Source → ℚ
sourceL1 source =
  Sums.sumRational Physical.physicalSU2Coordinates4
    (λ target → ∣ source target ∣)

rootGreenResponse :
  ∀ {hessian green} →
  CT.PhysicalCombesThomasResolvent hessian green →
  Source → ℚ
rootGreenResponse {green = green} resolvent source =
  Sums.sumRational Physical.physicalSU2Coordinates4
    (λ target →
      green (CT.root (CT.geometry resolvent)) target * source target)

rootGreenResponseWeightedUpper :
  ∀ {hessian green}
    (resolvent : CT.PhysicalCombesThomasResolvent hessian green)
    source →
  ∣ rootGreenResponse resolvent source ∣
  ≤ Survival.p33InverseScale
      * weightedSourceL1 (CT.geometry resolvent) source
rootGreenResponseWeightedUpper {green = green} resolvent source =
  let
    indices = Physical.physicalSU2Coordinates4
    geometry = CT.geometry resolvent
    root = CT.root geometry

    triangle :
      ∣ rootGreenResponse resolvent source ∣
      ≤ Sums.sumRational indices
          (λ target → ∣ green root target ∣ * ∣ source target ∣)
    triangle =
      subst
        (λ upper → ∣ rootGreenResponse resolvent source ∣ ≤ upper)
        (Schur.sumAbsoluteProductsExact
          indices (green root) source)
        (Schur.sumAbsoluteTriangle
          indices (λ target → green root target * source target))

    pointwise : ∀ target →
      ∣ green root target ∣ * ∣ source target ∣
      ≤ (Survival.p33InverseScale * CT.physicalWeight geometry target)
          * ∣ source target ∣
    pointwise target =
      Norm.scaleNonnegative ∣ source target ∣
        (ℚP.0≤∣p∣ (source target))
        (CT.physicalGreenKernelDecay resolvent target)

    summed :
      Sums.sumRational indices
        (λ target → ∣ green root target ∣ * ∣ source target ∣)
      ≤ Sums.sumRational indices
        (λ target →
          (Survival.p33InverseScale * CT.physicalWeight geometry target)
            * ∣ source target ∣)
    summed = Schur.sumPointwiseBelow indices _ _ pointwise

    reassociate :
      Sums.sumRational indices
        (λ target →
          (Survival.p33InverseScale * CT.physicalWeight geometry target)
            * ∣ source target ∣)
      ≡ Sums.sumRational indices
        (λ target →
          Survival.p33InverseScale
            * (CT.physicalWeight geometry target * ∣ source target ∣))
    reassociate = Sums.sumRationalCong indices _ _
      (λ target → ℚRing.solve-∀
        Survival.p33InverseScale
        (CT.physicalWeight geometry target)
        ∣ source target ∣)

    factor :
      Sums.sumRational indices
        (λ target →
          Survival.p33InverseScale
            * (CT.physicalWeight geometry target * ∣ source target ∣))
      ≡ Survival.p33InverseScale
          * weightedSourceL1 geometry source
    factor = Sums.sumRationalScale
      Survival.p33InverseScale indices
      (λ target → CT.physicalWeight geometry target * ∣ source target ∣)
  in
  ℚP.≤-trans triangle
    (subst
      (λ upper →
        Sums.sumRational indices
          (λ target → ∣ green root target ∣ * ∣ source target ∣)
        ≤ upper)
      (trans reassociate factor)
      summed)

weightedSourceL1OnRemoteSupport :
  ∀ {hessian}
    (geometry : CT.PhysicalCombesThomasGeometry hessian)
    source q →
  (∀ target →
    source target ≡ 0ℚ
    ⊎ CT.physicalWeight geometry target ≤ q) →
  weightedSourceL1 geometry source ≤ q * sourceL1 source
weightedSourceL1OnRemoteSupport geometry source q support =
  let
    indices = Physical.physicalSU2Coordinates4

    pointwise : ∀ target →
      CT.physicalWeight geometry target * ∣ source target ∣
      ≤ q * ∣ source target ∣
    pointwise target with support target
    ... | inj₁ sourceZero rewrite sourceZero = ℚP.≤-refl
    ... | inj₂ weightBelow =
      Norm.scaleNonnegative ∣ source target ∣
        (ℚP.0≤∣p∣ (source target)) weightBelow

    summed = Schur.sumPointwiseBelow indices _ _ pointwise

    factor :
      Sums.sumRational indices
        (λ target → q * ∣ source target ∣)
      ≡ q * sourceL1 source
    factor = Sums.sumRationalScale q indices
      (λ target → ∣ source target ∣)
  in
  subst
    (λ upper → weightedSourceL1 geometry source ≤ upper)
    factor summed

rootGreenResponseRemoteUpper :
  ∀ {hessian green}
    (resolvent : CT.PhysicalCombesThomasResolvent hessian green)
    source q →
  (∀ target →
    source target ≡ 0ℚ
    ⊎ CT.physicalWeight (CT.geometry resolvent) target ≤ q) →
  ∣ rootGreenResponse resolvent source ∣
  ≤ (Survival.p33InverseScale * q) * sourceL1 source
rootGreenResponseRemoteUpper resolvent source q support =
  let
    weighted = rootGreenResponseWeightedUpper resolvent source
    supportBound = weightedSourceL1OnRemoteSupport
      (CT.geometry resolvent) source q support
    scaledSupport = Norm.scaleNonnegative Survival.p33InverseScale
      (ℚP.nonNegative⁻¹ Survival.p33InverseScale)
      supportBound
  in
  ℚP.≤-trans weighted
    (subst
      (λ upper →
        Survival.p33InverseScale
          * weightedSourceL1 (CT.geometry resolvent) source
        ≤ upper)
      (ℚRing.solve-∀
        Survival.p33InverseScale q (sourceL1 source))
      scaledSupport)

p33PhysicalCombesThomasWeightedResponseLevel : ProofLevel
p33PhysicalCombesThomasWeightedResponseLevel = machineChecked

p33PhysicalCombesThomasRemoteResponseLevel : ProofLevel
p33PhysicalCombesThomasRemoteResponseLevel = machineChecked
