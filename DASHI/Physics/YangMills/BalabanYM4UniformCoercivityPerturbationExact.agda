module DASHI.Physics.YangMills.BalabanYM4UniformCoercivityPerturbationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics, 1995 reprint.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- DASHI CONTRIBUTION
--
-- Quantitative RG1c perturbation lemma.  Starting from the selected physical
-- constrained-Hessian floor 1/32, any same-carrier quadratic-form variation
-- costing at most 1/64 of ||h||^2 leaves a uniform 1/64 floor.  This is the
-- exact amount of background-uniformity the Combes--Thomas lane needs; one
-- does not have to reconstruct the selected coercivity proof at each RG state.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; -_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

selectedFloor perturbationAllowance uniformFloor : ℚ
selectedFloor = + 1 / 32
perturbationAllowance = + 1 / 64
uniformFloor = + 1 / 64

floorDifferenceExact :
  selectedFloor - perturbationAllowance ≡ uniformFloor
floorDifferenceExact = ℚRing.solve []

record QuadraticFormPerturbationData
    (normSq referenceQuadratic currentQuadratic perturbationMagnitude : ℚ) : Set where
  field
    referenceFloor : selectedFloor * normSq ≤ referenceQuadratic

    perturbationSmall :
      perturbationMagnitude ≤ perturbationAllowance * normSq

    currentAboveReferenceMinusPerturbation :
      referenceQuadratic - perturbationMagnitude ≤ currentQuadratic

open QuadraticFormPerturbationData public

uniformOneSixtyFourthFloor :
  ∀ normSq referenceQuadratic currentQuadratic perturbationMagnitude →
  QuadraticFormPerturbationData
    normSq referenceQuadratic currentQuadratic perturbationMagnitude →
  uniformFloor * normSq ≤ currentQuadratic
uniformOneSixtyFourthFloor
    normSq referenceQuadratic currentQuadratic perturbationMagnitude data =
  let
    signedCombined :
      selectedFloor * normSq + (- (perturbationAllowance * normSq))
      ≤ referenceQuadratic + (- perturbationMagnitude)
    signedCombined = ℚP.+-mono-≤
      (referenceFloor data)
      (ℚP.neg-mono-≤ (perturbationSmall data))

    differenceBound :
      (selectedFloor - perturbationAllowance) * normSq
      ≤ referenceQuadratic - perturbationMagnitude
    differenceBound =
      subst
        (λ lower → lower ≤ referenceQuadratic - perturbationMagnitude)
        (ℚRing.solve-∀ selectedFloor perturbationAllowance normSq)
        (subst
          (λ upper →
            selectedFloor * normSq + (- (perturbationAllowance * normSq))
            ≤ upper)
          (ℚRing.solve-∀ referenceQuadratic perturbationMagnitude)
          signedCombined)

    currentBound :
      (selectedFloor - perturbationAllowance) * normSq ≤ currentQuadratic
    currentBound = ℚP.≤-trans differenceBound
      (currentAboveReferenceMinusPerturbation data)
  in
  subst
    (λ coefficient → coefficient * normSq ≤ currentQuadratic)
    (sym floorDifferenceExact)
    currentBound

ym4UniformCoercivityPerturbationArithmeticLevel : ProofLevel
ym4UniformCoercivityPerturbationArithmeticLevel = machineChecked

-- Remaining physical RG1c leaf: on every admissible generated background A,
-- prove the same-carrier form estimate
--
--   |<h,(H_A-H_ref)h>| <= (1/64)||h||^2.
--
-- Combined with the existing selected 1/32 floor this module yields the
-- uniform 1/64 floor consumed by the physical Combes--Thomas theorem.
ym4PhysicalHessianVariationOneSixtyFourthLevel : ProofLevel
ym4PhysicalHessianVariationOneSixtyFourthLevel = conditional
