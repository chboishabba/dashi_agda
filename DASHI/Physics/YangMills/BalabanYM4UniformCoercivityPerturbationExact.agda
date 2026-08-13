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
-- costing at most 1/64 of ||h||^2 leaves a uniform 1/64 floor.
--
-- Round 53 also exposes the preferred LOCAL route.  If the plaquette Hessian
-- decomposition yields an aggregate Lipschitz estimate
--
--   variation <= (L_H * radius * overlap) ||h||^2
--
-- then the entire all-background coercivity theorem reduces to the scalar
-- invariant-region compatibility condition
--
--   L_H * radius * overlap <= 1/64.
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

------------------------------------------------------------------------
-- Local plaquette-Lipschitz route.
------------------------------------------------------------------------

record LocalHessianRadiusBudget
    (normSq perturbationMagnitude : ℚ) : Set where
  field
    localLipschitz backgroundRadius overlap : ℚ

    aggregateLocalVariation :
      perturbationMagnitude
      ≤ ((localLipschitz * backgroundRadius) * overlap) * normSq

    radiusCompatibility :
      (localLipschitz * backgroundRadius) * overlap
      ≤ perturbationAllowance

open LocalHessianRadiusBudget public

localRadiusBudgetGivesOneSixtyFourthVariation :
  ∀ normSq perturbationMagnitude →
  0ℚ ≤ normSq →
  LocalHessianRadiusBudget normSq perturbationMagnitude →
  perturbationMagnitude ≤ perturbationAllowance * normSq
localRadiusBudgetGivesOneSixtyFourthVariation
    normSq perturbationMagnitude normNonnegative data =
  ℚP.≤-trans
    (aggregateLocalVariation data)
    (ℚP.*-monoʳ-≤-nonNeg normSq (radiusCompatibility data))

localRadiusBudgetClosesUniformCoercivity :
  ∀ normSq referenceQuadratic currentQuadratic perturbationMagnitude →
  0ℚ ≤ normSq →
  selectedFloor * normSq ≤ referenceQuadratic →
  referenceQuadratic - perturbationMagnitude ≤ currentQuadratic →
  LocalHessianRadiusBudget normSq perturbationMagnitude →
  uniformFloor * normSq ≤ currentQuadratic
localRadiusBudgetClosesUniformCoercivity
    normSq referenceQuadratic currentQuadratic perturbationMagnitude
    normNonnegative referenceBound currentBound localBudget =
  uniformOneSixtyFourthFloor
    normSq referenceQuadratic currentQuadratic perturbationMagnitude
    record
      { referenceFloor = referenceBound
      ; perturbationSmall =
          localRadiusBudgetGivesOneSixtyFourthVariation
            normSq perturbationMagnitude normNonnegative localBudget
      ; currentAboveReferenceMinusPerturbation = currentBound
      }

ym4UniformCoercivityPerturbationArithmeticLevel : ProofLevel
ym4UniformCoercivityPerturbationArithmeticLevel = machineChecked

ym4LocalHessianRadiusCompatibilityLevel : ProofLevel
ym4LocalHessianRadiusCompatibilityLevel = machineChecked

-- Remaining physical RG1c leaf: prove the literal Wilson-Hessian local
-- Lipschitz/overlap decomposition and verify L_H * r_RG * overlap <= 1/64.
ym4PhysicalLocalHessianRadiusBudgetLevel : ProofLevel
ym4PhysicalLocalHessianRadiusBudgetLevel = conditional
