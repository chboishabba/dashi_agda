module DASHI.Physics.YangMills.BalabanStepVBishopFiniteGeometricExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- PURPOSE
-- Instantiate the finite Step-V geometric shell estimate on the repository's
-- concrete Bishop-real carrier.  For 0 <= q < 1 the supersolution is
-- B = (1-q)^(-1), and the generic finite induction proves every partial sum is
-- at most B.  No completed infinite series is used.
------------------------------------------------------------------------

open import Data.Rational.Unnormalised as ℚ using (0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as ℚP
open import Data.Sum.Base using (inj₂)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricBackendExact as StepV
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricInductionExact as Induction
open import DASHI.Physics.YangMills.CompactLieProofLevel

bishopOrderedSemiringKernel :
  StepV.OrderedSemiringKernel BishopReal.ℝ
bishopOrderedSemiringKernel = record
  { zero = BishopReal.0ℝ
  ; one = BishopReal.1ℝ
  ; add = BishopReal._+_
  ; multiply = BishopReal._*_
  ; LessEqual = BishopReal._≤_
  ; StrictlyLess = BishopReal._<_
  ; reflexive = λ value → BishopProperties.≤-refl
  ; transitive = BishopProperties.≤-trans
  ; addMonotone = BishopProperties.+-mono-≤
  ; multiplyMonotoneNonnegative =
      λ zeroBelowLeft zeroBelowRight leftBound rightBound →
        BishopProperties.*-mono-≤
          (BishopProperties.0≤x⇒nonNegx zeroBelowLeft)
          (BishopProperties.0≤x⇒nonNegx zeroBelowRight)
          leftBound rightBound
  }

bishopOneNonnegative :
  BishopReal._≤_ BishopReal.0ℝ BishopReal.1ℝ
bishopOneNonnegative =
  BishopProperties.p≤q⇒p⋆≤q⋆
    0ℚᵘ 1ℚᵘ (ℚP.nonNegative⁻¹ 1ℚᵘ)

bishopGeometricSemiringLaws :
  Induction.GeometricSemiringLaws bishopOrderedSemiringKernel
bishopGeometricSemiringLaws = record
  { Equivalent = BishopReal._≃_
  ; equivalentRefl = λ value → BishopProperties.≃-refl
  ; equivalentSym = BishopProperties.≃-symm
  ; equivalentTrans = BishopProperties.≃-trans
  ; lessEqualRespectLeft = BishopProperties.≤-respˡ-≃
  ; lessEqualRespectRight = BishopProperties.≤-respʳ-≃
  ; addCongruent = BishopProperties.+-cong
  ; multiplyCongruent = BishopProperties.*-cong
  ; addAssociative = BishopProperties.+-assoc
  ; addIdentityLeft = BishopProperties.+-identityˡ
  ; addIdentityRight = BishopProperties.+-identityʳ
  ; multiplyZeroRight = BishopProperties.*-zeroʳ
  ; multiplyDistributesOverAddLeft = BishopProperties.*-distribˡ-+
  ; zeroNonnegative = BishopProperties.≤-refl
  ; oneNonnegative = bishopOneNonnegative
  }

record BishopGeometricRatio : Set₁ where
  field
    ratio : BishopReal.ℝ
    ratioNonnegative :
      BishopReal._≤_ BishopReal.0ℝ ratio
    ratioBelowOne :
      BishopReal._<_ ratio BishopReal.1ℝ

open BishopGeometricRatio public

oneMinusRatio : BishopGeometricRatio → BishopReal.ℝ
oneMinusRatio inputs =
  BishopReal._-_ BishopReal.1ℝ (ratio inputs)

oneMinusRatioPositive :
  (inputs : BishopGeometricRatio) →
  BishopReal._<_ BishopReal.0ℝ (oneMinusRatio inputs)
oneMinusRatioPositive inputs =
  BishopProperties.x<y⇒0<y-x
    (ratio inputs) BishopReal.1ℝ (ratioBelowOne inputs)

oneMinusRatioNonzero :
  (inputs : BishopGeometricRatio) →
  BishopReal._≄0 (oneMinusRatio inputs)
oneMinusRatioNonzero inputs =
  inj₂ (oneMinusRatioPositive inputs)

bishopGeometricUniformBound :
  BishopGeometricRatio → BishopReal.ℝ
bishopGeometricUniformBound inputs =
  BishopInverse._⁻¹
    (oneMinusRatio inputs)
    (oneMinusRatioNonzero inputs)

bishopGeometricUniformBoundPositive :
  (inputs : BishopGeometricRatio) →
  BishopReal._<_ BishopReal.0ℝ
    (bishopGeometricUniformBound inputs)
bishopGeometricUniformBoundPositive inputs =
  BishopInverse.0<x⇒0<x⁻¹
    (oneMinusRatioNonzero inputs)
    (oneMinusRatioPositive inputs)

oneMinusRatioPlusRatioIsOne :
  (inputs : BishopGeometricRatio) →
  BishopReal._≃_
    (BishopReal._+_
      (oneMinusRatio inputs)
      (ratio inputs))
    BishopReal.1ℝ
oneMinusRatioPlusRatioIsOne inputs =
  let open BishopProperties.ℝ-Solver
  in solve 1
      (λ q → (Κ 1ℚᵘ ⊖ q) ⊕ q ⊜ Κ 1ℚᵘ)
      BishopProperties.≃-refl
      (ratio inputs)

bishopGeometricAffineFixedPoint :
  (inputs : BishopGeometricRatio) →
  BishopReal._≃_
    (BishopReal._+_
      BishopReal.1ℝ
      (BishopReal._*_
        (ratio inputs)
        (bishopGeometricUniformBound inputs)))
    (bishopGeometricUniformBound inputs)
bishopGeometricAffineFixedPoint inputs =
  let
    q = ratio inputs
    gap = oneMinusRatio inputs
    bound = bishopGeometricUniformBound inputs
    inverseLaw =
      BishopInverse.*-inverseʳ gap (oneMinusRatioNonzero inputs)
  in
  BishopProperties.≃-trans
    (BishopProperties.+-cong
      (BishopProperties.≃-symm inverseLaw)
      BishopProperties.≃-refl)
    (BishopProperties.≃-trans
      (BishopProperties.≃-symm
        (BishopProperties.*-distribʳ-+ bound gap q))
      (BishopProperties.≃-trans
        (BishopProperties.*-congʳ
          (oneMinusRatioPlusRatioIsOne inputs))
        (BishopProperties.*-identityˡ bound)))

bishopFiniteGeometricSupersolution :
  (inputs : BishopGeometricRatio) →
  Induction.FiniteGeometricSupersolution
    bishopOrderedSemiringKernel
    bishopGeometricSemiringLaws
    (ratio inputs)
bishopFiniteGeometricSupersolution inputs = record
  { ratioNonnegative = ratioNonnegative inputs
  ; ratioBelowOne = ratioBelowOne inputs
  ; uniformBound = bishopGeometricUniformBound inputs
  ; zeroBelowUniformBound =
      BishopProperties.<⇒≤
        (bishopGeometricUniformBoundPositive inputs)
  ; affineSupersolution =
      BishopProperties.≤-reflexive
        (bishopGeometricAffineFixedPoint inputs)
  }

bishopFiniteGeometricUniformBound :
  (inputs : BishopGeometricRatio) →
  StepV.FiniteGeometricUniformBound
    bishopOrderedSemiringKernel
    (ratio inputs)
bishopFiniteGeometricUniformBound inputs =
  Induction.finiteGeometricUniformBoundFromSupersolution
    (bishopFiniteGeometricSupersolution inputs)

bishopOrderedSemiringBackendLevel : ProofLevel
bishopOrderedSemiringBackendLevel = machineChecked

bishopFiniteGeometricSupersolutionLevel : ProofLevel
bishopFiniteGeometricSupersolutionLevel = machineChecked

bishopFiniteGeometricUniformBoundLevel : ProofLevel
bishopFiniteGeometricUniformBoundLevel = machineChecked
