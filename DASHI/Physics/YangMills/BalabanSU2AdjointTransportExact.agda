module DASHI.Physics.YangMills.BalabanSU2AdjointTransportExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_+R_; _*R_; -R_; zeroR; oneR; -‿inverseʳ)
open import DASHI.Physics.YangMills.BalabanSU2AdjointRotationScalar using
  (rotationX; rotationY; rotationZ)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (module RealPolynomialSolver; oneCoefficient; zeroCoefficient)
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  (solveComputed; computed)
open import DASHI.Physics.YangMills.BalabanSU2AdjointRotationPolynomial using
  (rotationXP; rotationYP; rotationZP; oneP; twoP)
open RealPolynomialSolver using
  (Polynomial; con; _:=_; _:+_; _:*_; :-_)

------------------------------------------------------------------------
-- Exact SU(2) adjoint-transport algebra.
--
-- For q = a + bi + cj + dk and v = (x,y,z), the existing concrete
-- quaternion conjugation formulas give the literal adjoint rotation Rq v.
-- This module proves, by computed integer-coefficient normalization:
--
--   ||Rq v||² = ||q||⁴ ||v||²
--
-- and the stronger displacement identity
--
--   ||Rq v - v||²
--     = 4 ( ||Im q||² ||v||² - <Im q,v>² )
--       + (||q||² - 1)² ||v||².
--
-- On the unit-quaternion carrier the defect term vanishes exactly.  This is
-- the algebraic core needed by the transport part of the background-Hessian
-- perturbation estimate; the subsequent ordered norm/radius estimate remains
-- a separate analytic step.
------------------------------------------------------------------------

twoR fourR : ℝ
twoR = oneR +R oneR
fourR = twoR *R twoR

squareR : ℝ → ℝ
squareR value = value *R value

qNormSqR : ℝ → ℝ → ℝ → ℝ → ℝ
qNormSqR a b c d =
  ((squareR a +R squareR b) +R squareR c) +R squareR d

imaginaryNormSqR : ℝ → ℝ → ℝ → ℝ
imaginaryNormSqR b c d =
  (squareR b +R squareR c) +R squareR d

vectorNormSqR : ℝ → ℝ → ℝ → ℝ
vectorNormSqR x y z =
  (squareR x +R squareR y) +R squareR z

imaginaryDotVectorR :
  ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
imaginaryDotVectorR b c d x y z =
  ((b *R x) +R (c *R y)) +R (d *R z)

rotatedNormSqR :
  ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
rotatedNormSqR a b c d x y z =
  (squareR (rotationX a b c d x y z)
    +R squareR (rotationY a b c d x y z))
    +R squareR (rotationZ a b c d x y z)

adjointDisplacementSqR :
  ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
adjointDisplacementSqR a b c d x y z =
  (squareR (rotationX a b c d x y z +R (-R x))
    +R squareR (rotationY a b c d x y z +R (-R y)))
    +R squareR (rotationZ a b c d x y z +R (-R z))

unitDefectR : ℝ → ℝ → ℝ → ℝ → ℝ
unitDefectR a b c d = qNormSqR a b c d +R (-R oneR)

unitAdjointDisplacementMainR :
  ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
unitAdjointDisplacementMainR b c d x y z =
  fourR *R
    ((imaginaryNormSqR b c d *R vectorNormSqR x y z)
      +R (-R squareR (imaginaryDotVectorR b c d x y z)))

------------------------------------------------------------------------
-- Computed polynomial syntax.
------------------------------------------------------------------------

fourP : ∀ {n} → Polynomial n
fourP = twoP :* twoP

squareP : ∀ {n} → Polynomial n → Polynomial n
squareP value = value :* value

qNormSqP :
  ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n
qNormSqP a b c d =
  ((squareP a :+ squareP b) :+ squareP c) :+ squareP d

imaginaryNormSqP :
  ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n
imaginaryNormSqP b c d =
  (squareP b :+ squareP c) :+ squareP d

vectorNormSqP :
  ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n
vectorNormSqP x y z =
  (squareP x :+ squareP y) :+ squareP z

imaginaryDotVectorP :
  ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
imaginaryDotVectorP b c d x y z =
  ((b :* x) :+ (c :* y)) :+ (d :* z)

rotatedNormSqP :
  ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
rotatedNormSqP a b c d x y z =
  (squareP (rotationXP a b c d x y z)
    :+ squareP (rotationYP a b c d x y z))
    :+ squareP (rotationZP a b c d x y z)

adjointDisplacementSqP :
  ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
adjointDisplacementSqP a b c d x y z =
  (squareP (rotationXP a b c d x y z :+ (:- x))
    :+ squareP (rotationYP a b c d x y z :+ (:- y)))
    :+ squareP (rotationZP a b c d x y z :+ (:- z))

unitDefectP :
  ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n
unitDefectP a b c d = qNormSqP a b c d :+ (:- oneP)

unitAdjointDisplacementMainP :
  ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
unitAdjointDisplacementMainP b c d x y z =
  fourP :*
    ((imaginaryNormSqP b c d :* vectorNormSqP x y z)
      :+ (:- squareP (imaginaryDotVectorP b c d x y z)))

------------------------------------------------------------------------
-- Exact identities.
------------------------------------------------------------------------

adjointRotationNormExact :
  ∀ a b c d x y z →
  rotatedNormSqR a b c d x y z
  ≡ (qNormSqR a b c d *R qNormSqR a b c d)
      *R vectorNormSqR x y z
adjointRotationNormExact =
  solveComputed 7
    (λ a b c d x y z →
      rotatedNormSqP a b c d x y z
      := (qNormSqP a b c d :* qNormSqP a b c d)
          :* vectorNormSqP x y z)
    computed

adjointDisplacementWithUnitDefectExact :
  ∀ a b c d x y z →
  adjointDisplacementSqR a b c d x y z
  ≡ unitAdjointDisplacementMainR b c d x y z
      +R ((unitDefectR a b c d *R unitDefectR a b c d)
        *R vectorNormSqR x y z)
adjointDisplacementWithUnitDefectExact =
  solveComputed 7
    (λ a b c d x y z →
      adjointDisplacementSqP a b c d x y z
      := unitAdjointDisplacementMainP b c d x y z
        :+ ((unitDefectP a b c d :* unitDefectP a b c d)
          :* vectorNormSqP x y z))
    computed

unitDefectVanishes :
  ∀ a b c d →
  qNormSqR a b c d ≡ oneR →
  unitDefectR a b c d ≡ zeroR
unitDefectVanishes a b c d unit =
  trans
    (cong (λ value → value +R (-R oneR)) unit)
    (-‿inverseʳ oneR)

dropZeroDefect :
  ∀ main vectorNorm →
  main +R ((zeroR *R zeroR) *R vectorNorm) ≡ main
dropZeroDefect =
  solveComputed 2
    (λ main vectorNorm →
      main :+ (((con zeroCoefficient) :* (con zeroCoefficient))
        :* vectorNorm)
      := main)
    computed

adjointDisplacementOnUnitQuaternion :
  ∀ a b c d x y z →
  qNormSqR a b c d ≡ oneR →
  adjointDisplacementSqR a b c d x y z
  ≡ unitAdjointDisplacementMainR b c d x y z
adjointDisplacementOnUnitQuaternion a b c d x y z unit
  rewrite unitDefectVanishes a b c d unit =
  trans
    (adjointDisplacementWithUnitDefectExact a b c d x y z)
    (dropZeroDefect
      (unitAdjointDisplacementMainR b c d x y z)
      (vectorNormSqR x y z))

su2AdjointNormIdentityLevel : ProofLevel
su2AdjointNormIdentityLevel = computed

su2AdjointUnitDisplacementIdentityLevel : ProofLevel
su2AdjointUnitDisplacementIdentityLevel = machineChecked

su2AdjointSmallRadiusOperatorBoundLevel : ProofLevel
su2AdjointSmallRadiusOperatorBoundLevel = conditional
