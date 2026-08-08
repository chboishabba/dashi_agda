module DASHI.Physics.YangMills.BalabanP33LiteralHessianSpectralCertificateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics, 1995 reprint.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- DASHI CONTRIBUTION
--
-- Add a finite exact spectral certificate before any symbolic matrix inverse.
-- On the literal 3072-coordinate physical carrier an eigenpair equation is
-- converted to the exact Rayleigh identity
--
--   v^T M v = lambda ||v||^2.
--
-- Therefore a quadratic floor M >= c I certifies lambda >= c for every
-- normalized eigenvector.  If c>0, a normalized zero eigenvector is impossible.
-- This is a regression/certification theorem for a constructed literal Hessian;
-- it does not replace the analytic proof of the floor or construct that matrix.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact as Sq
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical

PhysicalVector : Set
PhysicalVector = Physical.PhysicalSU2Coordinate4 → ℚ

PhysicalMatrix : Set
PhysicalMatrix = Physical.PhysicalSU2Matrix4

PhysicalEigenpair : PhysicalMatrix → PhysicalVector → ℚ → Set
PhysicalEigenpair matrix vector eigenvalue =
  ∀ row →
  Physical.physicalMatrixApply matrix vector row
  ≡ eigenvalue * vector row

record PhysicalQuadraticFloor
    (matrix : PhysicalMatrix)
    (floor : ℚ) : Set₁ where
  field
    quadraticLower : ∀ vector →
      floor * Physical.physicalSU2CoordinateNormSq vector
      ≤ Physical.physicalMatrixQuadratic matrix vector

open PhysicalQuadraticFloor public

eigenpairQuadraticExact :
  ∀ matrix vector eigenvalue →
  PhysicalEigenpair matrix vector eigenvalue →
  Physical.physicalMatrixQuadratic matrix vector
  ≡ eigenvalue * Physical.physicalSU2CoordinateNormSq vector
eigenpairQuadraticExact matrix vector eigenvalue eigenpair =
  trans
    (Sums.sumRationalCong
      Physical.physicalSU2Coordinates4
      (λ row →
        vector row
          * Physical.physicalMatrixApply matrix vector row)
      (λ row → vector row * (eigenvalue * vector row))
      (λ row → cong (vector row *_) (eigenpair row)))
    (trans
      (Sums.sumRationalCong
        Physical.physicalSU2Coordinates4
        (λ row → vector row * (eigenvalue * vector row))
        (λ row → eigenvalue * Sq.sq (vector row))
        (λ row → ℚRing.solve-∀ (vector row) eigenvalue))
      (Sums.sumRationalScale
        eigenvalue
        Physical.physicalSU2Coordinates4
        (λ row → Sq.sq (vector row))))

normalizedEigenvalueLower :
  ∀ {matrix vector eigenvalue floor} →
  PhysicalQuadraticFloor matrix floor →
  PhysicalEigenpair matrix vector eigenvalue →
  Physical.physicalSU2CoordinateNormSq vector ≡ 1ℚ →
  floor ≤ eigenvalue
normalizedEigenvalueLower
    {matrix} {vector} {eigenvalue} {floor}
    lower eigenpair normalized =
  let
    quadraticBound = quadraticLower lower vector

    identified :
      floor * Physical.physicalSU2CoordinateNormSq vector
      ≤ eigenvalue * Physical.physicalSU2CoordinateNormSq vector
    identified =
      subst
        (λ upper →
          floor * Physical.physicalSU2CoordinateNormSq vector
          ≤ upper)
        (eigenpairQuadraticExact
          matrix vector eigenvalue eigenpair)
        quadraticBound
  in
  subst
    (λ left → left ≤ eigenvalue)
    (trans
      (cong (floor *_) normalized)
      (ℚRing.solve-∀ floor))
    (subst
      (λ right →
        floor * Physical.physicalSU2CoordinateNormSq vector
        ≤ right)
      (trans
        (cong (eigenvalue *_) normalized)
        (ℚRing.solve-∀ eigenvalue))
      identified)

literalHessianNoNormalizedZeroEigenvector :
  ∀ {matrix vector floor} →
  PhysicalQuadraticFloor matrix floor →
  0ℚ < floor →
  PhysicalEigenpair matrix vector 0ℚ →
  Physical.physicalSU2CoordinateNormSq vector ≡ 1ℚ →
  ⊥
literalHessianNoNormalizedZeroEigenvector
    lower floorPositive zeroEigenpair normalized =
  let
    floorBelowZero : _
    floorBelowZero =
      normalizedEigenvalueLower
        lower zeroEigenpair normalized
  in
  (ℚP.<⇒≱ floorPositive) floorBelowZero

p33OneThirtySecond : ℚ
p33OneThirtySecond = + 1 / 32

p33OneThirtySecondPositive : 0ℚ < p33OneThirtySecond
p33OneThirtySecondPositive = ℚP.positive⁻¹ p33OneThirtySecond

p33NormalizedEigenvalueAtLeastOneThirtySecond :
  ∀ {matrix vector eigenvalue} →
  PhysicalQuadraticFloor matrix p33OneThirtySecond →
  PhysicalEigenpair matrix vector eigenvalue →
  Physical.physicalSU2CoordinateNormSq vector ≡ 1ℚ →
  p33OneThirtySecond ≤ eigenvalue
p33NormalizedEigenvalueAtLeastOneThirtySecond =
  normalizedEigenvalueLower

p33NoNormalizedZeroEigenvector :
  ∀ {matrix vector} →
  PhysicalQuadraticFloor matrix p33OneThirtySecond →
  PhysicalEigenpair matrix vector 0ℚ →
  Physical.physicalSU2CoordinateNormSq vector ≡ 1ℚ →
  ⊥
p33NoNormalizedZeroEigenvector lower =
  literalHessianNoNormalizedZeroEigenvector
    lower p33OneThirtySecondPositive

literalHessianRayleighCertificateLevel : ProofLevel
literalHessianRayleighCertificateLevel = machineChecked

literalHessianNoZeroEigenvectorLevel : ProofLevel
literalHessianNoZeroEigenvectorLevel = machineChecked
