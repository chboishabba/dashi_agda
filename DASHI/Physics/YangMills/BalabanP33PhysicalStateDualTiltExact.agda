module DASHI.Physics.YangMills.BalabanP33PhysicalStateDualTiltExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrodinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Make the state/test-covector distinction explicit on the literal physical
-- coordinate carrier.  The Combes--Thomas weight and its reciprocal act
-- pointwise on states, are exact inverses, and the existing diagonal
-- conjugation is identified entrywise with
--
--   M_mu(x,y) = W_mu(x) M(x,y) W_mu^-1(y).
--
-- The tilt defect is therefore the same support-local matrix multiplied by the
-- scalar modulation defect.  This is an adapter to the existing physical
-- Combes--Thomas proof, not a new independent decay premise.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasConjugationExact as CT
import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasPromotionExact as Promotion

Coordinate : Set
Coordinate = Physical.PhysicalSU2Coordinate4

PhysicalState : Set
PhysicalState = Coordinate → ℚ

PhysicalCovector : Set
PhysicalCovector = Coordinate → ℚ

PhysicalOperator : Set
PhysicalOperator = Physical.PhysicalSU2Matrix4

stateCovectorPairing : PhysicalCovector → PhysicalState → ℚ
stateCovectorPairing = Physical.physicalCoordinateDot

weightState :
  ∀ {matrix} →
  Promotion.PhysicalCombesThomasGeometry matrix →
  PhysicalState → PhysicalState
weightState geometry state coordinate =
  Promotion.physicalWeight geometry coordinate * state coordinate

inverseWeightState :
  ∀ {matrix} →
  Promotion.PhysicalCombesThomasGeometry matrix →
  PhysicalState → PhysicalState
inverseWeightState geometry state coordinate =
  Promotion.physicalInverseWeight geometry coordinate * state coordinate

weightAfterInverseWeightPointwise :
  ∀ {matrix}
    (geometry : Promotion.PhysicalCombesThomasGeometry matrix)
    state coordinate →
  weightState geometry (inverseWeightState geometry state) coordinate
  ≡ state coordinate
weightAfterInverseWeightPointwise geometry state coordinate =
  trans
    (ℚRing.solve-∀
      (Promotion.physicalWeight geometry coordinate)
      (Promotion.physicalInverseWeight geometry coordinate)
      (state coordinate))
    (trans
      (cong
        (_* state coordinate)
        (Promotion.physicalWeightInverseLawCommuted
          geometry coordinate))
      (ℚRing.solve-∀ (state coordinate)))

inverseWeightAfterWeightPointwise :
  ∀ {matrix}
    (geometry : Promotion.PhysicalCombesThomasGeometry matrix)
    state coordinate →
  inverseWeightState geometry (weightState geometry state) coordinate
  ≡ state coordinate
inverseWeightAfterWeightPointwise geometry state coordinate =
  trans
    (ℚRing.solve-∀
      (Promotion.physicalWeight geometry coordinate)
      (Promotion.physicalInverseWeight geometry coordinate)
      (state coordinate))
    (trans
      (cong
        (_* state coordinate)
        (Promotion.physicalWeightInverseLaw geometry coordinate))
      (ℚRing.solve-∀ (state coordinate)))

tiltedPhysicalOperator :
  ∀ {matrix} →
  Promotion.PhysicalCombesThomasGeometry matrix →
  PhysicalOperator
tiltedPhysicalOperator {matrix} geometry =
  CT.diagonalConjugate
    (Promotion.physicalWeight geometry)
    (Promotion.physicalInverseWeight geometry)
    matrix

tiltedHessianStateDualEntryExact :
  ∀ {matrix}
    (geometry : Promotion.PhysicalCombesThomasGeometry matrix)
    left right →
  tiltedPhysicalOperator geometry left right
  ≡ Promotion.physicalWeight geometry left
      * matrix left right
      * Promotion.physicalInverseWeight geometry right
tiltedHessianStateDualEntryExact geometry left right =
  ℚRing.solve []

tiltedHessianDifferenceEntry :
  ∀ {matrix} →
  Promotion.PhysicalCombesThomasGeometry matrix →
  Coordinate → Coordinate → ℚ
tiltedHessianDifferenceEntry {matrix} geometry left right =
  tiltedPhysicalOperator geometry left right - matrix left right

tiltedHessianDifferenceEntryExact :
  ∀ {matrix}
    (geometry : Promotion.PhysicalCombesThomasGeometry matrix)
    left right →
  tiltedHessianDifferenceEntry geometry left right
  ≡
  (Promotion.physicalWeight geometry left
    * Promotion.physicalInverseWeight geometry right
    - 1ℚ)
  * matrix left right
tiltedHessianDifferenceEntryExact {matrix} geometry left right =
  ℚRing.solve-∀
    (Promotion.physicalWeight geometry left)
    (Promotion.physicalInverseWeight geometry right)
    (matrix left right)

tiltedHessianDifferenceSupport :
  ∀ {matrix}
    (geometry : Promotion.PhysicalCombesThomasGeometry matrix)
    left right →
  matrix left right ≡ 0ℚ →
  tiltedHessianDifferenceEntry geometry left right ≡ 0ℚ
tiltedHessianDifferenceSupport geometry left right zeroEntry
  rewrite zeroEntry = ℚRing.solve []

physicalStateDualTiltLevel : ProofLevel
physicalStateDualTiltLevel = machineChecked

physicalTiltDifferenceEntryLevel : ProofLevel
physicalTiltDifferenceEntryLevel = machineChecked
