module DASHI.Physics.YangMills.BalabanP33PhysicalQuadraticToSquaredCoercivityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Augustin-Louis Cauchy, 1821 finite-sum inequality.
-- Hermann Amandus Schwarz, 1888 integral inequality.
-- No DOI applies to these classical results.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Convert the actual quadratic Hessian estimate
--
--   (1/32)||v||^2 <= <v,Hv>
--
-- into the squared operator lower bound required by the square-root-free
-- Combes--Thomas theorem:
--
--   (1/1024)||v||^2 <= ||Hv||^2.
--
-- The proof is the exact finite Cauchy--Schwarz argument on the literal
-- 3072-coordinate carrier.  It handles the zero-norm and positive-norm cases
-- separately, so no division by a possibly zero norm and no spectral theorem
-- is hidden.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; _<_; NonZero; NonNegative; Positive)
import Data.Rational as ℚFull
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2CauchyInverseSquaredExact as Cauchy
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33CombesThomasSquaredHalfGapExact as Squared
import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasSchurExact as PhysicalSchur

PhysicalMatrix : Set
PhysicalMatrix = Physical.PhysicalSU2Matrix4

physicalNormSqNonnegative : ∀ vector →
  0ℚ ≤ Physical.physicalSU2CoordinateNormSq vector
physicalNormSqNonnegative vector =
  Schur.sumNonnegative
    Physical.physicalSU2Coordinates4
    (λ coordinate → FiniteL2.square (vector coordinate))
    (λ coordinate → FiniteL2.squareNonnegative (vector coordinate))

record PhysicalOriginalQuadraticCoercivity
    (hessian : PhysicalMatrix) : Set₁ where
  field
    schurData : PhysicalSchur.PhysicalCombesThomasSchurData hessian

    quadraticLower : ∀ vector →
      P33.p33PhysicalFloor
        * Physical.physicalSU2CoordinateNormSq vector
      ≤ Physical.physicalCoordinateDot vector
          (Physical.physicalMatrixApply hessian vector)

open PhysicalOriginalQuadraticCoercivity public

originalSquaredLowerFromQuadratic :
  ∀ {hessian}
    (coercivity : PhysicalOriginalQuadraticCoercivity hessian)
    vector →
  Squared.p33OriginalGapSquared
    * Physical.physicalSU2CoordinateNormSq vector
  ≤ Physical.physicalSU2CoordinateNormSq
      (Physical.physicalMatrixApply hessian vector)
originalSquaredLowerFromQuadratic {hessian} coercivity vector
  with ℚFull._≟_
    (Physical.physicalSU2CoordinateNormSq vector) 0ℚ
... | yes normZero =
  subst
    (λ coefficient →
      coefficient * Physical.physicalSU2CoordinateNormSq vector
      ≤ Physical.physicalSU2CoordinateNormSq
          (Physical.physicalMatrixApply hessian vector))
    (sym Squared.p33OriginalGapSquaredIsOneOverThirtyTwoSquared)
    (Cauchy.coercivityGivesZeroInputInverseSquaredBound
      P33.p33PhysicalFloor
      (Physical.physicalSU2CoordinateNormSq vector)
      (Physical.physicalSU2CoordinateNormSq
        (Physical.physicalMatrixApply hessian vector))
      normZero
      (physicalNormSqNonnegative
        (Physical.physicalMatrixApply hessian vector)))
... | no normNonzero =
  let
    normValue = Physical.physicalSU2CoordinateNormSq vector

    normNonnegative : 0ℚ ≤ normValue
    normNonnegative = physicalNormSqNonnegative vector

    instance
      normNN : NonNegative normValue
      normNN = ℚ.nonNegative normNonnegative

      normNZ : NonZero normValue
      normNZ = ℚ.≢-nonZero normNonzero

      normPositiveInstance : Positive normValue
      normPositiveInstance = ℚP.nonNeg∧nonZero⇒pos normValue

    normPositive : 0ℚ < normValue
    normPositive = ℚP.positive⁻¹ normValue

    squared :
      (P33.p33PhysicalFloor * P33.p33PhysicalFloor) * normValue
      ≤ Physical.physicalSU2CoordinateNormSq
          (Physical.physicalMatrixApply hessian vector)
    squared =
      Cauchy.coercivityGivesPositiveInputInverseSquaredBound
        P33.p33PhysicalFloor
        normValue
        (Physical.physicalSU2CoordinateNormSq
          (Physical.physicalMatrixApply hessian vector))
        (Physical.physicalCoordinateDot vector
          (Physical.physicalMatrixApply hessian vector))
        (ℚP.nonNegative⁻¹ P33.p33PhysicalFloor)
        normPositive
        (physicalNormSqNonnegative
          (Physical.physicalMatrixApply hessian vector))
        (quadraticLower coercivity vector)
        (Cauchy.physicalCoordinateCauchySchwarzSquared
          vector (Physical.physicalMatrixApply hessian vector))
  in
  subst
    (λ coefficient →
      coefficient * normValue
      ≤ Physical.physicalSU2CoordinateNormSq
          (Physical.physicalMatrixApply hessian vector))
    (sym Squared.p33OriginalGapSquaredIsOneOverThirtyTwoSquared)
    squared

physicalOriginalSquaredCoercivityFromQuadratic :
  ∀ {hessian} →
  PhysicalOriginalQuadraticCoercivity hessian →
  PhysicalSchur.PhysicalOriginalSquaredCoercivity hessian
physicalOriginalSquaredCoercivityFromQuadratic coercivity = record
  { schurData = schurData coercivity
  ; originalSquaredLower = originalSquaredLowerFromQuadratic coercivity
  }

physicalQuadraticToSquaredCoercivityLevel : ProofLevel
physicalQuadraticToSquaredCoercivityLevel = machineChecked

physicalZeroNormBranchLevel : ProofLevel
physicalZeroNormBranchLevel = machineChecked

physicalPositiveNormBranchLevel : ProofLevel
physicalPositiveNormBranchLevel = machineChecked
