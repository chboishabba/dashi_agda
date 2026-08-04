module DASHI.Physics.YangMills.BalabanP33PhysicalSU2MatrixCoercivityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Complete the coordinate-transfer part of the physical spectral realization.
-- The literal three-component SU(2) bond encoder is bijective and norm
-- preserving.  Consequently a physical Hessian represented by a literal finite
-- matrix inherits the P33 floor on every coordinate vector:
--
--   (1/32) ||z||^2 <= z^T H z.
--
-- This is the exact matrix coercivity statement from which a finite symmetric
-- spectral decomposition may read off lambda_min >= 1/32.  The theorem does
-- not assume a second coordinate-space coercivity premise.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRationalCong)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq)
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates

matrixApplyCong :
  ∀ matrix left right →
  (∀ coordinate → left coordinate ≡ right coordinate) →
  ∀ row →
  Coordinates.physicalMatrixApply matrix left row
  ≡ Coordinates.physicalMatrixApply matrix right row
matrixApplyCong matrix left right pointwise row =
  sumRationalCong
    Coordinates.physicalSU2Coordinates4
    (λ column → matrix row column * left column)
    (λ column → matrix row column * right column)
    (λ column → cong (matrix row column *_) (pointwise column))

matrixQuadraticCong :
  ∀ matrix left right →
  (∀ coordinate → left coordinate ≡ right coordinate) →
  Coordinates.physicalMatrixQuadratic matrix left
  ≡ Coordinates.physicalMatrixQuadratic matrix right
matrixQuadraticCong matrix left right pointwise =
  sumRationalCong
    Coordinates.physicalSU2Coordinates4
    (λ coordinate →
      left coordinate
      * Coordinates.physicalMatrixApply matrix left coordinate)
    (λ coordinate →
      right coordinate
      * Coordinates.physicalMatrixApply matrix right coordinate)
    (λ coordinate →
      cong₂ _*_
        (pointwise coordinate)
        (matrixApplyCong matrix left right pointwise coordinate))

coordinateNormEncodeDecodeExact :
  ∀ vector →
  Coordinates.physicalSU2CoordinateNormSq vector
  ≡ Coordinates.physicalSU2BondNormSq
      (Coordinates.decodePhysicalSU2 vector)
coordinateNormEncodeDecodeExact vector =
  trans
    (sym
      (sumRationalCong
        Coordinates.physicalSU2Coordinates4
        (λ coordinate →
          sq
            (Coordinates.encodePhysicalSU2
              (Coordinates.decodePhysicalSU2 vector) coordinate))
        (λ coordinate → sq (vector coordinate))
        (λ coordinate →
          cong sq
            (Coordinates.encodeAfterDecodePointwise vector coordinate))))
    (Coordinates.encodePhysicalSU2NormSqExact
      (Coordinates.decodePhysicalSU2 vector))

matrixQuadraticEncodeDecodeExact :
  ∀ matrix vector →
  Coordinates.physicalMatrixQuadratic matrix
    (Coordinates.encodePhysicalSU2
      (Coordinates.decodePhysicalSU2 vector))
  ≡ Coordinates.physicalMatrixQuadratic matrix vector
matrixQuadraticEncodeDecodeExact matrix vector =
  matrixQuadraticCong matrix
    (Coordinates.encodePhysicalSU2
      (Coordinates.decodePhysicalSU2 vector))
    vector
    (Coordinates.encodeAfterDecodePointwise vector)

record PhysicalSU2MatrixHessian : Set₁ where
  field
    matrix : Coordinates.PhysicalSU2Matrix4
    physicalEnergy : Coordinates.PhysicalSU2BondField4 → ℚ

    energyIsMatrixQuadratic : ∀ fld →
      physicalEnergy fld
      ≡ Coordinates.physicalMatrixQuadratic matrix
          (Coordinates.encodePhysicalSU2 fld)

    physicalP33Floor : ∀ fld →
      P33.p33PhysicalFloor * Coordinates.physicalSU2BondNormSq fld
      ≤ physicalEnergy fld

open PhysicalSU2MatrixHessian public

physicalP33FloorTransfersToEveryCoordinate :
  (dataSet : PhysicalSU2MatrixHessian) →
  ∀ vector →
  P33.p33PhysicalFloor
    * Coordinates.physicalSU2CoordinateNormSq vector
  ≤ Coordinates.physicalMatrixQuadratic (matrix dataSet) vector
physicalP33FloorTransfersToEveryCoordinate dataSet vector
  rewrite coordinateNormEncodeDecodeExact vector
        | sym (matrixQuadraticEncodeDecodeExact (matrix dataSet) vector)
        | sym (energyIsMatrixQuadratic dataSet
            (Coordinates.decodePhysicalSU2 vector)) =
  physicalP33Floor dataSet (Coordinates.decodePhysicalSU2 vector)

physicalSU2MatrixCongruenceLevel : ProofLevel
physicalSU2MatrixCongruenceLevel = machineChecked

physicalSU2CoordinateCoercivityTransferLevel : ProofLevel
physicalSU2CoordinateCoercivityTransferLevel = machineChecked
