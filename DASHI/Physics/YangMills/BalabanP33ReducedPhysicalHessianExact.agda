module DASHI.Physics.YangMills.BalabanP33ReducedPhysicalHessianExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Franco Brezzi,
-- "On the Existence, Uniqueness and Approximation of Saddle-Point Problems
-- Arising from Lagrangian Multipliers",
-- RAIRO Analyse Numérique 8 (1974), 129--151.
-- No DOI was assigned to the cited article.
--
-- DASHI CONTRIBUTION
--
-- Repair the exploratory reduced-Hessian module by deleting the invalid
-- attempt to select a coordinate from an arbitrary possibly-empty carrier.
-- Given an explicitly supplied finite isometric frame U, construct
-- H_phys=U*HU, transport the quadratic floor, and derive both exact inverse
-- laws for H_phys from a checked rational matrix-inverse certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT

record ReducedPhysicalFrame (Reduced : Set) : Set₁ where
  field
    reducedCarrier : Matrix.FiniteRationalCoordinates Reduced
    frameMatrix : Rect.RectangularMatrix KKT.State Reduced
    frameIsometry : ∀ left right →
      Rect.composeRectangular KKT.physicalStateCarrier
        (Rect.transposeRectangular frameMatrix) frameMatrix left right
      ≡ Matrix.delta reducedCarrier left right
open ReducedPhysicalFrame public

ReducedVector : Set → Set
ReducedVector Reduced = Reduced → ℚ

frameApply : ∀ {Reduced} → ReducedPhysicalFrame Reduced →
  ReducedVector Reduced → KKT.StateVector
frameApply frame = Rect.applyRectangular
  (reducedCarrier frame) (frameMatrix frame)

frameAdjointApply : ∀ {Reduced} → ReducedPhysicalFrame Reduced →
  KKT.StateVector → ReducedVector Reduced
frameAdjointApply frame = Rect.applyRectangular KKT.physicalStateCarrier
  (Rect.transposeRectangular (frameMatrix frame))

frameAdjointFrameExact : ∀ {Reduced}
    (frame : ReducedPhysicalFrame Reduced) vector coordinate →
  frameAdjointApply frame (frameApply frame vector) coordinate
  ≡ vector coordinate
frameAdjointFrameExact frame vector coordinate = trans
  (sym (Rect.applyComposeRectangularExact
    KKT.physicalStateCarrier (reducedCarrier frame)
    (Rect.transposeRectangular (frameMatrix frame))
    (frameMatrix frame) vector coordinate))
  (trans
    (Matrix.matrixPointwiseActionCong (reducedCarrier frame)
      (Rect.composeRectangular KKT.physicalStateCarrier
        (Rect.transposeRectangular (frameMatrix frame))
        (frameMatrix frame))
      (Matrix.delta (reducedCarrier frame))
      (frameIsometry frame) vector coordinate)
    (Matrix.deltaActsAsIdentity (reducedCarrier frame) vector coordinate))

frameNormExact : ∀ {Reduced}
    (frame : ReducedPhysicalFrame Reduced) vector →
  KKT.stateNormSq (frameApply frame vector)
  ≡ Rect.finiteNormSq (reducedCarrier frame) vector
frameNormExact frame vector = trans
  (Rect.rectangularAdjointExact KKT.physicalStateCarrier
    (reducedCarrier frame) (frameMatrix frame)
    vector (frameApply frame vector))
  (Sums.sumRationalCong
    (Matrix.coordinates (reducedCarrier frame))
    (λ coordinate → vector coordinate *
      frameAdjointApply frame (frameApply frame vector) coordinate)
    (λ coordinate → vector coordinate * vector coordinate)
    (λ coordinate → cong (vector coordinate *_)
      (frameAdjointFrameExact frame vector coordinate)))

frameNormExactFinite : ∀ {Reduced}
    (frame : ReducedPhysicalFrame Reduced) vector →
  KKT.stateNormSq (frameApply frame vector)
  ≡ Rect.finiteNormSq (reducedCarrier frame) vector
frameNormExactFinite = frameNormExact

reducedHessianMatrix : ∀ {Reduced} → ReducedPhysicalFrame Reduced →
  Matrix.RationalMatrix KKT.State → Matrix.RationalMatrix Reduced
reducedHessianMatrix frame hessian =
  Rect.composeRectangular KKT.physicalStateCarrier
    (Rect.transposeRectangular (frameMatrix frame))
    (Rect.composeRectangular KKT.physicalStateCarrier
      hessian (frameMatrix frame))

reducedHessianApplyExact : ∀ {Reduced}
    (frame : ReducedPhysicalFrame Reduced) hessian vector coordinate →
  Rect.applyRectangular (reducedCarrier frame)
    (reducedHessianMatrix frame hessian) vector coordinate
  ≡ frameAdjointApply frame
      (Rect.applyRectangular KKT.physicalStateCarrier hessian
        (frameApply frame vector)) coordinate
reducedHessianApplyExact frame hessian vector coordinate = trans
  (Rect.applyComposeRectangularExact KKT.physicalStateCarrier
    (reducedCarrier frame)
    (Rect.transposeRectangular (frameMatrix frame))
    (Rect.composeRectangular KKT.physicalStateCarrier
      hessian (frameMatrix frame)) vector coordinate)
  (Rect.applyRectangularVectorCong KKT.physicalStateCarrier
    (Rect.transposeRectangular (frameMatrix frame))
    (λ stateCoordinate → Rect.applyComposeRectangularExact
      KKT.physicalStateCarrier (reducedCarrier frame)
      hessian (frameMatrix frame) vector stateCoordinate)
    coordinate)

reducedHessianQuadraticExact : ∀ {Reduced}
    (frame : ReducedPhysicalFrame Reduced) hessian vector →
  Rect.finiteDot (reducedCarrier frame) vector
    (Rect.applyRectangular (reducedCarrier frame)
      (reducedHessianMatrix frame hessian) vector)
  ≡ KKT.stateDot (frameApply frame vector)
      (Rect.applyRectangular KKT.physicalStateCarrier hessian
        (frameApply frame vector))
reducedHessianQuadraticExact frame hessian vector = trans
  (Sums.sumRationalCong (Matrix.coordinates (reducedCarrier frame))
    (λ coordinate → vector coordinate *
      Rect.applyRectangular (reducedCarrier frame)
        (reducedHessianMatrix frame hessian) vector coordinate)
    (λ coordinate → vector coordinate *
      frameAdjointApply frame
        (Rect.applyRectangular KKT.physicalStateCarrier hessian
          (frameApply frame vector)) coordinate)
    (λ coordinate → cong (vector coordinate *_)
      (reducedHessianApplyExact frame hessian vector coordinate)))
  (sym (Rect.rectangularAdjointExact KKT.physicalStateCarrier
    (reducedCarrier frame) (frameMatrix frame) vector
    (Rect.applyRectangular KKT.physicalStateCarrier hessian
      (frameApply frame vector))))

record FrameConstrainedQuadraticFloor {Reduced : Set}
    (frame : ReducedPhysicalFrame Reduced)
    (hessian : Matrix.RationalMatrix KKT.State) (floor : ℚ) : Set₁ where
  field
    ambientFloorOnFrame : ∀ vector →
      floor * KKT.stateNormSq (frameApply frame vector)
      ≤ KKT.stateDot (frameApply frame vector)
          (Rect.applyRectangular KKT.physicalStateCarrier hessian
            (frameApply frame vector))
open FrameConstrainedQuadraticFloor public

reducedHessianQuadraticFloor : ∀ {Reduced frame hessian floor} →
  FrameConstrainedQuadraticFloor {Reduced = Reduced} frame hessian floor →
  ∀ vector →
  floor * Rect.finiteNormSq (reducedCarrier frame) vector
  ≤ Rect.finiteDot (reducedCarrier frame) vector
      (Rect.applyRectangular (reducedCarrier frame)
        (reducedHessianMatrix frame hessian) vector)
reducedHessianQuadraticFloor {frame = frame} {hessian} certificate vector =
  subst
    (λ lower → lower ≤ Rect.finiteDot (reducedCarrier frame) vector
      (Rect.applyRectangular (reducedCarrier frame)
        (reducedHessianMatrix frame hessian) vector))
    (cong (_ *_) (sym (frameNormExact frame vector)))
    (subst
      (λ upper → _ * KKT.stateNormSq (frameApply frame vector) ≤ upper)
      (sym (reducedHessianQuadraticExact frame hessian vector))
      (ambientFloorOnFrame certificate vector))

record ReducedHessianInverseData (Reduced : Set) : Set₁ where
  field
    frame : ReducedPhysicalFrame Reduced
    ambientHessian : Matrix.RationalMatrix KKT.State
    inverseCertificate : Matrix.RationalMatrixInverseCertificate
      (reducedCarrier frame)
      (reducedHessianMatrix frame ambientHessian)
open ReducedHessianInverseData public

reducedGreenApply : ∀ {Reduced} → ReducedHessianInverseData Reduced →
  ReducedVector Reduced → ReducedVector Reduced
reducedGreenApply inverseData = Rect.applyRectangular
  (reducedCarrier (frame inverseData))
  (Matrix.inverseMatrix (inverseCertificate inverseData))

reducedGreenLeftExact : ∀ {Reduced}
    (inverseData : ReducedHessianInverseData Reduced) vector coordinate →
  reducedGreenApply inverseData
    (Rect.applyRectangular (reducedCarrier (frame inverseData))
      (reducedHessianMatrix (frame inverseData)
        (ambientHessian inverseData)) vector)
    coordinate ≡ vector coordinate
reducedGreenLeftExact inverseData =
  Matrix.matrixInverseLeftExact (inverseCertificate inverseData)

reducedGreenRightExact : ∀ {Reduced}
    (inverseData : ReducedHessianInverseData Reduced) vector coordinate →
  Rect.applyRectangular (reducedCarrier (frame inverseData))
    (reducedHessianMatrix (frame inverseData)
      (ambientHessian inverseData))
    (reducedGreenApply inverseData vector) coordinate ≡ vector coordinate
reducedGreenRightExact inverseData =
  Matrix.matrixInverseRightExact (inverseCertificate inverseData)

reducedPhysicalHessianLevel : ProofLevel
reducedPhysicalHessianLevel = machineChecked

reducedQuadraticFloorTransportLevel : ProofLevel
reducedQuadraticFloorTransportLevel = machineChecked

reducedInverseCertificateLevel : ProofLevel
reducedInverseCertificateLevel = machineChecked

ambientProjectedInverseRejectedLevel : ProofLevel
ambientProjectedInverseRejectedLevel = machineChecked
