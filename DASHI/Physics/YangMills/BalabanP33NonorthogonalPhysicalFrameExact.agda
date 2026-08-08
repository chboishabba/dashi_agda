module DASHI.Physics.YangMills.BalabanP33NonorthogonalPhysicalFrameExact where

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
-- Avoid a false rational orthonormalisation requirement.  A physical tangent
-- frame is an arbitrary injective rational matrix B whose Gram matrix
--
--   G_B = B* B
--
-- has an exact rational inverse.  The orthogonal projector is
--
--   P_B = B G_B^-1 B*,
--
-- the reduced Hessian is H_B = B* H B, and constrained coercivity is transported
-- as the generalized inequality
--
--   lambda <v,G_B v> <= <v,H_B v>.
--
-- Exact inverse laws for H_B are obtained without square roots or algebraic
-- extensions.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT

ReducedVector : Set → Set
ReducedVector Reduced = Reduced → ℚ

frameGramRaw :
  ∀ {Reduced : Set} →
  Matrix.FiniteRationalCoordinates Reduced →
  Rect.RectangularMatrix KKT.State Reduced →
  Matrix.RationalMatrix Reduced
frameGramRaw reducedCarrier frameMatrix =
  Rect.composeRectangular
    KKT.physicalStateCarrier
    (Rect.transposeRectangular frameMatrix)
    frameMatrix

record NonorthogonalPhysicalFrame (Reduced : Set) : Set₁ where
  field
    reducedCarrier : Matrix.FiniteRationalCoordinates Reduced
    frameMatrix : Rect.RectangularMatrix KKT.State Reduced

    frameGramInverseCertificate :
      Matrix.RationalMatrixInverseCertificate
        reducedCarrier
        (frameGramRaw reducedCarrier frameMatrix)

    frameGramInverseSymmetric : ∀ left right →
      Matrix.inverseMatrix frameGramInverseCertificate left right
      ≡ Matrix.inverseMatrix frameGramInverseCertificate right left

open NonorthogonalPhysicalFrame public

frameConstraintData :
  ∀ {Reduced} →
  NonorthogonalPhysicalFrame Reduced →
  KKT.FiniteKKTProjectorData Reduced
frameConstraintData frame = record
  { KKT.FiniteKKTProjectorData.multiplierCarrier =
      reducedCarrier frame
  ; KKT.FiniteKKTProjectorData.constraintMatrix =
      Rect.transposeRectangular (frameMatrix frame)
  ; KKT.FiniteKKTProjectorData.gramInverseCertificate =
      frameGramInverseCertificate frame
  ; KKT.FiniteKKTProjectorData.gramInverseSymmetric =
      frameGramInverseSymmetric frame
  }

frameApply :
  ∀ {Reduced} →
  NonorthogonalPhysicalFrame Reduced →
  ReducedVector Reduced → KKT.StateVector
frameApply frame =
  Rect.applyRectangular
    (reducedCarrier frame)
    (frameMatrix frame)

frameAdjointApply :
  ∀ {Reduced} →
  NonorthogonalPhysicalFrame Reduced →
  KKT.StateVector → ReducedVector Reduced
frameAdjointApply frame =
  Rect.applyRectangular
    KKT.physicalStateCarrier
    (Rect.transposeRectangular (frameMatrix frame))

frameGram :
  ∀ {Reduced} →
  NonorthogonalPhysicalFrame Reduced →
  Matrix.RationalMatrix Reduced
frameGram frame =
  frameGramRaw (reducedCarrier frame) (frameMatrix frame)

frameGramApply :
  ∀ {Reduced} →
  NonorthogonalPhysicalFrame Reduced →
  ReducedVector Reduced → ReducedVector Reduced
frameGramApply frame =
  Rect.applyRectangular
    (reducedCarrier frame)
    (frameGram frame)

frameGramGreenApply :
  ∀ {Reduced} →
  NonorthogonalPhysicalFrame Reduced →
  ReducedVector Reduced → ReducedVector Reduced
frameGramGreenApply frame =
  Rect.applyRectangular
    (reducedCarrier frame)
    (Matrix.inverseMatrix (frameGramInverseCertificate frame))

recoverFrameCoordinates :
  ∀ {Reduced} →
  NonorthogonalPhysicalFrame Reduced →
  KKT.StateVector → ReducedVector Reduced
recoverFrameCoordinates frame vector =
  frameGramGreenApply frame (frameAdjointApply frame vector)

frameProject :
  ∀ {Reduced} →
  NonorthogonalPhysicalFrame Reduced →
  KKT.StateVector → KKT.StateVector
frameProject frame =
  KKT.selectedConstraintRepair (frameConstraintData frame)

frameProjectActionExact :
  ∀ {Reduced}
    (frame : NonorthogonalPhysicalFrame Reduced)
    vector coordinate →
  frameProject frame vector coordinate
  ≡ frameApply frame (recoverFrameCoordinates frame vector) coordinate
frameProjectActionExact frame vector coordinate = refl

frameAdjointFrameExact :
  ∀ {Reduced}
    (frame : NonorthogonalPhysicalFrame Reduced)
    vector coordinate →
  frameAdjointApply frame (frameApply frame vector) coordinate
  ≡ frameGramApply frame vector coordinate
frameAdjointFrameExact frame =
  KKT.constraintGramActionExact (frameConstraintData frame)

recoverAfterFrame :
  ∀ {Reduced}
    (frame : NonorthogonalPhysicalFrame Reduced)
    vector coordinate →
  recoverFrameCoordinates frame (frameApply frame vector) coordinate
  ≡ vector coordinate
recoverAfterFrame frame vector coordinate =
  trans
    (Rect.applyRectangularVectorCong
      (reducedCarrier frame)
      (Matrix.inverseMatrix (frameGramInverseCertificate frame))
      (frameAdjointFrameExact frame vector)
      coordinate)
    (Matrix.matrixInverseLeftExact
      (frameGramInverseCertificate frame)
      vector coordinate)

frameProjectFixesFrame :
  ∀ {Reduced}
    (frame : NonorthogonalPhysicalFrame Reduced)
    vector coordinate →
  frameProject frame (frameApply frame vector) coordinate
  ≡ frameApply frame vector coordinate
frameProjectFixesFrame frame =
  KKT.repairOfAdjointExact (frameConstraintData frame)

frameProjectIdempotent :
  ∀ {Reduced}
    (frame : NonorthogonalPhysicalFrame Reduced)
    vector coordinate →
  frameProject frame (frameProject frame vector) coordinate
  ≡ frameProject frame vector coordinate
frameProjectIdempotent frame vector coordinate =
  KKT.repairOfAdjointExact
    (frameConstraintData frame)
    (recoverFrameCoordinates frame vector)
    coordinate

frameProjectSelfAdjoint :
  ∀ {Reduced}
    (frame : NonorthogonalPhysicalFrame Reduced)
    left right →
  KKT.stateDot left (frameProject frame right)
  ≡ KKT.stateDot (frameProject frame left) right
frameProjectSelfAdjoint frame =
  KKT.selectedRepairSelfAdjoint (frameConstraintData frame)

frameAdjointProjectExact :
  ∀ {Reduced}
    (frame : NonorthogonalPhysicalFrame Reduced)
    vector coordinate →
  frameAdjointApply frame (frameProject frame vector) coordinate
  ≡ frameAdjointApply frame vector coordinate
frameAdjointProjectExact frame =
  KKT.constraintRepairExact (frameConstraintData frame)

frameNormGramExact :
  ∀ {Reduced}
    (frame : NonorthogonalPhysicalFrame Reduced)
    vector →
  KKT.stateNormSq (frameApply frame vector)
  ≡ Rect.finiteDot (reducedCarrier frame)
      vector (frameGramApply frame vector)
frameNormGramExact frame vector =
  trans
    (Rect.rectangularAdjointExact
      KKT.physicalStateCarrier
      (reducedCarrier frame)
      (frameMatrix frame)
      vector
      (frameApply frame vector))
    (Sums.sumRationalCong
      (Matrix.coordinates (reducedCarrier frame))
      (λ coordinate →
        vector coordinate
        * frameAdjointApply frame (frameApply frame vector) coordinate)
      (λ coordinate →
        vector coordinate * frameGramApply frame vector coordinate)
      (λ coordinate →
        cong (vector coordinate *_)
          (frameAdjointFrameExact frame vector coordinate)))

frameProjectNormContraction :
  ∀ {Reduced}
    (frame : NonorthogonalPhysicalFrame Reduced)
    vector →
  KKT.stateNormSq (frameProject frame vector)
  ≤ KKT.stateNormSq vector
frameProjectNormContraction frame vector =
  let
    data = frameConstraintData frame
    complement = KKT.selectedAdmissibleProject data vector
    complementNN = KKT.stateNormSqNonnegative complement

    repairBelowSum :
      KKT.stateNormSq (frameProject frame vector)
      ≤ KKT.stateNormSq complement
        + KKT.stateNormSq (frameProject frame vector)
    repairBelowSum =
      subst
        (λ lower → lower ≤ KKT.stateNormSq complement
          + KKT.stateNormSq (frameProject frame vector))
        (sym (ℚP.+-identityˡ
          (KKT.stateNormSq (frameProject frame vector))))
        (ℚP.+-mono-≤ complementNN ℚP.≤-refl)
  in
  subst
    (λ upper → KKT.stateNormSq (frameProject frame vector) ≤ upper)
    (sym (KKT.selectedStatePythagorean data vector))
    repairBelowSum

reducedHessianMatrix :
  ∀ {Reduced} →
  NonorthogonalPhysicalFrame Reduced →
  Matrix.RationalMatrix KKT.State →
  Matrix.RationalMatrix Reduced
reducedHessianMatrix frame hessian =
  Rect.composeRectangular
    KKT.physicalStateCarrier
    (Rect.transposeRectangular (frameMatrix frame))
    (Rect.composeRectangular
      KKT.physicalStateCarrier hessian (frameMatrix frame))

reducedHessianApplyExact :
  ∀ {Reduced}
    (frame : NonorthogonalPhysicalFrame Reduced)
    hessian vector coordinate →
  Rect.applyRectangular
    (reducedCarrier frame)
    (reducedHessianMatrix frame hessian)
    vector coordinate
  ≡ frameAdjointApply frame
      (Rect.applyRectangular KKT.physicalStateCarrier hessian
        (frameApply frame vector))
      coordinate
reducedHessianApplyExact frame hessian vector coordinate =
  trans
    (Rect.applyComposeRectangularExact
      KKT.physicalStateCarrier
      (reducedCarrier frame)
      (Rect.transposeRectangular (frameMatrix frame))
      (Rect.composeRectangular
        KKT.physicalStateCarrier hessian (frameMatrix frame))
      vector coordinate)
    (Rect.applyRectangularVectorCong
      KKT.physicalStateCarrier
      (Rect.transposeRectangular (frameMatrix frame))
      (λ stateCoordinate →
        Rect.applyComposeRectangularExact
          KKT.physicalStateCarrier
          (reducedCarrier frame)
          hessian (frameMatrix frame)
          vector stateCoordinate)
      coordinate)

reducedHessianQuadraticExact :
  ∀ {Reduced}
    (frame : NonorthogonalPhysicalFrame Reduced)
    hessian vector →
  Rect.finiteDot (reducedCarrier frame) vector
    (Rect.applyRectangular
      (reducedCarrier frame)
      (reducedHessianMatrix frame hessian) vector)
  ≡ KKT.stateDot
      (frameApply frame vector)
      (Rect.applyRectangular KKT.physicalStateCarrier
        hessian (frameApply frame vector))
reducedHessianQuadraticExact frame hessian vector =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates (reducedCarrier frame))
      (λ coordinate →
        vector coordinate
        * Rect.applyRectangular
            (reducedCarrier frame)
            (reducedHessianMatrix frame hessian)
            vector coordinate)
      (λ coordinate →
        vector coordinate
        * frameAdjointApply frame
            (Rect.applyRectangular KKT.physicalStateCarrier
              hessian (frameApply frame vector)) coordinate)
      (λ coordinate →
        cong (vector coordinate *_)
          (reducedHessianApplyExact frame hessian vector coordinate)))
    (sym
      (Rect.rectangularAdjointExact
        KKT.physicalStateCarrier
        (reducedCarrier frame)
        (frameMatrix frame)
        vector
        (Rect.applyRectangular KKT.physicalStateCarrier
          hessian (frameApply frame vector))))

record GeneralizedFrameQuadraticFloor
    {Reduced : Set}
    (frame : NonorthogonalPhysicalFrame Reduced)
    (hessian : Matrix.RationalMatrix KKT.State)
    (floor : ℚ) : Set₁ where
  field
    ambientFloorOnFrame : ∀ vector →
      floor * KKT.stateNormSq (frameApply frame vector)
      ≤ KKT.stateDot
          (frameApply frame vector)
          (Rect.applyRectangular KKT.physicalStateCarrier
            hessian (frameApply frame vector))

open GeneralizedFrameQuadraticFloor public

reducedHessianGeneralizedFloor :
  ∀ {Reduced frame hessian floor} →
  GeneralizedFrameQuadraticFloor
    {Reduced = Reduced} frame hessian floor →
  ∀ vector →
  floor * Rect.finiteDot (reducedCarrier frame)
      vector (frameGramApply frame vector)
  ≤ Rect.finiteDot (reducedCarrier frame)
      vector
      (Rect.applyRectangular
        (reducedCarrier frame)
        (reducedHessianMatrix frame hessian) vector)
reducedHessianGeneralizedFloor
    {frame = frame} {hessian} {floor = floor} certificate vector =
  subst
    (λ lower → lower ≤ Rect.finiteDot (reducedCarrier frame) vector
      (Rect.applyRectangular (reducedCarrier frame)
        (reducedHessianMatrix frame hessian) vector))
    (cong (floor *_) (sym (frameNormGramExact frame vector)))
    (subst
      (λ upper → floor * KKT.stateNormSq (frameApply frame vector) ≤ upper)
      (sym (reducedHessianQuadraticExact frame hessian vector))
      (ambientFloorOnFrame certificate vector))

record NonorthogonalReducedHessianInverseData
    (Reduced : Set) : Set₁ where
  field
    frame : NonorthogonalPhysicalFrame Reduced
    ambientHessian : Matrix.RationalMatrix KKT.State
    reducedHessianInverseCertificate :
      Matrix.RationalMatrixInverseCertificate
        (reducedCarrier frame)
        (reducedHessianMatrix frame ambientHessian)

open NonorthogonalReducedHessianInverseData public

reducedGreenApply :
  ∀ {Reduced} →
  NonorthogonalReducedHessianInverseData Reduced →
  ReducedVector Reduced → ReducedVector Reduced
reducedGreenApply data =
  Rect.applyRectangular
    (reducedCarrier (frame data))
    (Matrix.inverseMatrix
      (reducedHessianInverseCertificate data))

reducedGreenLeftExact :
  ∀ {Reduced}
    (data : NonorthogonalReducedHessianInverseData Reduced)
    vector coordinate →
  reducedGreenApply data
    (Rect.applyRectangular
      (reducedCarrier (frame data))
      (reducedHessianMatrix (frame data) (ambientHessian data)) vector)
    coordinate
  ≡ vector coordinate
reducedGreenLeftExact data =
  Matrix.matrixInverseLeftExact
    (reducedHessianInverseCertificate data)

reducedGreenRightExact :
  ∀ {Reduced}
    (data : NonorthogonalReducedHessianInverseData Reduced)
    vector coordinate →
  Rect.applyRectangular
    (reducedCarrier (frame data))
    (reducedHessianMatrix (frame data) (ambientHessian data))
    (reducedGreenApply data vector)
    coordinate
  ≡ vector coordinate
reducedGreenRightExact data =
  Matrix.matrixInverseRightExact
    (reducedHessianInverseCertificate data)

nonorthogonalFrameProjectorLevel : ProofLevel
nonorthogonalFrameProjectorLevel = machineChecked

nonorthogonalGeneralizedCoercivityLevel : ProofLevel
nonorthogonalGeneralizedCoercivityLevel = machineChecked

nonorthogonalReducedInverseLevel : ProofLevel
nonorthogonalReducedInverseLevel = machineChecked

selectedPhysicalFrameProducerLevel : ProofLevel
selectedPhysicalFrameProducerLevel = conditional
