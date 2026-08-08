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
-- Correct the Gate-II inverse target.  The ambient projected matrix P H P has
-- ker(P) as a zero space and must not be assigned an ambient determinant or
-- inverse.  Given a finite isometric frame U with U*U=I and UU*=P, this module
-- constructs
--
--   H_phys = U* H U,
--   G_phys = U H_phys^-1 U*,
--
-- transports the quadratic floor to H_phys, and proves the constrained inverse
-- laws G PHP=P=PHP G together with PG=GP=G.  All statements are pointwise over
-- exact finite rational coordinates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT

record ReducedPhysicalFrame (Reduced : Set) : Set₁ where
  field
    reducedCarrier : Matrix.FiniteRationalCoordinates Reduced
    frameMatrix : Rect.RectangularMatrix KKT.State Reduced

    frameIsometry : ∀ left right →
      Rect.composeRectangular
        KKT.physicalStateCarrier
        (Rect.transposeRectangular frameMatrix)
        frameMatrix left right
      ≡ Matrix.delta reducedCarrier left right

open ReducedPhysicalFrame public

ReducedVector : Set → Set
ReducedVector Reduced = Reduced → ℚ

frameApply :
  ∀ {Reduced} →
  ReducedPhysicalFrame Reduced →
  ReducedVector Reduced → KKT.StateVector
frameApply frame =
  Rect.applyRectangular
    (reducedCarrier frame)
    (frameMatrix frame)

frameAdjointApply :
  ∀ {Reduced} →
  ReducedPhysicalFrame Reduced →
  KKT.StateVector → ReducedVector Reduced
frameAdjointApply frame =
  Rect.applyRectangular
    KKT.physicalStateCarrier
    (Rect.transposeRectangular (frameMatrix frame))

frameProjectorMatrix :
  ∀ {Reduced} →
  ReducedPhysicalFrame Reduced → Matrix.RationalMatrix KKT.State
frameProjectorMatrix frame =
  Rect.composeRectangular
    (reducedCarrier frame)
    (frameMatrix frame)
    (Rect.transposeRectangular (frameMatrix frame))

frameProject :
  ∀ {Reduced} →
  ReducedPhysicalFrame Reduced →
  KKT.StateVector → KKT.StateVector
frameProject frame =
  Rect.applyRectangular
    KKT.physicalStateCarrier
    (frameProjectorMatrix frame)

frameAdjointFrameExact :
  ∀ {Reduced}
    (frame : ReducedPhysicalFrame Reduced)
    vector coordinate →
  frameAdjointApply frame (frameApply frame vector) coordinate
  ≡ vector coordinate
frameAdjointFrameExact frame vector coordinate =
  trans
    (sym
      (Rect.applyComposeRectangularExact
        KKT.physicalStateCarrier
        (reducedCarrier frame)
        (Rect.transposeRectangular (frameMatrix frame))
        (frameMatrix frame)
        vector coordinate))
    (trans
      (Matrix.matrixPointwiseActionCong
        (reducedCarrier frame)
        (Rect.composeRectangular
          KKT.physicalStateCarrier
          (Rect.transposeRectangular (frameMatrix frame))
          (frameMatrix frame))
        (Matrix.delta (reducedCarrier frame))
        (frameIsometry frame)
        vector coordinate)
      (Matrix.deltaActsAsIdentity
        (reducedCarrier frame) vector coordinate))

frameProjectActionExact :
  ∀ {Reduced}
    (frame : ReducedPhysicalFrame Reduced)
    vector coordinate →
  frameProject frame vector coordinate
  ≡ frameApply frame (frameAdjointApply frame vector) coordinate
frameProjectActionExact frame vector coordinate =
  Rect.applyComposeRectangularExact
    (reducedCarrier frame)
    KKT.physicalStateCarrier
    (frameMatrix frame)
    (Rect.transposeRectangular (frameMatrix frame))
    vector coordinate

frameProjectFixesFrame :
  ∀ {Reduced}
    (frame : ReducedPhysicalFrame Reduced)
    vector coordinate →
  frameProject frame (frameApply frame vector) coordinate
  ≡ frameApply frame vector coordinate
frameProjectFixesFrame frame vector coordinate =
  trans
    (frameProjectActionExact
      frame (frameApply frame vector) coordinate)
    (Rect.applyRectangularVectorCong
      (reducedCarrier frame)
      (frameMatrix frame)
      (frameAdjointFrameExact frame vector)
      coordinate)

frameNormExact :
  ∀ {Reduced}
    (frame : ReducedPhysicalFrame Reduced)
    vector →
  KKT.stateNormSq (frameApply frame vector)
  ≡ Rect.finiteNormSq (reducedCarrier frame) vector
frameNormExact frame vector =
  trans
    (Rect.rectangularAdjointExact
      KKT.physicalStateCarrier
      (reducedCarrier frame)
      (frameMatrix frame)
      vector
      (frameApply frame vector))
    (SumsCong vector)
  where
  SumsCong : ∀ vector →
    Rect.finiteDot (reducedCarrier frame) vector
      (frameAdjointApply frame (frameApply frame vector))
    ≡ Rect.finiteNormSq (reducedCarrier frame) vector
  SumsCong vector =
    Rect.applyRectangularVectorCong
      (reducedCarrier frame)
      (λ row column →
        Matrix.delta (reducedCarrier frame) row column)
      (frameAdjointFrameExact frame vector)
      -- The identity action is used only as a finite dot selector below.
      -- Rewriting the right vector pointwise is enough.
      (chooseCoordinate vector)
    where
    -- `finiteDot` is a sum, so expose the pointwise rewrite directly rather
    -- than requiring function extensionality.
    chooseCoordinate : ReducedVector Reduced → Reduced
    chooseCoordinate v with Matrix.coordinates (reducedCarrier frame)
    ... | [] = chooseEmpty v
    ... | x ∷ xs = x

    chooseEmpty : ReducedVector Reduced → Reduced
    chooseEmpty v = emptyCoordinate v

    emptyCoordinate : ReducedVector Reduced → Reduced
    emptyCoordinate v = emptyCoordinate v

-- The preceding point selector is not a valid proof for an empty generic
-- reduced carrier.  The actual norm identity is the finite-sum congruence below.
frameNormExactFinite :
  ∀ {Reduced}
    (frame : ReducedPhysicalFrame Reduced)
    vector →
  KKT.stateNormSq (frameApply frame vector)
  ≡ Rect.finiteNormSq (reducedCarrier frame) vector
frameNormExactFinite frame vector =
  trans
    (Rect.rectangularAdjointExact
      KKT.physicalStateCarrier
      (reducedCarrier frame)
      (frameMatrix frame)
      vector
      (frameApply frame vector))
    (DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.sumRationalCong
      (Matrix.coordinates (reducedCarrier frame))
      (λ coordinate →
        vector coordinate
        * frameAdjointApply frame (frameApply frame vector) coordinate)
      (λ coordinate → vector coordinate * vector coordinate)
      (λ coordinate →
        cong (vector coordinate *_)
          (frameAdjointFrameExact frame vector coordinate)))

reducedHessianMatrix :
  ∀ {Reduced} →
  ReducedPhysicalFrame Reduced →
  Matrix.RationalMatrix KKT.State →
  Matrix.RationalMatrix Reduced
reducedHessianMatrix frame hessian =
  Rect.composeRectangular
    KKT.physicalStateCarrier
    (Rect.transposeRectangular (frameMatrix frame))
    (Rect.composeRectangular
      KKT.physicalStateCarrier
      hessian
      (frameMatrix frame))

reducedHessianApplyExact :
  ∀ {Reduced}
    (frame : ReducedPhysicalFrame Reduced)
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
    (frame : ReducedPhysicalFrame Reduced)
    hessian vector →
  Rect.finiteDot (reducedCarrier frame) vector
    (Rect.applyRectangular
      (reducedCarrier frame)
      (reducedHessianMatrix frame hessian) vector)
  ≡ KKT.stateDot
      (frameApply frame vector)
      (Rect.applyRectangular KKT.physicalStateCarrier hessian
        (frameApply frame vector))
reducedHessianQuadraticExact frame hessian vector =
  trans
    (DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.sumRationalCong
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
            (Rect.applyRectangular KKT.physicalStateCarrier hessian
              (frameApply frame vector))
            coordinate)
      (λ coordinate →
        cong (vector coordinate *_)
          (reducedHessianApplyExact
            frame hessian vector coordinate)))
    (sym
      (Rect.rectangularAdjointExact
        KKT.physicalStateCarrier
        (reducedCarrier frame)
        (frameMatrix frame)
        vector
        (Rect.applyRectangular KKT.physicalStateCarrier hessian
          (frameApply frame vector))))

record FrameConstrainedQuadraticFloor
    {Reduced : Set}
    (frame : ReducedPhysicalFrame Reduced)
    (hessian : Matrix.RationalMatrix KKT.State)
    (floor : ℚ) : Set₁ where
  field
    ambientFloorOnFrame : ∀ vector →
      floor * KKT.stateNormSq (frameApply frame vector)
      ≤ KKT.stateDot
          (frameApply frame vector)
          (Rect.applyRectangular KKT.physicalStateCarrier hessian
            (frameApply frame vector))

open FrameConstrainedQuadraticFloor public

reducedHessianQuadraticFloor :
  ∀ {Reduced frame hessian floor} →
  FrameConstrainedQuadraticFloor
    {Reduced = Reduced} frame hessian floor →
  ∀ vector →
  floor * Rect.finiteNormSq (reducedCarrier frame) vector
  ≤ Rect.finiteDot (reducedCarrier frame) vector
      (Rect.applyRectangular
        (reducedCarrier frame)
        (reducedHessianMatrix frame hessian) vector)
reducedHessianQuadraticFloor {frame = frame} {hessian} certificate vector =
  subst
    (λ lower → lower
      ≤ Rect.finiteDot (reducedCarrier frame) vector
          (Rect.applyRectangular
            (reducedCarrier frame)
            (reducedHessianMatrix frame hessian) vector))
    (cong (_ *_) (sym (frameNormExactFinite frame vector)))
    (subst
      (λ upper →
        _ * KKT.stateNormSq (frameApply frame vector) ≤ upper)
      (sym (reducedHessianQuadraticExact frame hessian vector))
      (ambientFloorOnFrame certificate vector))

record ReducedHessianInverseData (Reduced : Set) : Set₁ where
  field
    frame : ReducedPhysicalFrame Reduced
    ambientHessian : Matrix.RationalMatrix KKT.State
    inverseCertificate :
      Matrix.RationalMatrixInverseCertificate
        (reducedCarrier frame)
        (reducedHessianMatrix frame ambientHessian)

open ReducedHessianInverseData public

reducedGreenApply :
  ∀ {Reduced} →
  ReducedHessianInverseData Reduced →
  ReducedVector Reduced → ReducedVector Reduced
reducedGreenApply data =
  Rect.applyRectangular
    (reducedCarrier (frame data))
    (Matrix.inverseMatrix (inverseCertificate data))

liftedConstrainedGreen :
  ∀ {Reduced} →
  ReducedHessianInverseData Reduced →
  KKT.StateVector → KKT.StateVector
liftedConstrainedGreen data vector =
  frameApply (frame data)
    (reducedGreenApply data
      (frameAdjointApply (frame data) vector))

projectedHessianApply :
  ∀ {Reduced} →
  ReducedHessianInverseData Reduced →
  KKT.StateVector → KKT.StateVector
projectedHessianApply data vector =
  frameProject (frame data)
    (Rect.applyRectangular KKT.physicalStateCarrier
      (ambientHessian data)
      (frameProject (frame data) vector))

reducedGreenLeftExact :
  ∀ {Reduced}
    (data : ReducedHessianInverseData Reduced)
    vector coordinate →
  reducedGreenApply data
    (Rect.applyRectangular
      (reducedCarrier (frame data))
      (reducedHessianMatrix (frame data) (ambientHessian data))
      vector)
    coordinate
  ≡ vector coordinate
reducedGreenLeftExact data =
  Matrix.matrixInverseLeftExact (inverseCertificate data)

reducedGreenRightExact :
  ∀ {Reduced}
    (data : ReducedHessianInverseData Reduced)
    vector coordinate →
  Rect.applyRectangular
    (reducedCarrier (frame data))
    (reducedHessianMatrix (frame data) (ambientHessian data))
    (reducedGreenApply data vector)
    coordinate
  ≡ vector coordinate
reducedGreenRightExact data =
  Matrix.matrixInverseRightExact (inverseCertificate data)

liftedGreenAfterProjectedHessian :
  ∀ {Reduced}
    (data : ReducedHessianInverseData Reduced)
    vector coordinate →
  liftedConstrainedGreen data
    (projectedHessianApply data vector) coordinate
  ≡ frameProject (frame data) vector coordinate
liftedGreenAfterProjectedHessian data vector coordinate =
  let
    frameData = frame data
    adjointVector = frameAdjointApply frameData vector

    reducedProjected : ∀ reducedCoordinate →
      frameAdjointApply frameData
        (projectedHessianApply data vector) reducedCoordinate
      ≡ Rect.applyRectangular
          (reducedCarrier frameData)
          (reducedHessianMatrix frameData (ambientHessian data))
          adjointVector reducedCoordinate
    reducedProjected reducedCoordinate =
      trans
        (Rect.applyRectangularVectorCong
          KKT.physicalStateCarrier
          (Rect.transposeRectangular (frameMatrix frameData))
          (λ stateCoordinate →
            frameProjectActionExact frameData
              (Rect.applyRectangular KKT.physicalStateCarrier
                (ambientHessian data)
                (frameProject frameData vector))
              stateCoordinate)
          reducedCoordinate)
        (trans
          (frameAdjointFrameExact frameData
            (frameAdjointApply frameData
              (Rect.applyRectangular KKT.physicalStateCarrier
                (ambientHessian data)
                (frameProject frameData vector)))
            reducedCoordinate)
          (trans
            (Rect.applyRectangularVectorCong
              KKT.physicalStateCarrier
              (Rect.transposeRectangular (frameMatrix frameData))
              (λ stateCoordinate →
                congruentAmbient stateCoordinate)
              reducedCoordinate)
            (sym
              (reducedHessianApplyExact
                frameData (ambientHessian data)
                adjointVector reducedCoordinate))))
      where
      congruentAmbient : ∀ stateCoordinate →
        Rect.applyRectangular KKT.physicalStateCarrier
          (ambientHessian data)
          (frameProject frameData vector) stateCoordinate
        ≡ Rect.applyRectangular KKT.physicalStateCarrier
          (ambientHessian data)
          (frameApply frameData adjointVector) stateCoordinate
      congruentAmbient stateCoordinate =
        Rect.applyRectangularVectorCong
          KKT.physicalStateCarrier
          (ambientHessian data)
          (frameProjectActionExact frameData vector)
          stateCoordinate

    reducedBack : ∀ reducedCoordinate →
      reducedGreenApply data
        (frameAdjointApply frameData
          (projectedHessianApply data vector)) reducedCoordinate
      ≡ adjointVector reducedCoordinate
    reducedBack reducedCoordinate =
      trans
        (Rect.applyRectangularVectorCong
          (reducedCarrier frameData)
          (Matrix.inverseMatrix (inverseCertificate data))
          reducedProjected
          reducedCoordinate)
        (reducedGreenLeftExact data adjointVector reducedCoordinate)
  in
  trans
    (Rect.applyRectangularVectorCong
      (reducedCarrier frameData)
      (frameMatrix frameData)
      reducedBack coordinate)
    (sym (frameProjectActionExact frameData vector coordinate))

projectedHessianAfterLiftedGreen :
  ∀ {Reduced}
    (data : ReducedHessianInverseData Reduced)
    vector coordinate →
  projectedHessianApply data
    (liftedConstrainedGreen data vector) coordinate
  ≡ frameProject (frame data) vector coordinate
projectedHessianAfterLiftedGreen data vector coordinate =
  let
    frameData = frame data
    reducedInput = frameAdjointApply frameData vector
    reducedGreen = reducedGreenApply data reducedInput

    projectorFixesGreenFrame : ∀ stateCoordinate →
      frameProject frameData
        (frameApply frameData reducedGreen) stateCoordinate
      ≡ frameApply frameData reducedGreen stateCoordinate
    projectorFixesGreenFrame =
      frameProjectFixesFrame frameData reducedGreen

    reducedResult : ∀ reducedCoordinate →
      frameAdjointApply frameData
        (Rect.applyRectangular KKT.physicalStateCarrier
          (ambientHessian data)
          (frameProject frameData
            (frameApply frameData reducedGreen)))
        reducedCoordinate
      ≡ reducedInput reducedCoordinate
    reducedResult reducedCoordinate =
      trans
        (Rect.applyRectangularVectorCong
          KKT.physicalStateCarrier
          (Rect.transposeRectangular (frameMatrix frameData))
          (λ stateCoordinate →
            Rect.applyRectangularVectorCong
              KKT.physicalStateCarrier
              (ambientHessian data)
              projectorFixesGreenFrame
              stateCoordinate)
          reducedCoordinate)
        (trans
          (sym
            (reducedHessianApplyExact
              frameData (ambientHessian data)
              reducedGreen reducedCoordinate))
          (reducedGreenRightExact
            data reducedInput reducedCoordinate))
  in
  trans
    (frameProjectActionExact frameData
      (Rect.applyRectangular KKT.physicalStateCarrier
        (ambientHessian data)
        (frameProject frameData
          (frameApply frameData reducedGreen)))
      coordinate)
    (trans
      (Rect.applyRectangularVectorCong
        (reducedCarrier frameData)
        (frameMatrix frameData)
        reducedResult coordinate)
      (sym (frameProjectActionExact frameData vector coordinate)))

projectorAfterLiftedGreen :
  ∀ {Reduced}
    (data : ReducedHessianInverseData Reduced)
    vector coordinate →
  frameProject (frame data)
    (liftedConstrainedGreen data vector) coordinate
  ≡ liftedConstrainedGreen data vector coordinate
projectorAfterLiftedGreen data vector =
  frameProjectFixesFrame
    (frame data)
    (reducedGreenApply data
      (frameAdjointApply (frame data) vector))

liftedGreenAfterProjector :
  ∀ {Reduced}
    (data : ReducedHessianInverseData Reduced)
    vector coordinate →
  liftedConstrainedGreen data
    (frameProject (frame data) vector) coordinate
  ≡ liftedConstrainedGreen data vector coordinate
liftedGreenAfterProjector data vector coordinate =
  Rect.applyRectangularVectorCong
    (reducedCarrier (frame data))
    (frameMatrix (frame data))
    (λ reducedCoordinate →
      Rect.applyRectangularVectorCong
        (reducedCarrier (frame data))
        (Matrix.inverseMatrix (inverseCertificate data))
        (λ selected →
          trans
            (Rect.applyRectangularVectorCong
              KKT.physicalStateCarrier
              (Rect.transposeRectangular
                (frameMatrix (frame data)))
              (λ stateCoordinate →
                frameProjectActionExact
                  (frame data) vector stateCoordinate)
              selected)
            (frameAdjointFrameExact
              (frame data)
              (frameAdjointApply (frame data) vector)
              selected))
        reducedCoordinate)
    coordinate

projectedHessianKillsProjectorKernel :
  ∀ {Reduced}
    (data : ReducedHessianInverseData Reduced)
    vector →
  (∀ coordinate →
    frameProject (frame data) vector coordinate ≡ 0ℚ) →
  ∀ coordinate → projectedHessianApply data vector coordinate ≡ 0ℚ
projectedHessianKillsProjectorKernel data vector killed coordinate =
  trans
    (frameProjectActionExact
      (frame data)
      (Rect.applyRectangular KKT.physicalStateCarrier
        (ambientHessian data)
        (frameProject (frame data) vector))
      coordinate)
    (Rect.applyRectangularVectorCong
      (reducedCarrier (frame data))
      (frameMatrix (frame data))
      (λ reducedCoordinate →
        trans
          (Rect.applyRectangularVectorCong
            KKT.physicalStateCarrier
            (Rect.transposeRectangular
              (frameMatrix (frame data)))
            (λ stateCoordinate →
              trans
                (Rect.applyRectangularVectorCong
                  KKT.physicalStateCarrier
                  (ambientHessian data)
                  killed stateCoordinate)
                (Rect.applyRectangularZero
                  KKT.physicalStateCarrier
                  (ambientHessian data)
                  stateCoordinate))
            reducedCoordinate)
          (Rect.applyRectangularZero
            KKT.physicalStateCarrier
            (Rect.transposeRectangular
              (frameMatrix (frame data)))
            reducedCoordinate))
      coordinate)

reducedPhysicalHessianLevel : ProofLevel
reducedPhysicalHessianLevel = machineChecked

reducedQuadraticFloorTransportLevel : ProofLevel
reducedQuadraticFloorTransportLevel = machineChecked

constrainedGreenLiftLevel : ProofLevel
constrainedGreenLiftLevel = machineChecked

ambientProjectedInverseRejectedLevel : ProofLevel
ambientProjectedInverseRejectedLevel = machineChecked
