module DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockInverseExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Franco Brezzi,
-- "On the Existence, Uniqueness and Approximation of Saddle-Point Problems
-- Arising from Lagrangian Multipliers",
-- RAIRO Analyse Numérique 8 (1974), 129--151.
-- No DOI was assigned to the cited article.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Close the finite-dimensional logical gap between a constructed KKT right
-- inverse and a genuine inverse.  Coercivity is required only on ker L, while
-- multiplier uniqueness is required only modulo the retained row redundancy.
-- From these two exact hypotheses we prove
--
--   ker [H L*; L 0] = {0},
--
-- injectivity of the complete block, and hence that the Round-39 right inverse
-- is also a left inverse.  No determinant, dimension count or hidden deletion
-- of redundant rows is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockGreenAlgebraExact as Algebra
import DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockGreenExact as Block

zeroBlock : ∀ {Multiplier} → Block.KKTBlockVector Multiplier
zeroBlock = Block.block (λ _ → 0ℚ) (λ _ → 0ℚ)

record HomogeneousKKTEquations
    {Multiplier : Set}
    (greenData : Algebra.ConstrainedGreenData Multiplier)
    (vector : Block.KKTBlockVector Multiplier) : Set where
  field
    stateEquationZero : ∀ coordinate →
      Block.statePart (Block.applyKKTBlock greenData vector) coordinate
      ≡ 0ℚ
    constraintEquationZero : ∀ row →
      Block.multiplierPart (Block.applyKKTBlock greenData vector) row
      ≡ 0ℚ
open HomogeneousKKTEquations public

record ReducedKKTCoercivity
    {Multiplier : Set}
    (greenData : Algebra.ConstrainedGreenData Multiplier) : Set₁ where
  field
    kernelQuadraticZeroForcesStateZero : ∀ state →
      (∀ row →
        KKT.constraintApply (Algebra.projectorData greenData) state row
        ≡ 0ℚ) →
      KKT.stateDot state (Algebra.hessianApply greenData state) ≡ 0ℚ →
      ∀ coordinate → state coordinate ≡ 0ℚ

    reducedMultiplierAdjointInjective : ∀ multiplier →
      (∀ coordinate →
        KKT.constraintAdjointApply
          (Algebra.projectorData greenData) multiplier coordinate
        ≡ 0ℚ) →
      ∀ row → multiplier row ≡ 0ℚ
open ReducedKKTCoercivity public

stateDotRightPointwiseCong :
  ∀ {left right : KKT.StateVector} →
  (∀ coordinate → left coordinate ≡ right coordinate) →
  ∀ vector →
  KKT.stateDot vector left ≡ KKT.stateDot vector right
stateDotRightPointwiseCong {left} {right} pointwise vector =
  Sums.sumRationalCong
    (Matrix.coordinates KKT.physicalStateCarrier)
    (λ coordinate → vector coordinate * left coordinate)
    (λ coordinate → vector coordinate * right coordinate)
    (λ coordinate → cong (vector coordinate *_) (pointwise coordinate))

constraintPartOfHomogeneous :
  ∀ {Multiplier}
    {greenData : Algebra.ConstrainedGreenData Multiplier}
    {vector : Block.KKTBlockVector Multiplier} →
  HomogeneousKKTEquations greenData vector →
  ∀ row →
  KKT.constraintApply (Algebra.projectorData greenData)
    (Block.statePart vector) row ≡ 0ℚ
constraintPartOfHomogeneous homogeneous =
  constraintEquationZero homogeneous

stateEquationExpanded :
  ∀ {Multiplier}
    {greenData : Algebra.ConstrainedGreenData Multiplier}
    {vector : Block.KKTBlockVector Multiplier} →
  HomogeneousKKTEquations greenData vector →
  ∀ coordinate →
  Algebra.hessianApply greenData (Block.statePart vector) coordinate
  + KKT.constraintAdjointApply (Algebra.projectorData greenData)
      (Block.multiplierPart vector) coordinate
  ≡ 0ℚ
stateEquationExpanded homogeneous = stateEquationZero homogeneous

constraintAdjointPairingZero :
  ∀ {Multiplier}
    {greenData : Algebra.ConstrainedGreenData Multiplier}
    {vector : Block.KKTBlockVector Multiplier} →
  HomogeneousKKTEquations greenData vector →
  KKT.stateDot (Block.statePart vector)
    (KKT.constraintAdjointApply (Algebra.projectorData greenData)
      (Block.multiplierPart vector))
  ≡ 0ℚ
constraintAdjointPairingZero {greenData = greenData} {vector = vector}
    homogeneous =
  trans
    (sym
      (Rect.rectangularAdjointExact
        (KKT.multiplierCarrier (Algebra.projectorData greenData))
        KKT.physicalStateCarrier
        (KKT.constraintMatrix (Algebra.projectorData greenData))
        (Block.statePart vector)
        (Block.multiplierPart vector)))
    (trans
      (Sums.sumRationalCong
        (Matrix.coordinates
          (KKT.multiplierCarrier (Algebra.projectorData greenData)))
        (λ row →
          KKT.constraintApply (Algebra.projectorData greenData)
            (Block.statePart vector) row
          * Block.multiplierPart vector row)
        (λ _ → 0ℚ)
        (λ row → trans
          (cong (_* Block.multiplierPart vector row)
            (constraintPartOfHomogeneous homogeneous row))
          (ℚRing.solve-∀ (Block.multiplierPart vector row))))
      (DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact.sumRationalZero
        (Matrix.coordinates
          (KKT.multiplierCarrier (Algebra.projectorData greenData)))))

homogeneousStateQuadraticZero :
  ∀ {Multiplier}
    {greenData : Algebra.ConstrainedGreenData Multiplier}
    {vector : Block.KKTBlockVector Multiplier} →
  HomogeneousKKTEquations greenData vector →
  KKT.stateDot (Block.statePart vector)
    (Algebra.hessianApply greenData (Block.statePart vector))
  ≡ 0ℚ
homogeneousStateQuadraticZero {greenData = greenData} {vector = vector}
    homogeneous =
  let
    state = Block.statePart vector
    multiplier = Block.multiplierPart vector
    dotFullZero :
      KKT.stateDot state
        (Rect.vectorAdd
          (Algebra.hessianApply greenData state)
          (KKT.constraintAdjointApply
            (Algebra.projectorData greenData) multiplier))
      ≡ 0ℚ
    dotFullZero = trans
      (stateDotRightPointwiseCong
        (stateEquationExpanded homogeneous) state)
      (Rect.finiteDotZeroRight KKT.physicalStateCarrier state)

    dotSplit = Rect.finiteDotAddRight
      KKT.physicalStateCarrier state
      (Algebra.hessianApply greenData state)
      (KKT.constraintAdjointApply
        (Algebra.projectorData greenData) multiplier)
  in
  trans
    (sym (ℚRing.solve-∀
      (KKT.stateDot state (Algebra.hessianApply greenData state))
      (KKT.stateDot state
        (KKT.constraintAdjointApply
          (Algebra.projectorData greenData) multiplier))))
    (trans
      (cong
        (λ selected → selected
          - KKT.stateDot state
              (KKT.constraintAdjointApply
                (Algebra.projectorData greenData) multiplier))
        (trans (sym dotSplit) dotFullZero))
      (trans
        (cong
          (λ selected → 0ℚ - selected)
          (constraintAdjointPairingZero homogeneous))
        (ℚRing.solve [])))

finiteKKTHomogeneousStateZero :
  ∀ {Multiplier}
    {greenData : Algebra.ConstrainedGreenData Multiplier} →
  ReducedKKTCoercivity greenData →
  ∀ {vector} →
  HomogeneousKKTEquations greenData vector →
  ∀ coordinate → Block.statePart vector coordinate ≡ 0ℚ
finiteKKTHomogeneousStateZero control homogeneous =
  kernelQuadraticZeroForcesStateZero control
    _
    (constraintPartOfHomogeneous homogeneous)
    (homogeneousStateQuadraticZero homogeneous)

finiteKKTHomogeneousReducedMultiplierZero :
  ∀ {Multiplier}
    {greenData : Algebra.ConstrainedGreenData Multiplier} →
  ReducedKKTCoercivity greenData →
  ∀ {vector} →
  HomogeneousKKTEquations greenData vector →
  ∀ row → Block.multiplierPart vector row ≡ 0ℚ
finiteKKTHomogeneousReducedMultiplierZero
    {greenData = greenData} control {vector} homogeneous =
  let
    stateZero = finiteKKTHomogeneousStateZero control homogeneous
    adjointZero : ∀ coordinate →
      KKT.constraintAdjointApply (Algebra.projectorData greenData)
        (Block.multiplierPart vector) coordinate ≡ 0ℚ
    adjointZero coordinate =
      trans
        (sym
          (ℚRing.solve-∀
            (Algebra.hessianApply greenData
              (Block.statePart vector) coordinate)
            (KKT.constraintAdjointApply
              (Algebra.projectorData greenData)
              (Block.multiplierPart vector) coordinate)))
        (trans
          (cong
            (λ selected →
              selected
              - Algebra.hessianApply greenData
                  (Block.statePart vector) coordinate)
            (stateEquationExpanded homogeneous coordinate))
          (trans
            (cong
              (λ selected → 0ℚ - selected)
              (trans
                (Algebra.hessianPointwiseCong greenData stateZero coordinate)
                (Rect.applyRectangularZero
                  KKT.physicalStateCarrier
                  (Algebra.hessianMatrix greenData) coordinate)))
            (ℚRing.solve [])))
  in
  reducedMultiplierAdjointInjective control
    (Block.multiplierPart vector) adjointZero

finiteKKTKernelTrivial :
  ∀ {Multiplier}
    {greenData : Algebra.ConstrainedGreenData Multiplier} →
  ReducedKKTCoercivity greenData →
  ∀ {vector} →
  HomogeneousKKTEquations greenData vector →
  Block.PointwiseKKTBlockEquality vector zeroBlock
finiteKKTKernelTrivial control homogeneous = record
  { Block.PointwiseKKTBlockEquality.stateEqual =
      finiteKKTHomogeneousStateZero control homogeneous
  ; Block.PointwiseKKTBlockEquality.multiplierEqual =
      finiteKKTHomogeneousReducedMultiplierZero control homogeneous }

blockSubtract : ∀ {Multiplier} →
  Block.KKTBlockVector Multiplier → Block.KKTBlockVector Multiplier →
  Block.KKTBlockVector Multiplier
blockSubtract left right = Block.block
  (Rect.vectorSubtract (Block.statePart left) (Block.statePart right))
  (Rect.vectorSubtract (Block.multiplierPart left) (Block.multiplierPart right))

blockApplyDifferenceHomogeneous :
  ∀ {Multiplier}
    {greenData : Algebra.ConstrainedGreenData Multiplier}
    {left right : Block.KKTBlockVector Multiplier} →
  Block.PointwiseKKTBlockEquality
    (Block.applyKKTBlock greenData left)
    (Block.applyKKTBlock greenData right) →
  HomogeneousKKTEquations greenData (blockSubtract left right)
blockApplyDifferenceHomogeneous {greenData = greenData} {left} {right}
    equality = record
  { stateEquationZero = λ coordinate →
      trans
        (cong₂ _+_
          (Algebra.hessianPointwiseCong greenData
            (λ selected → refl) coordinate)
          (Rect.applyRectangularSubtract
            (KKT.multiplierCarrier (Algebra.projectorData greenData))
            (Rect.transposeRectangular
              (KKT.constraintMatrix (Algebra.projectorData greenData)))
            (Block.multiplierPart left) (Block.multiplierPart right)
            coordinate))
        (trans
          (sym
            (ℚRing.solve-∀
              (Algebra.hessianApply greenData (Block.statePart left) coordinate)
              (KKT.constraintAdjointApply
                (Algebra.projectorData greenData)
                (Block.multiplierPart left) coordinate)
              (Algebra.hessianApply greenData (Block.statePart right) coordinate)
              (KKT.constraintAdjointApply
                (Algebra.projectorData greenData)
                (Block.multiplierPart right) coordinate)))
          (trans
            (cong₂ _-_
              (Block.stateEqual equality coordinate)
              refl)
            (ℚRing.solve-∀
              (Block.statePart
                (Block.applyKKTBlock greenData right) coordinate))))
  ; constraintEquationZero = λ row →
      trans
        (Algebra.constraintSubtractExact greenData
          (Block.statePart left) (Block.statePart right) row)
        (trans
          (cong₂ _-_
            (Block.multiplierEqual equality row) refl)
          (ℚRing.solve-∀
            (Block.multiplierPart
              (Block.applyKKTBlock greenData right) row))) }

finiteKKTBlockInjective :
  ∀ {Multiplier}
    {greenData : Algebra.ConstrainedGreenData Multiplier} →
  ReducedKKTCoercivity greenData →
  ∀ {left right} →
  Block.PointwiseKKTBlockEquality
    (Block.applyKKTBlock greenData left)
    (Block.applyKKTBlock greenData right) →
  Block.PointwiseKKTBlockEquality left right
finiteKKTBlockInjective control {left} {right} equality =
  let
    differenceZero = finiteKKTKernelTrivial control
      (blockApplyDifferenceHomogeneous equality)
  in record
    { Block.PointwiseKKTBlockEquality.stateEqual = λ coordinate →
        trans
          (sym
            (ℚRing.solve-∀
              (Block.statePart left coordinate)
              (Block.statePart right coordinate)))
          (trans
            (cong
              (λ selected → selected + Block.statePart right coordinate)
              (Block.stateEqual differenceZero coordinate))
            (ℚRing.solve-∀ (Block.statePart right coordinate)))
    ; Block.PointwiseKKTBlockEquality.multiplierEqual = λ row →
        trans
          (sym
            (ℚRing.solve-∀
              (Block.multiplierPart left row)
              (Block.multiplierPart right row)))
          (trans
            (cong
              (λ selected → selected + Block.multiplierPart right row)
              (Block.multiplierEqual differenceZero row))
            (ℚRing.solve-∀ (Block.multiplierPart right row))) }

finiteKKTRightInverseIsLeftInverse :
  ∀ {Multiplier}
    {greenData : Algebra.ConstrainedGreenData Multiplier} →
  ReducedKKTCoercivity greenData →
  ∀ vector →
  Block.PointwiseKKTBlockEquality
    (Block.solveKKTBlock greenData
      (Block.applyKKTBlock greenData vector))
    vector
finiteKKTRightInverseIsLeftInverse {greenData = greenData} control vector =
  finiteKKTBlockInjective control
    (Block.kktBlockRightInverseExact greenData
      (Block.applyKKTBlock greenData vector))

record FiniteKKTBlockInverseExact
    {Multiplier : Set}
    (greenData : Algebra.ConstrainedGreenData Multiplier) : Set₁ where
  field
    rightInverse : ∀ source →
      Block.PointwiseKKTBlockEquality
        (Block.applyKKTBlock greenData
          (Block.solveKKTBlock greenData source)) source
    leftInverse : ∀ vector →
      Block.PointwiseKKTBlockEquality
        (Block.solveKKTBlock greenData
          (Block.applyKKTBlock greenData vector)) vector
open FiniteKKTBlockInverseExact public

finiteKKTBlockInverseExact :
  ∀ {Multiplier}
    {greenData : Algebra.ConstrainedGreenData Multiplier} →
  ReducedKKTCoercivity greenData →
  FiniteKKTBlockInverseExact greenData
finiteKKTBlockInverseExact {greenData = greenData} control = record
  { rightInverse = Block.kktBlockRightInverseExact greenData
  ; leftInverse = finiteKKTRightInverseIsLeftInverse control }

finiteKKTKernelTrivialLevel : ProofLevel
finiteKKTKernelTrivialLevel = machineChecked

finiteKKTTwoSidedInverseLevel : ProofLevel
finiteKKTTwoSidedInverseLevel = machineChecked

selectedReducedCoercivityProducerLevel : ProofLevel
selectedReducedCoercivityProducerLevel = conditional
