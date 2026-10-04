{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345ActualCommutatorRowsRound846Exact where

------------------------------------------------------------------------
-- R846 / ACTUAL R30 FORCING IN THE EIGHT R230 WORK ROWS
--
-- Avoid a global 728-mode forcing theorem.  On each of the eight selected
-- output fibres, first prune every cell whose q-velocity vanishes.  The
-- surviving p forcing slots are exactly the eight R844 active forcing rows,
-- plus p=0.  R436 supplies the latter exactly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityZeroOutputRound436Exact as R436
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Unit
import DASHI.Physics.Closure.NSTriadKNR650Rational345VectorWorkRound829Exact as Vector
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact as Active
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSupportMaxCutRound834Exact as Sparse
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot
import DASHI.Physics.Closure.NSTriadKNR650Rational345DirectPhysicalSnapshotRound841Exact as Direct
import DASHI.Physics.Closure.NSTriadKNR650Rational345GeometryCalibrationRound842Exact as Geometry
import DASHI.Physics.Closure.NSTriadKNR650Rational345OrderedCellsRound843Exact as Cells
import DASHI.Physics.Closure.NSTriadKNR650Rational345ForcingRowsRound844Exact as Rows
import DASHI.Physics.Closure.NSTriadKNR650Rational345RepositoryHelicalRowsRound845Exact as HelicalRows
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work

F : C3.RealField _
F = Rational.rationalRealField

qActive : Physical.PhysicalTriadIncidence → Bool
qActive tau = Snapshot.velocityActive (Physical.q tau)

z₁ z₂ z₄ z₅ z₇ z₈ : Physical.PhysicalTriadIncidence
z₁ = Physical.physicalTriad Z3.zeroMode Active.k₁ Active.k₁ refl
z₂ = Physical.physicalTriad Z3.zeroMode Active.k₂ Active.k₂ refl
z₄ = Physical.physicalTriad Z3.zeroMode Active.k₄ Active.k₄ refl
z₅ = Physical.physicalTriad Z3.zeroMode Active.k₅ Active.k₅ refl
z₇ = Physical.physicalTriad Z3.zeroMode Active.k₇ Active.k₇ refl
z₈ = Physical.physicalTriad Z3.zeroMode Active.k₈ Active.k₈ refl

module Evaluate
    {E : C3.IntegerEmbedding F}
    (unit : Unit.UnitPreservingIntegerEmbedding F E)
    (I : C3.ModeInverseSquare F E) where

  system = Direct.directAuditSystem E I
  forcing = Audit.projectedNonlinearity system
  S = Active.selected345HelicalScalars
  module G = Geometry.Geometry unit I
  module R = Rows.Evaluate unit I
  module H = HelicalRows.Evaluate unit I

  forcingZero : forcing Z3.zeroMode ≡ C3.complex3Zero F
  forcingZero =
    R436.projectedNonlinearityAtZeroIsZero
      system (Direct.snapshotVelocityTransverse E)

  pruneActual :
    (output : Z3.FourierMode) →
    Work.fixedOutputCommutator
      S Snapshot.velocity345 forcing 4 output
    ≡
    R224.foldVector
      (R230.forcingCommutatorCell S Snapshot.velocity345 forcing)
      (Sparse.filterSelected qActive
        (Output.physicalOutputFiber 4 output))
  pruneActual output =
    Sparse.foldPruneZero qActive
      (R230.forcingCommutatorCell S Snapshot.velocity345 forcing)
      zero
      (Output.physicalOutputFiber 4 output)
    where
    zero :
      (tau : Physical.PhysicalTriadIncidence) →
      qActive tau ≡ false →
      R230.forcingCommutatorCell
        S Snapshot.velocity345 forcing tau
      ≡ C3.complex3Zero F
    zero tau rejected =
      Sparse.forcingCommutatorZeroFromQVelocityZero
        S Snapshot.velocity345 forcing tau
        (Snapshot.velocityInactiveZero (Physical.q tau) rejected)

  qFibre₁ :
    Sparse.filterSelected qActive (Output.physicalOutputFiber 4 Active.k₁)
    ≡ Cells.t₁a ∷ Cells.t₁b ∷ z₁ ∷ []
  qFibre₁ = refl

  qFibre₂ :
    Sparse.filterSelected qActive (Output.physicalOutputFiber 4 Active.k₂)
    ≡ Cells.t₂a ∷ HelicalRows.g₂m ∷ Cells.t₂b ∷ z₂ ∷ []
  qFibre₂ = refl

  qFibre₃ :
    Sparse.filterSelected qActive (Output.physicalOutputFiber 4 Active.k₃)
    ≡ Cells.t₃a ∷ Cells.t₃b ∷ []
  qFibre₃ = refl

  qFibre₄ :
    Sparse.filterSelected qActive (Output.physicalOutputFiber 4 Active.k₄)
    ≡ Cells.t₄a ∷ HelicalRows.g₄m ∷ Cells.t₄b ∷ z₄ ∷ []
  qFibre₄ = refl

  qFibre₅ :
    Sparse.filterSelected qActive (Output.physicalOutputFiber 4 Active.k₅)
    ≡ HelicalRows.g₅m ∷ Cells.t₅a ∷ Cells.t₅b ∷ z₅ ∷ []
  qFibre₅ = refl

  qFibre₆ :
    Sparse.filterSelected qActive (Output.physicalOutputFiber 4 Active.k₆)
    ≡ Cells.t₆b ∷ Cells.t₆a ∷ []
  qFibre₆ = refl

  qFibre₇ :
    Sparse.filterSelected qActive (Output.physicalOutputFiber 4 Active.k₇)
    ≡ HelicalRows.g₇m ∷ Cells.t₇b ∷ Cells.t₇a ∷ z₇ ∷ []
  qFibre₇ = refl

  qFibre₈ :
    Sparse.filterSelected qActive (Output.physicalOutputFiber 4 Active.k₈)
    ≡ Cells.t₈b ∷ Cells.t₈a ∷ z₈ ∷ []
  qFibre₈ = refl

  actualComm₁ :
    Work.fixedOutputCommutator
      S Snapshot.velocity345 forcing 4 Active.k₁
    ≡ Vector.g₁
  actualComm₁ =
    trans (pruneActual Active.k₁) tail
    where
    tail :
      R224.foldVector
        (R230.forcingCommutatorCell S Snapshot.velocity345 forcing)
        (Sparse.filterSelected qActive
          (Output.physicalOutputFiber 4 Active.k₁))
      ≡ Vector.g₁
    tail
      rewrite qFibre₁ | R.forcing₂ | R.forcing₄ | forcingZero
            | G.embedMinus3 | G.embedMinus4 | C3.embedZero E
            | G.inv₁ | G.inv₂ | G.inv₄ = refl

  actualComm₂ :
    Work.fixedOutputCommutator
      S Snapshot.velocity345 forcing 4 Active.k₂
    ≡ Vector.g₂
  actualComm₂ =
    trans (pruneActual Active.k₂) tail
    where
    tail :
      R224.foldVector
        (R230.forcingCommutatorCell S Snapshot.velocity345 forcing)
        (Sparse.filterSelected qActive
          (Output.physicalOutputFiber 4 Active.k₂))
      ≡ Vector.g₂
    tail
      rewrite qFibre₂
            | R.forcing₁ | R.forcing₃ | R.forcing₅ | forcingZero
            | G.embedMinus3 | G.embedMinus4 | G.embedPlus4 | C3.embedZero E
            | G.inv₁ | G.inv₂ | G.inv₃ | G.inv₄ | G.inv₅ = refl

  actualComm₃ :
    Work.fixedOutputCommutator
      S Snapshot.velocity345 forcing 4 Active.k₃
    ≡ Vector.g₃
  actualComm₃ =
    trans (pruneActual Active.k₃) tail
    where
    tail :
      R224.foldVector
        (R230.forcingCommutatorCell S Snapshot.velocity345 forcing)
        (Sparse.filterSelected qActive
          (Output.physicalOutputFiber 4 Active.k₃))
      ≡ Vector.g₃
    tail
      rewrite qFibre₃ | R.forcing₂ | R.forcing₅
            | G.embedMinus3 | G.embedPlus4 | C3.embedZero E
            | G.inv₂ | G.inv₅ = refl

  actualComm₄ :
    Work.fixedOutputCommutator
      S Snapshot.velocity345 forcing 4 Active.k₄
    ≡ Vector.g₄
  actualComm₄ =
    trans (pruneActual Active.k₄) tail
    where
    tail :
      R224.foldVector
        (R230.forcingCommutatorCell S Snapshot.velocity345 forcing)
        (Sparse.filterSelected qActive
          (Output.physicalOutputFiber 4 Active.k₄))
      ≡ Vector.g₄
    tail
      rewrite qFibre₄
            | R.forcing₁ | R.forcing₆ | R.forcing₇ | forcingZero
            | G.embedMinus3 | G.embedMinus4 | G.embedPlus3 | C3.embedZero E
            | G.inv₁ | G.inv₂ | G.inv₄ | G.inv₆ | G.inv₇ = refl

  actualComm₅ :
    Work.fixedOutputCommutator
      S Snapshot.velocity345 forcing 4 Active.k₅
    ≡ Vector.g₅
  actualComm₅ =
    trans (pruneActual Active.k₅) tail
    where
    tail :
      R224.foldVector
        (R230.forcingCommutatorCell S Snapshot.velocity345 forcing)
        (Sparse.filterSelected qActive
          (Output.physicalOutputFiber 4 Active.k₅))
      ≡ Vector.g₅
    tail
      rewrite qFibre₅
            | R.forcing₃ | R.forcing₂ | R.forcing₈ | forcingZero
            | G.embedMinus3 | G.embedPlus3 | G.embedPlus4 | C3.embedZero E
            | G.inv₂ | G.inv₃ | G.inv₅ | G.inv₇ | G.inv₈ = refl

  actualComm₆ :
    Work.fixedOutputCommutator
      S Snapshot.velocity345 forcing 4 Active.k₆
    ≡ Vector.g₆
  actualComm₆ =
    trans (pruneActual Active.k₆) tail
    where
    tail :
      R224.foldVector
        (R230.forcingCommutatorCell S Snapshot.velocity345 forcing)
        (Sparse.filterSelected qActive
          (Output.physicalOutputFiber 4 Active.k₆))
      ≡ Vector.g₆
    tail
      rewrite qFibre₆ | R.forcing₇ | R.forcing₄
            | G.embedMinus4 | G.embedPlus3 | C3.embedZero E
            | G.inv₄ | G.inv₇ = refl

  actualComm₇ :
    Work.fixedOutputCommutator
      S Snapshot.velocity345 forcing 4 Active.k₇
    ≡ Vector.g₇
  actualComm₇ =
    trans (pruneActual Active.k₇) tail
    where
    tail :
      R224.foldVector
        (R230.forcingCommutatorCell S Snapshot.velocity345 forcing)
        (Sparse.filterSelected qActive
          (Output.physicalOutputFiber 4 Active.k₇))
      ≡ Vector.g₇
    tail
      rewrite qFibre₇
            | R.forcing₆ | R.forcing₈ | R.forcing₄ | forcingZero
            | G.embedMinus4 | G.embedPlus3 | G.embedPlus4 | C3.embedZero E
            | G.inv₄ | G.inv₅ | G.inv₆ | G.inv₈ = refl

  actualComm₈ :
    Work.fixedOutputCommutator
      S Snapshot.velocity345 forcing 4 Active.k₈
    ≡ Vector.g₈
  actualComm₈ =
    trans (pruneActual Active.k₈) tail
    where
    tail :
      R224.foldVector
        (R230.forcingCommutatorCell S Snapshot.velocity345 forcing)
        (Sparse.filterSelected qActive
          (Output.physicalOutputFiber 4 Active.k₈))
      ≡ Vector.g₈
    tail
      rewrite qFibre₈
            | R.forcing₇ | R.forcing₅ | forcingZero
            | G.embedPlus3 | G.embedPlus4 | C3.embedZero E
            | G.inv₅ | G.inv₇ = refl

round846ActualR30ForcingUsedInEightR230Rows : Bool
round846ActualR30ForcingUsedInEightR230Rows = true

round846GlobalForcingSameObjectTheoremRequired : Bool
round846GlobalForcingSameObjectTheoremRequired = false

round846ClayPromotion : Bool
round846ClayPromotion = false
