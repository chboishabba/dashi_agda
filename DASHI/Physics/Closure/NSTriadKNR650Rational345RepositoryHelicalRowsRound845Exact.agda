{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345RepositoryHelicalRowsRound845Exact where

------------------------------------------------------------------------
-- R845 / DIRECT R224/R230 ACTIVE-FOLD EVALUATION
--
-- R836 prunes complete fibres exactly.  R842 fixes all active Leray geometry.
-- This owner targets the remaining eight mixed vectors and eight commutator
-- vectors directly against R829B's m_i/g_i table.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Unit
import DASHI.Physics.Closure.NSTriadKNR650Rational345VectorWorkRound829Exact as Vector
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact as Active
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSupportMaxCutRound834Exact as Sparse
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot
import DASHI.Physics.Closure.NSTriadKNR650Rational345GeometryCalibrationRound842Exact as Geometry
import DASHI.Physics.Closure.NSTriadKNR650Rational345OrderedCellsRound843Exact as Cells
import DASHI.Physics.Closure.NSTriadKNR650Rational345ForcingRowsRound844Exact as Rows
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- Extra active commutator incidences not present in the velocity-velocity
-- mixed two-cell fibres.
------------------------------------------------------------------------

g₂m g₄m g₅m g₇m : Physical.PhysicalTriadIncidence
g₂m = Physical.physicalTriad Active.k₃ Active.k₄ Active.k₂ refl
g₄m = Physical.physicalTriad Active.k₆ Active.k₂ Active.k₄ refl
g₅m = Physical.physicalTriad Active.k₃ Active.k₇ Active.k₅ refl
g₇m = Physical.physicalTriad Active.k₆ Active.k₅ Active.k₇ refl

module Evaluate
    {E : C3.IntegerEmbedding F}
    (unit : Unit.UnitPreservingIntegerEmbedding F E)
    (I : C3.ModeInverseSquare F E) where

  module G = Geometry.Geometry unit I
  module M = Rows.Evaluate unit I

  S = Active.selected345HelicalScalars

  mixed₁ :
    Work.fixedOutputMixedProduct S Snapshot.velocity345 4 Active.k₁
    ≡ Vector.m₁
  mixed₁ =
    trans
      (Snapshot.pruneMixed345
        (Output.physicalOutputFiber 4 Active.k₁))
      tail
    where
    tail :
      R224.foldVector
        (R224.mixedPlusMinus S Snapshot.velocity345)
        (Sparse.filterSelected Snapshot.mixedCellActive
          (Output.physicalOutputFiber 4 Active.k₁))
      ≡ Vector.m₁
    tail
      rewrite M.fibre₁
            | G.embedMinus3 | G.embedMinus4 | C3.embedZero E
            | G.inv₁ | G.inv₂ | G.inv₄ = refl

  mixed₂ :
    Work.fixedOutputMixedProduct S Snapshot.velocity345 4 Active.k₂
    ≡ Vector.m₂
  mixed₂ =
    trans (Snapshot.pruneMixed345 (Output.physicalOutputFiber 4 Active.k₂)) tail
    where
    tail :
      R224.foldVector (R224.mixedPlusMinus S Snapshot.velocity345)
        (Sparse.filterSelected Snapshot.mixedCellActive
          (Output.physicalOutputFiber 4 Active.k₂))
      ≡ Vector.m₂
    tail
      rewrite M.fibre₂
            | G.embedMinus3 | G.embedMinus4 | G.embedPlus4 | C3.embedZero E
            | G.inv₁ | G.inv₂ | G.inv₅ = refl

  mixed₃ :
    Work.fixedOutputMixedProduct S Snapshot.velocity345 4 Active.k₃
    ≡ Vector.m₃
  mixed₃ =
    trans (Snapshot.pruneMixed345 (Output.physicalOutputFiber 4 Active.k₃)) tail
    where
    tail :
      R224.foldVector (R224.mixedPlusMinus S Snapshot.velocity345)
        (Sparse.filterSelected Snapshot.mixedCellActive
          (Output.physicalOutputFiber 4 Active.k₃))
      ≡ Vector.m₃
    tail
      rewrite M.fibre₃
            | G.embedMinus3 | G.embedPlus4 | C3.embedZero E
            | G.inv₂ | G.inv₅ = refl

  mixed₄ :
    Work.fixedOutputMixedProduct S Snapshot.velocity345 4 Active.k₄
    ≡ Vector.m₄
  mixed₄ =
    trans (Snapshot.pruneMixed345 (Output.physicalOutputFiber 4 Active.k₄)) tail
    where
    tail :
      R224.foldVector (R224.mixedPlusMinus S Snapshot.velocity345)
        (Sparse.filterSelected Snapshot.mixedCellActive
          (Output.physicalOutputFiber 4 Active.k₄))
      ≡ Vector.m₄
    tail
      rewrite M.fibre₄
            | G.embedMinus3 | G.embedMinus4 | G.embedPlus3 | C3.embedZero E
            | G.inv₁ | G.inv₇ = refl

  mixed₅ :
    Work.fixedOutputMixedProduct S Snapshot.velocity345 4 Active.k₅
    ≡ Vector.m₅
  mixed₅ =
    trans (Snapshot.pruneMixed345 (Output.physicalOutputFiber 4 Active.k₅)) tail
    where
    tail :
      R224.foldVector (R224.mixedPlusMinus S Snapshot.velocity345)
        (Sparse.filterSelected Snapshot.mixedCellActive
          (Output.physicalOutputFiber 4 Active.k₅))
      ≡ Vector.m₅
    tail
      rewrite M.fibre₅
            | G.embedMinus3 | G.embedPlus3 | G.embedPlus4 | C3.embedZero E
            | G.inv₂ | G.inv₈ = refl

  mixed₆ :
    Work.fixedOutputMixedProduct S Snapshot.velocity345 4 Active.k₆
    ≡ Vector.m₆
  mixed₆ =
    trans (Snapshot.pruneMixed345 (Output.physicalOutputFiber 4 Active.k₆)) tail
    where
    tail :
      R224.foldVector (R224.mixedPlusMinus S Snapshot.velocity345)
        (Sparse.filterSelected Snapshot.mixedCellActive
          (Output.physicalOutputFiber 4 Active.k₆))
      ≡ Vector.m₆
    tail
      rewrite M.fibre₆
            | G.embedMinus4 | G.embedPlus3 | C3.embedZero E
            | G.inv₄ | G.inv₇ = refl

  mixed₇ :
    Work.fixedOutputMixedProduct S Snapshot.velocity345 4 Active.k₇
    ≡ Vector.m₇
  mixed₇ =
    trans (Snapshot.pruneMixed345 (Output.physicalOutputFiber 4 Active.k₇)) tail
    where
    tail :
      R224.foldVector (R224.mixedPlusMinus S Snapshot.velocity345)
        (Sparse.filterSelected Snapshot.mixedCellActive
          (Output.physicalOutputFiber 4 Active.k₇))
      ≡ Vector.m₇
    tail
      rewrite M.fibre₇
            | G.embedMinus4 | G.embedPlus3 | G.embedPlus4 | C3.embedZero E
            | G.inv₄ | G.inv₈ = refl

  mixed₈ :
    Work.fixedOutputMixedProduct S Snapshot.velocity345 4 Active.k₈
    ≡ Vector.m₈
  mixed₈ =
    trans (Snapshot.pruneMixed345 (Output.physicalOutputFiber 4 Active.k₈)) tail
    where
    tail :
      R224.foldVector (R224.mixedPlusMinus S Snapshot.velocity345)
        (Sparse.filterSelected Snapshot.mixedCellActive
          (Output.physicalOutputFiber 4 Active.k₈))
      ≡ Vector.m₈
    tail
      rewrite M.fibre₈
            | G.embedPlus3 | G.embedPlus4 | C3.embedZero E
            | G.inv₅ | G.inv₇ = refl

  ----------------------------------------------------------------------
  -- Active commutator fibre lists.  These are executable finite equalities.
  ----------------------------------------------------------------------

  commFibre₁ :
    Sparse.filterSelected Snapshot.commutatorCellActive
      (Output.physicalOutputFiber 4 Active.k₁)
    ≡ Cells.t₁a ∷ Cells.t₁b ∷ []
  commFibre₁ = refl

  commFibre₂ :
    Sparse.filterSelected Snapshot.commutatorCellActive
      (Output.physicalOutputFiber 4 Active.k₂)
    ≡ Cells.t₂a ∷ g₂m ∷ Cells.t₂b ∷ []
  commFibre₂ = refl

  commFibre₃ :
    Sparse.filterSelected Snapshot.commutatorCellActive
      (Output.physicalOutputFiber 4 Active.k₃)
    ≡ Cells.t₃a ∷ Cells.t₃b ∷ []
  commFibre₃ = refl

  commFibre₄ :
    Sparse.filterSelected Snapshot.commutatorCellActive
      (Output.physicalOutputFiber 4 Active.k₄)
    ≡ Cells.t₄a ∷ g₄m ∷ Cells.t₄b ∷ []
  commFibre₄ = refl

  commFibre₅ :
    Sparse.filterSelected Snapshot.commutatorCellActive
      (Output.physicalOutputFiber 4 Active.k₅)
    ≡ Cells.t₅a ∷ g₅m ∷ Cells.t₅b ∷ []
  commFibre₅ = refl

  commFibre₆ :
    Sparse.filterSelected Snapshot.commutatorCellActive
      (Output.physicalOutputFiber 4 Active.k₆)
    ≡ Cells.t₆a ∷ Cells.t₆b ∷ []
  commFibre₆ = refl

  commFibre₇ :
    Sparse.filterSelected Snapshot.commutatorCellActive
      (Output.physicalOutputFiber 4 Active.k₇)
    ≡ Cells.t₇a ∷ g₇m ∷ Cells.t₇b ∷ []
  commFibre₇ = refl

  commFibre₈ :
    Sparse.filterSelected Snapshot.commutatorCellActive
      (Output.physicalOutputFiber 4 Active.k₈)
    ≡ Cells.t₈a ∷ Cells.t₈b ∷ []
  commFibre₈ = refl

  comm₁ :
    Work.fixedOutputCommutator S Snapshot.velocity345 Snapshot.forcing345 4 Active.k₁
    ≡ Vector.g₁
  comm₁ =
    trans (Snapshot.pruneCommutator345 (Output.physicalOutputFiber 4 Active.k₁)) tail
    where
    tail :
      R224.foldVector
        (R230.forcingCommutatorCell S Snapshot.velocity345 Snapshot.forcing345)
        (Sparse.filterSelected Snapshot.commutatorCellActive
          (Output.physicalOutputFiber 4 Active.k₁))
      ≡ Vector.g₁
    tail
      rewrite commFibre₁
            | G.embedMinus3 | G.embedMinus4 | C3.embedZero E
            | G.inv₁ | G.inv₂ | G.inv₄ = refl

  comm₂ :
    Work.fixedOutputCommutator S Snapshot.velocity345 Snapshot.forcing345 4 Active.k₂
    ≡ Vector.g₂
  comm₂ =
    trans (Snapshot.pruneCommutator345 (Output.physicalOutputFiber 4 Active.k₂)) tail
    where
    tail :
      R224.foldVector
        (R230.forcingCommutatorCell S Snapshot.velocity345 Snapshot.forcing345)
        (Sparse.filterSelected Snapshot.commutatorCellActive
          (Output.physicalOutputFiber 4 Active.k₂))
      ≡ Vector.g₂
    tail
      rewrite commFibre₂
            | G.embedMinus3 | G.embedMinus4 | G.embedPlus4 | C3.embedZero E
            | G.inv₁ | G.inv₂ | G.inv₃ | G.inv₄ | G.inv₅ = refl

  comm₃ :
    Work.fixedOutputCommutator S Snapshot.velocity345 Snapshot.forcing345 4 Active.k₃
    ≡ Vector.g₃
  comm₃ =
    trans (Snapshot.pruneCommutator345 (Output.physicalOutputFiber 4 Active.k₃)) tail
    where
    tail :
      R224.foldVector
        (R230.forcingCommutatorCell S Snapshot.velocity345 Snapshot.forcing345)
        (Sparse.filterSelected Snapshot.commutatorCellActive
          (Output.physicalOutputFiber 4 Active.k₃))
      ≡ Vector.g₃
    tail
      rewrite commFibre₃
            | G.embedMinus3 | G.embedPlus4 | C3.embedZero E
            | G.inv₂ | G.inv₅ = refl

  comm₄ :
    Work.fixedOutputCommutator S Snapshot.velocity345 Snapshot.forcing345 4 Active.k₄
    ≡ Vector.g₄
  comm₄ =
    trans (Snapshot.pruneCommutator345 (Output.physicalOutputFiber 4 Active.k₄)) tail
    where
    tail :
      R224.foldVector
        (R230.forcingCommutatorCell S Snapshot.velocity345 Snapshot.forcing345)
        (Sparse.filterSelected Snapshot.commutatorCellActive
          (Output.physicalOutputFiber 4 Active.k₄))
      ≡ Vector.g₄
    tail
      rewrite commFibre₄
            | G.embedMinus3 | G.embedMinus4 | G.embedPlus3 | C3.embedZero E
            | G.inv₁ | G.inv₂ | G.inv₄ | G.inv₆ | G.inv₇ = refl

  comm₅ :
    Work.fixedOutputCommutator S Snapshot.velocity345 Snapshot.forcing345 4 Active.k₅
    ≡ Vector.g₅
  comm₅ =
    trans (Snapshot.pruneCommutator345 (Output.physicalOutputFiber 4 Active.k₅)) tail
    where
    tail :
      R224.foldVector
        (R230.forcingCommutatorCell S Snapshot.velocity345 Snapshot.forcing345)
        (Sparse.filterSelected Snapshot.commutatorCellActive
          (Output.physicalOutputFiber 4 Active.k₅))
      ≡ Vector.g₅
    tail
      rewrite commFibre₅
            | G.embedMinus3 | G.embedPlus3 | G.embedPlus4 | C3.embedZero E
            | G.inv₂ | G.inv₃ | G.inv₅ | G.inv₇ | G.inv₈ = refl

  comm₆ :
    Work.fixedOutputCommutator S Snapshot.velocity345 Snapshot.forcing345 4 Active.k₆
    ≡ Vector.g₆
  comm₆ =
    trans (Snapshot.pruneCommutator345 (Output.physicalOutputFiber 4 Active.k₆)) tail
    where
    tail :
      R224.foldVector
        (R230.forcingCommutatorCell S Snapshot.velocity345 Snapshot.forcing345)
        (Sparse.filterSelected Snapshot.commutatorCellActive
          (Output.physicalOutputFiber 4 Active.k₆))
      ≡ Vector.g₆
    tail
      rewrite commFibre₆
            | G.embedMinus4 | G.embedPlus3 | C3.embedZero E
            | G.inv₄ | G.inv₇ = refl

  comm₇ :
    Work.fixedOutputCommutator S Snapshot.velocity345 Snapshot.forcing345 4 Active.k₇
    ≡ Vector.g₇
  comm₇ =
    trans (Snapshot.pruneCommutator345 (Output.physicalOutputFiber 4 Active.k₇)) tail
    where
    tail :
      R224.foldVector
        (R230.forcingCommutatorCell S Snapshot.velocity345 Snapshot.forcing345)
        (Sparse.filterSelected Snapshot.commutatorCellActive
          (Output.physicalOutputFiber 4 Active.k₇))
      ≡ Vector.g₇
    tail
      rewrite commFibre₇
            | G.embedMinus4 | G.embedPlus3 | G.embedPlus4 | C3.embedZero E
            | G.inv₄ | G.inv₅ | G.inv₆ | G.inv₈ = refl

  comm₈ :
    Work.fixedOutputCommutator S Snapshot.velocity345 Snapshot.forcing345 4 Active.k₈
    ≡ Vector.g₈
  comm₈ =
    trans (Snapshot.pruneCommutator345 (Output.physicalOutputFiber 4 Active.k₈)) tail
    where
    tail :
      R224.foldVector
        (R230.forcingCommutatorCell S Snapshot.velocity345 Snapshot.forcing345)
        (Sparse.filterSelected Snapshot.commutatorCellActive
          (Output.physicalOutputFiber 4 Active.k₈))
      ≡ Vector.g₈
    tail
      rewrite commFibre₈
            | G.embedPlus3 | G.embedPlus4 | C3.embedZero E
            | G.inv₅ | G.inv₇ = refl

round845EightR224MixedRowsKernelTargeted : Bool
round845EightR224MixedRowsKernelTargeted = true

round845EightR230CommutatorRowsKernelTargeted : Bool
round845EightR230CommutatorRowsKernelTargeted = true

round845GlobalHelicalProjectorLawUsed : Bool
round845GlobalHelicalProjectorLawUsed = false

round845ClayPromotion : Bool
round845ClayPromotion = false
