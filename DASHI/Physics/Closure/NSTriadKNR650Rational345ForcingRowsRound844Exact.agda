{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345ForcingRowsRound844Exact where

------------------------------------------------------------------------
-- R844 / ACTIVE-FIBRE ENUMERATION -> EIGHT LITERAL R30 FORCING ROWS
--
-- R840 reduces projectedNonlinearity to seed-seed cells.  At each active
-- 3-4-5 output there are exactly two such ordered cells.  R843E evaluates all
-- sixteen cells.  This owner performs the finite enumeration/aggregation and
-- identifies the repository R30 forcing with Snapshot.forcing345.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Unit
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSupportMaxCutRound834Exact as Sparse
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot
import DASHI.Physics.Closure.NSTriadKNR650Rational345ProjectedNonlinearityPruneRound840Exact as R840
import DASHI.Physics.Closure.NSTriadKNR650Rational345DirectPhysicalSnapshotRound841Exact as Direct
import DASHI.Physics.Closure.NSTriadKNR650Rational345OrderedCellsRound843Exact as Cells
import DASHI.Physics.Closure.NSTriadKNR650Rational345OrderedCellEvaluationRound843Exact as CellEval

F : C3.RealField _
F = Rational.rationalRealField

module Evaluate
    {E : C3.IntegerEmbedding F}
    (unit : Unit.UnitPreservingIntegerEmbedding F E)
    (I : C3.ModeInverseSquare F E) where

  system = Direct.directAuditSystem E I
  module P = R840.SparseR30 system (Direct.directVelocitySame E I)
  module C = CellEval.Evaluate unit I

  fibre₁ :
    Sparse.filterSelected Snapshot.mixedCellActive
      (Output.physicalOutputFiber 4 Cells.Active.k₁)
    ≡ Cells.t₁a ∷ Cells.t₁b ∷ []
  fibre₁ = refl

  fibre₂ :
    Sparse.filterSelected Snapshot.mixedCellActive
      (Output.physicalOutputFiber 4 Cells.Active.k₂)
    ≡ Cells.t₂a ∷ Cells.t₂b ∷ []
  fibre₂ = refl

  fibre₃ :
    Sparse.filterSelected Snapshot.mixedCellActive
      (Output.physicalOutputFiber 4 Cells.Active.k₃)
    ≡ Cells.t₃a ∷ Cells.t₃b ∷ []
  fibre₃ = refl

  fibre₄ :
    Sparse.filterSelected Snapshot.mixedCellActive
      (Output.physicalOutputFiber 4 Cells.Active.k₄)
    ≡ Cells.t₄a ∷ Cells.t₄b ∷ []
  fibre₄ = refl

  fibre₅ :
    Sparse.filterSelected Snapshot.mixedCellActive
      (Output.physicalOutputFiber 4 Cells.Active.k₅)
    ≡ Cells.t₅a ∷ Cells.t₅b ∷ []
  fibre₅ = refl

  fibre₆ :
    Sparse.filterSelected Snapshot.mixedCellActive
      (Output.physicalOutputFiber 4 Cells.Active.k₆)
    ≡ Cells.t₆a ∷ Cells.t₆b ∷ []
  fibre₆ = refl

  fibre₇ :
    Sparse.filterSelected Snapshot.mixedCellActive
      (Output.physicalOutputFiber 4 Cells.Active.k₇)
    ≡ Cells.t₇a ∷ Cells.t₇b ∷ []
  fibre₇ = refl

  fibre₈ :
    Sparse.filterSelected Snapshot.mixedCellActive
      (Output.physicalOutputFiber 4 Cells.Active.k₈)
    ≡ Cells.t₈a ∷ Cells.t₈b ∷ []
  fibre₈ = refl

  forcing₁ :
    Audit.projectedNonlinearity system Cells.Active.k₁
    ≡ Snapshot.forcing345 Cells.Active.k₁
  forcing₁ =
    trans (P.projectedNonlinearityIsActiveR30Fold Cells.Active.k₁) tail
    where
    tail :
      P.activeR30Fold Cells.Active.k₁
      ≡ Snapshot.forcing345 Cells.Active.k₁
    tail rewrite fibre₁ | C.cell₁aExact | C.cell₁bExact = refl

  forcing₂ :
    Audit.projectedNonlinearity system Cells.Active.k₂
    ≡ Snapshot.forcing345 Cells.Active.k₂
  forcing₂ =
    trans (P.projectedNonlinearityIsActiveR30Fold Cells.Active.k₂) tail
    where
    tail :
      P.activeR30Fold Cells.Active.k₂
      ≡ Snapshot.forcing345 Cells.Active.k₂
    tail rewrite fibre₂ | C.cell₂aExact | C.cell₂bExact = refl

  forcing₃ :
    Audit.projectedNonlinearity system Cells.Active.k₃
    ≡ Snapshot.forcing345 Cells.Active.k₃
  forcing₃ =
    trans (P.projectedNonlinearityIsActiveR30Fold Cells.Active.k₃) tail
    where
    tail :
      P.activeR30Fold Cells.Active.k₃
      ≡ Snapshot.forcing345 Cells.Active.k₃
    tail rewrite fibre₃ | C.cell₃aExact | C.cell₃bExact = refl

  forcing₄ :
    Audit.projectedNonlinearity system Cells.Active.k₄
    ≡ Snapshot.forcing345 Cells.Active.k₄
  forcing₄ =
    trans (P.projectedNonlinearityIsActiveR30Fold Cells.Active.k₄) tail
    where
    tail :
      P.activeR30Fold Cells.Active.k₄
      ≡ Snapshot.forcing345 Cells.Active.k₄
    tail rewrite fibre₄ | C.cell₄aExact | C.cell₄bExact = refl

  forcing₅ :
    Audit.projectedNonlinearity system Cells.Active.k₅
    ≡ Snapshot.forcing345 Cells.Active.k₅
  forcing₅ =
    trans (P.projectedNonlinearityIsActiveR30Fold Cells.Active.k₅) tail
    where
    tail :
      P.activeR30Fold Cells.Active.k₅
      ≡ Snapshot.forcing345 Cells.Active.k₅
    tail rewrite fibre₅ | C.cell₅aExact | C.cell₅bExact = refl

  forcing₆ :
    Audit.projectedNonlinearity system Cells.Active.k₆
    ≡ Snapshot.forcing345 Cells.Active.k₆
  forcing₆ =
    trans (P.projectedNonlinearityIsActiveR30Fold Cells.Active.k₆) tail
    where
    tail :
      P.activeR30Fold Cells.Active.k₆
      ≡ Snapshot.forcing345 Cells.Active.k₆
    tail rewrite fibre₆ | C.cell₆aExact | C.cell₆bExact = refl

  forcing₇ :
    Audit.projectedNonlinearity system Cells.Active.k₇
    ≡ Snapshot.forcing345 Cells.Active.k₇
  forcing₇ =
    trans (P.projectedNonlinearityIsActiveR30Fold Cells.Active.k₇) tail
    where
    tail :
      P.activeR30Fold Cells.Active.k₇
      ≡ Snapshot.forcing345 Cells.Active.k₇
    tail rewrite fibre₇ | C.cell₇aExact | C.cell₇bExact = refl

  forcing₈ :
    Audit.projectedNonlinearity system Cells.Active.k₈
    ≡ Snapshot.forcing345 Cells.Active.k₈
  forcing₈ =
    trans (P.projectedNonlinearityIsActiveR30Fold Cells.Active.k₈) tail
    where
    tail :
      P.activeR30Fold Cells.Active.k₈
      ≡ Snapshot.forcing345 Cells.Active.k₈
    tail rewrite fibre₈ | C.cell₈aExact | C.cell₈bExact = refl

round844EightActiveR30ForcingRowsKernelTargeted : Bool
round844EightActiveR30ForcingRowsKernelTargeted = true

round844FullModalForcingSameObjectClosed : Bool
round844FullModalForcingSameObjectClosed = false

round844ClayPromotion : Bool
round844ClayPromotion = false
