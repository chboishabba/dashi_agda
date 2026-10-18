{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345GlobalR692Round849Exact where

------------------------------------------------------------------------
-- R849 / ACTUAL GLOBAL R692 COHERENT WORK FOR THE 3-4-5 SNAPSHOT
--
-- R848 kills every inactive nonzero output before any estimate.  Therefore
-- Round692.nonzeroGlobalCommutatorWork reduces exactly to eight outputs.
-- R845 supplies the literal mixed rows and R846 supplies the literal R30
-- forcing commutator rows.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _/_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNLiteralNonzeroCutoffSupportRound404Exact as R404
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Unit
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorIncidenceExpansionRound692Exact as R692
import DASHI.Physics.Closure.NSTriadKNR650Rational345VectorWorkRound829Exact as Vector
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact as Active
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot
import DASHI.Physics.Closure.NSTriadKNR650Rational345DirectPhysicalSnapshotRound841Exact as Direct
import DASHI.Physics.Closure.NSTriadKNR650Rational345GeometryCalibrationRound842Exact as Geometry
import DASHI.Physics.Closure.NSTriadKNR650Rational345ForcingRowsRound844Exact as Rows
import DASHI.Physics.Closure.NSTriadKNR650Rational345RepositoryHelicalRowsRound845Exact as HelicalRows
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActualCommutatorRowsRound846Exact as Actual
import DASHI.Physics.Closure.NSTriadKNR650Rational345CriticalFoldsRound847Exact as Critical
import DASHI.Physics.Closure.NSTriadKNR650Rational345MixedOutputSupportRound848Exact as Support

F : C3.RealField _
F = Rational.rationalRealField

module Evaluate
    {E : C3.IntegerEmbedding F}
    (unit : Unit.UnitPreservingIntegerEmbedding F E)
    (I : C3.ModeInverseSquare F E) where

  physicalSystem = Direct.directPhysicalSystem E I
  module X = R692.Expansion physicalSystem Active.selected345HelicalScalars
  module H = HelicalRows.Evaluate unit I
  module A = Actual.Evaluate unit I

  pruneOutputs :
    (items : List Z3.FourierMode) →
    ((mode : Z3.FourierMode) →
      mode Cube.∈ items → Z3.NonZeroMode mode) →
    X.sumOutputCommutatorWork items
    ≡
    X.sumOutputCommutatorWork
      (Critical.filterModes Snapshot.forcingActive items)
  pruneOutputs [] allNonzero = refl
  pruneOutputs (mode ∷ rest) allNonzero
    with Snapshot.forcingActive mode in active
  ... | true =
    cong (X.outputCoherentCommutatorWork mode +_)
      (pruneOutputs rest
        (λ selected member → allNonzero selected (Cube.there member)))
  ... | false =
    trans
      (cong₂ _+_
        (Support.coherentWorkZeroAtInactiveNonzero
          X.forcing mode
          (allNonzero mode (Cube.here refl))
          active)
        (pruneOutputs rest
          (λ selected member → allNonzero selected (Cube.there member))))
      (solve
        (X.sumOutputCommutatorWork
          (Critical.filterModes Snapshot.forcingActive rest) ∷ []))

  activeOutputsExact :
    Critical.filterModes Snapshot.forcingActive
      (Canonical.nonzeroCutoffModes 4)
    ≡
      Active.k₁ ∷ Active.k₃ ∷ Active.k₂
      ∷ Active.k₆ ∷ Active.k₈ ∷ Active.k₇
      ∷ Active.k₄ ∷ Active.k₅ ∷ []
  activeOutputsExact = refl

  globalCoherentWorkExact :
    X.nonzeroGlobalCommutatorWork
    ≡ - ((+ 557627) / 125)
  globalCoherentWorkExact
    rewrite pruneOutputs
      (Canonical.nonzeroCutoffModes 4)
      (λ mode member → R404.nonzeroCutoffMemberNonzero member)
          | activeOutputsExact
          | H.mixed₁ | A.actualComm₁
          | H.mixed₂ | A.actualComm₂
          | H.mixed₃ | A.actualComm₃
          | H.mixed₄ | A.actualComm₄
          | H.mixed₅ | A.actualComm₅
          | H.mixed₆ | A.actualComm₆
          | H.mixed₇ | A.actualComm₇
          | H.mixed₈ | A.actualComm₈
          | Vector.w₁Exact | Vector.w₂Exact
          | Vector.w₃Exact | Vector.w₄Exact
          | Vector.w₅Exact | Vector.w₆Exact
          | Vector.w₇Exact | Vector.w₈Exact =
    solve []

round849ActualGlobalR692CoherentWorkClosed : Bool
round849ActualGlobalR692CoherentWorkClosed = true

round849GlobalInactiveOutputEstimateRequired : Bool
round849GlobalInactiveOutputEstimateRequired = false

round849GlobalForcingSameObjectTheoremRequired : Bool
round849GlobalForcingSameObjectTheoremRequired = false

round849ClayPromotion : Bool
round849ClayPromotion = false

round849ActualGlobalR692CoherentWorkClosedIsTrue :
  round849ActualGlobalR692CoherentWorkClosed ≡ true
round849ActualGlobalR692CoherentWorkClosedIsTrue = refl
