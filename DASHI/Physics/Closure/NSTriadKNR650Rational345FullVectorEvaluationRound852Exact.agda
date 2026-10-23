{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345FullVectorEvaluationRound852Exact where

------------------------------------------------------------------------
-- R852 / INHABIT THE ACTUAL R829D REPOSITORY VECTOR EVALUATION
--
-- R851 closes the true all-mode modal physical forcing identity, fixing
-- the false k=0 empty-support premise of the older R846 route.
-- R837 then proves each *full* physical output fibre equals its sparse
-- active-cell fold.  R845/R846 have already evaluated all eight actual
-- mixed/commutator rows on that same physical system.  Compose them:
--
--   R851.modalSameObject -> R837.Reduction
--      + R845.mixed₁..₈ + R846.actualComm₁..₈
--           -> R837.ActiveVectorEvaluation
--           -> R829D.Repository345VectorEvaluation.
--
-- This is a theorem about the exact rational radius-four instantaneous
-- Fourier system, NOT about a rational-valued real-time ODE trajectory.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Unit
import DASHI.Physics.Closure.NSTriadKNR650Rational345RepositoryVectorBoundaryRound829Exact as Boundary
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveRepositoryReductionRound837Exact as R837
import DASHI.Physics.Closure.NSTriadKNR650Rational345DirectPhysicalSnapshotRound841Exact as Direct
import DASHI.Physics.Closure.NSTriadKNR650Rational345RepositoryHelicalRowsRound845Exact as HelicalRows
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActualCommutatorRowsRound846Exact as Actual
import DASHI.Physics.Closure.NSTriadKNR650Rational345FullForcingSupportRound851Exact as R851

F : C3.RealField _
F = Rational.rationalRealField

module Evaluate
    {E : C3.IntegerEmbedding F}
    (unit : Unit.UnitPreservingIntegerEmbedding F E)
    (I : C3.ModeInverseSquare F E) where

  physical = Direct.directPhysicalSystem E I
  module Modal = R851.Evaluate unit I
  module R = R837.Reduction physical Modal.modalSameObject
  module H = HelicalRows.Evaluate unit I
  module A = Actual.Evaluate unit I

  activeVectors : R.ActiveVectorEvaluation
  activeVectors = record
    { R.mixed₁ = trans (sym (R.fullMixedIsActive Boundary.k₁)) H.mixed₁
    ; R.comm₁ = trans (sym (R.fullCommutatorIsActive Boundary.k₁)) A.actualComm₁
    ; R.mixed₂ = trans (sym (R.fullMixedIsActive Boundary.k₂)) H.mixed₂
    ; R.comm₂ = trans (sym (R.fullCommutatorIsActive Boundary.k₂)) A.actualComm₂
    ; R.mixed₃ = trans (sym (R.fullMixedIsActive Boundary.k₃)) H.mixed₃
    ; R.comm₃ = trans (sym (R.fullCommutatorIsActive Boundary.k₃)) A.actualComm₃
    ; R.mixed₄ = trans (sym (R.fullMixedIsActive Boundary.k₄)) H.mixed₄
    ; R.comm₄ = trans (sym (R.fullCommutatorIsActive Boundary.k₄)) A.actualComm₄
    ; R.mixed₅ = trans (sym (R.fullMixedIsActive Boundary.k₅)) H.mixed₅
    ; R.comm₅ = trans (sym (R.fullCommutatorIsActive Boundary.k₅)) A.actualComm₅
    ; R.mixed₆ = trans (sym (R.fullMixedIsActive Boundary.k₆)) H.mixed₆
    ; R.comm₆ = trans (sym (R.fullCommutatorIsActive Boundary.k₆)) A.actualComm₆
    ; R.mixed₇ = trans (sym (R.fullMixedIsActive Boundary.k₇)) H.mixed₇
    ; R.comm₇ = trans (sym (R.fullCommutatorIsActive Boundary.k₇)) A.actualComm₇
    ; R.mixed₈ = trans (sym (R.fullMixedIsActive Boundary.k₈)) H.mixed₈
    ; R.comm₈ = trans (sym (R.fullCommutatorIsActive Boundary.k₈)) A.actualComm₈
    }

  physicalR829D :
    Boundary.Repository345VectorEvaluation
      physical R.S
  physicalR829D = R.activeEvaluationBuildsR829D activeVectors

round852FullR829DRepositoryVectorRecordInhabited : Bool
round852FullR829DRepositoryVectorRecordInhabited = true

round852NoUniversalZeroOutputSupportAssumption : Bool
round852NoUniversalZeroOutputSupportAssumption = true

round852RealODETransportProved : Bool
round852RealODETransportProved = false

round852ClayPromotion : Bool
round852ClayPromotion = false

round852FullR829DRepositoryVectorRecordInhabitedIsTrue :
  round852FullR829DRepositoryVectorRecordInhabited ≡ true
round852FullR829DRepositoryVectorRecordInhabitedIsTrue = refl
