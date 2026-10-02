{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveRepositoryReductionRound837Exact where

------------------------------------------------------------------------
-- R837 / R829D FULL-FIBRE -> ACTIVE-FIBRE REPOSITORY REDUCTION
--
-- R834 proves exact sparse zero-pruning and R836 supplies the executable
-- 3-4-5 support classifiers.  This owner composes them with an ACTUAL
-- repository finite Galerkin system.
--
-- A caller supplies only the modal same-object facts
--
--   Audit.velocity            = velocity345
--   Audit.projectedNonlinearity = forcing345
--
-- and the finite active-fold vector evaluations.  The complete physical
-- output-fibre R224/R230 vector equalities required by R829D then follow.
--
-- This removes all inactive 728-cube cells from the remaining proof burden.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNProjectedForcingOuterCellExhaustiveRound437Exact as R437
import DASHI.Physics.Closure.NSTriadKNR650Rational345VectorWorkRound829Exact as Vector
import DASHI.Physics.Closure.NSTriadKNR650Rational345RepositoryVectorBoundaryRound829Exact as Boundary
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact as Active
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSupportMaxCutRound834Exact as Sparse
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot

F : C3.RealField _
F = Rational.rationalRealField

record Repository345ModalSameObject
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) : Set where
  field
    cutoffIsFour :
      Audit.cutoff (Field30.finiteSystem physicalSystem) ≡ 4

    velocitySame :
      (mode : Z3.FourierMode) →
      Audit.velocityAt (Field30.finiteSystem physicalSystem) mode
      ≡ Snapshot.velocity345 mode

    forcingSame :
      (mode : Z3.FourierMode) →
      Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem) mode
      ≡ Snapshot.forcing345 mode

open Repository345ModalSameObject public

module Reduction
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (M : Repository345ModalSameObject physicalSystem) where

  system = Field30.finiteSystem physicalSystem
  velocity = Audit.velocityAt system
  forcing = Audit.projectedNonlinearity system
  cutoff = Audit.cutoff system
  S = Active.selected345HelicalScalars

  actualMixedInactive :
    (tau : Physical.PhysicalTriadIncidence) →
    Snapshot.mixedCellActive tau ≡ false →
    Sparse.MixedInactiveReason velocity tau
  actualMixedInactive tau rejected
    with Snapshot.mixedInactiveReason tau rejected
  ... | Sparse.mixedPVelocityZero proof =
    Sparse.mixedPVelocityZero
      (trans (velocitySame M (Physical.p tau)) proof)
  ... | Sparse.mixedQVelocityZero proof =
    Sparse.mixedQVelocityZero
      (trans (velocitySame M (Physical.q tau)) proof)

  actualCommutatorInactive :
    (tau : Physical.PhysicalTriadIncidence) →
    Snapshot.commutatorCellActive tau ≡ false →
    Sparse.CommutatorInactiveReason velocity forcing tau
  actualCommutatorInactive tau rejected
    with Snapshot.commutatorInactiveReason tau rejected
  ... | Sparse.commPForcingZero proof =
    Sparse.commPForcingZero
      (trans (forcingSame M (Physical.p tau)) proof)
  ... | Sparse.commQVelocityZero proof =
    Sparse.commQVelocityZero
      (trans (velocitySame M (Physical.q tau)) proof)

  activeFibre :
    (Physical.PhysicalTriadIncidence → Bool) →
    Z3.FourierMode →
    List Physical.PhysicalTriadIncidence
  activeFibre select output =
    Sparse.filterSelected select
      (Output.physicalOutputFiber cutoff output)

  activeMixed : Z3.FourierMode → C3.Complex3 F
  activeMixed output =
    R224.foldVector
      (D1a.mixedProductCell S velocity)
      (activeFibre Snapshot.mixedCellActive output)

  activeCommutator : Z3.FourierMode → C3.Complex3 F
  activeCommutator output =
    R224.foldVector
      (R230.forcingCommutatorCell S velocity forcing)
      (activeFibre Snapshot.commutatorCellActive output)

  fullMixedIsActive :
    (output : Z3.FourierMode) →
    Work.fixedOutputMixedProduct S velocity cutoff output
    ≡ activeMixed output
  fullMixedIsActive output =
    Sparse.foldPruneZero
      Snapshot.mixedCellActive
      (D1a.mixedProductCell S velocity)
      zero
      (Output.physicalOutputFiber cutoff output)
    where
    zero :
      (tau : Physical.PhysicalTriadIncidence) →
      Snapshot.mixedCellActive tau ≡ false →
      D1a.mixedProductCell S velocity tau ≡ C3.complex3Zero F
    zero tau rejected with actualMixedInactive tau rejected
    ... | Sparse.mixedPVelocityZero proof =
      Sparse.mixedPlusMinusZeroFromPVelocityZero S velocity tau proof
    ... | Sparse.mixedQVelocityZero proof =
      Sparse.mixedPlusMinusZeroFromQVelocityZero S velocity tau proof

  fullCommutatorIsActive :
    (output : Z3.FourierMode) →
    Work.fixedOutputCommutator S velocity forcing cutoff output
    ≡ activeCommutator output
  fullCommutatorIsActive output =
    Sparse.foldPruneZero
      Snapshot.commutatorCellActive
      (R230.forcingCommutatorCell S velocity forcing)
      zero
      (Output.physicalOutputFiber cutoff output)
    where
    zero :
      (tau : Physical.PhysicalTriadIncidence) →
      Snapshot.commutatorCellActive tau ≡ false →
      R230.forcingCommutatorCell S velocity forcing tau
      ≡ C3.complex3Zero F
    zero tau rejected with actualCommutatorInactive tau rejected
    ... | Sparse.commPForcingZero proof =
      R437.forcingCommutatorZeroFromForcingZero
        S velocity forcing tau proof
    ... | Sparse.commQVelocityZero proof =
      Sparse.forcingCommutatorZeroFromQVelocityZero
        S velocity forcing tau proof

  record ActiveVectorEvaluation : Set where
    field
      mixed₁ : activeMixed Boundary.k₁ ≡ Vector.m₁
      comm₁ : activeCommutator Boundary.k₁ ≡ Vector.g₁
      mixed₂ : activeMixed Boundary.k₂ ≡ Vector.m₂
      comm₂ : activeCommutator Boundary.k₂ ≡ Vector.g₂
      mixed₃ : activeMixed Boundary.k₃ ≡ Vector.m₃
      comm₃ : activeCommutator Boundary.k₃ ≡ Vector.g₃
      mixed₄ : activeMixed Boundary.k₄ ≡ Vector.m₄
      comm₄ : activeCommutator Boundary.k₄ ≡ Vector.g₄
      mixed₅ : activeMixed Boundary.k₅ ≡ Vector.m₅
      comm₅ : activeCommutator Boundary.k₅ ≡ Vector.g₅
      mixed₆ : activeMixed Boundary.k₆ ≡ Vector.m₆
      comm₆ : activeCommutator Boundary.k₆ ≡ Vector.g₆
      mixed₇ : activeMixed Boundary.k₇ ≡ Vector.m₇
      comm₇ : activeCommutator Boundary.k₇ ≡ Vector.g₇
      mixed₈ : activeMixed Boundary.k₈ ≡ Vector.m₈
      comm₈ : activeCommutator Boundary.k₈ ≡ Vector.g₈

  open ActiveVectorEvaluation public

  activeEvaluationBuildsR829D :
    ActiveVectorEvaluation →
    Boundary.Repository345VectorEvaluation physicalSystem S
  activeEvaluationBuildsR829D A = record
    { Boundary.cutoffIsFour = cutoffIsFour M
    ; Boundary.mixed₁ = trans (fullMixedIsActive Boundary.k₁) (mixed₁ A)
    ; Boundary.comm₁ = trans (fullCommutatorIsActive Boundary.k₁) (comm₁ A)
    ; Boundary.mixed₂ = trans (fullMixedIsActive Boundary.k₂) (mixed₂ A)
    ; Boundary.comm₂ = trans (fullCommutatorIsActive Boundary.k₂) (comm₂ A)
    ; Boundary.mixed₃ = trans (fullMixedIsActive Boundary.k₃) (mixed₃ A)
    ; Boundary.comm₃ = trans (fullCommutatorIsActive Boundary.k₃) (comm₃ A)
    ; Boundary.mixed₄ = trans (fullMixedIsActive Boundary.k₄) (mixed₄ A)
    ; Boundary.comm₄ = trans (fullCommutatorIsActive Boundary.k₄) (comm₄ A)
    ; Boundary.mixed₅ = trans (fullMixedIsActive Boundary.k₅) (mixed₅ A)
    ; Boundary.comm₅ = trans (fullCommutatorIsActive Boundary.k₅) (comm₅ A)
    ; Boundary.mixed₆ = trans (fullMixedIsActive Boundary.k₆) (mixed₆ A)
    ; Boundary.comm₆ = trans (fullCommutatorIsActive Boundary.k₆) (comm₆ A)
    ; Boundary.mixed₇ = trans (fullMixedIsActive Boundary.k₇) (mixed₇ A)
    ; Boundary.comm₇ = trans (fullCommutatorIsActive Boundary.k₇) (comm₇ A)
    ; Boundary.mixed₈ = trans (fullMixedIsActive Boundary.k₈) (mixed₈ A)
    ; Boundary.comm₈ = trans (fullCommutatorIsActive Boundary.k₈) (comm₈ A)

    ; Boundary.velocity₁ =
        trans (velocitySame M Boundary.k₁) Snapshot.velocity₁
    ; Boundary.forcing₁ =
        trans (forcingSame M Boundary.k₁) Snapshot.forcing₁Exact
    ; Boundary.velocity₂ =
        trans (velocitySame M Boundary.k₂) Snapshot.velocity₂
    ; Boundary.forcing₂ =
        trans (forcingSame M Boundary.k₂) Snapshot.forcing₂Exact
    ; Boundary.velocity₄ =
        trans (velocitySame M Boundary.k₄) Snapshot.velocity₄
    ; Boundary.forcing₄ =
        trans (forcingSame M Boundary.k₄) Snapshot.forcing₄Exact
    ; Boundary.velocity₅ =
        trans (velocitySame M Boundary.k₅) Snapshot.velocity₅
    ; Boundary.forcing₅ =
        trans (forcingSame M Boundary.k₅) Snapshot.forcing₅Exact
    ; Boundary.velocity₇ =
        trans (velocitySame M Boundary.k₇) Snapshot.velocity₇
    ; Boundary.forcing₇ =
        trans (forcingSame M Boundary.k₇) Snapshot.forcing₇Exact
    ; Boundary.velocity₈ =
        trans (velocitySame M Boundary.k₈) Snapshot.velocity₈
    ; Boundary.forcing₈ =
        trans (forcingSame M Boundary.k₈) Snapshot.forcing₈Exact
    }

round837FullMixedFibreReducedToActiveCells : Bool
round837FullMixedFibreReducedToActiveCells = true

round837FullCommutatorFibreReducedToActiveCells : Bool
round837FullCommutatorFibreReducedToActiveCells = true

round837R829DConstructibleFromModalAndActiveEvaluation : Bool
round837R829DConstructibleFromModalAndActiveEvaluation = true

round837AdditionalAnalyticEstimateRequired : Bool
round837AdditionalAnalyticEstimateRequired = false

round837ClayPromotion : Bool
round837ClayPromotion = false

round837R829DConstructibleFromModalAndActiveEvaluationIsTrue :
  round837R829DConstructibleFromModalAndActiveEvaluation ≡ true
round837R829DConstructibleFromModalAndActiveEvaluationIsTrue = refl
