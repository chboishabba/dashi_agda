{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345RepositoryVectorBoundaryRound829Exact where

------------------------------------------------------------------------
-- R829D / REPOSITORY-NATIVE VECTOR EVALUATION BOUNDARY
--
-- R829B kernel-checks the eight exact vector -> coherent-work rows.
-- R829C kernel-checks the six exact velocity/forcing -> production/dissipation
-- rows.  This owner states the remaining same-object theorem at its smallest
-- literal boundary: the actual R224/R230/Audit operators on one physical
-- radius-four system must evaluate to those already-checked vectors.
--
-- No scalar arithmetic remains inside this boundary.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_; -[1+_])
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNR650Rational345VectorWorkRound829Exact as Vector
import DASHI.Physics.Closure.NSTriadKNR650Rational345EnergyRowsRound829Exact as Energy

F : C3.RealField _
F = Rational.rationalRealField

minus3 : Data.Integer.Base.ℤ
minus3 = -[1+ 2 ]

minus4 : Data.Integer.Base.ℤ
minus4 = -[1+ 3 ]

k₁ k₂ k₃ k₄ k₅ k₆ k₇ k₈ : Z3.FourierMode
k₁ = Z3.mode minus3 minus4 (+ 0)
k₂ = Z3.mode minus3 (+ 0) (+ 0)
k₃ = Z3.mode minus3 (+ 4) (+ 0)
k₄ = Z3.mode (+ 0) minus4 (+ 0)
k₅ = Z3.mode (+ 0) (+ 4) (+ 0)
k₆ = Z3.mode (+ 3) minus4 (+ 0)
k₇ = Z3.mode (+ 3) (+ 0) (+ 0)
k₈ = Z3.mode (+ 3) (+ 4) (+ 0)

record Repository345VectorEvaluation
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) : Set where
  field
    cutoffIsFour : Audit.cutoff (Field30.finiteSystem physicalSystem) ≡ 4

    mixed₁ :
      Work.fixedOutputMixedProduct S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.cutoff (Field30.finiteSystem physicalSystem)) k₁
      ≡ Vector.m₁
    comm₁ :
      Work.fixedOutputCommutator S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem))
        (Audit.cutoff (Field30.finiteSystem physicalSystem)) k₁
      ≡ Vector.g₁

    mixed₂ :
      Work.fixedOutputMixedProduct S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.cutoff (Field30.finiteSystem physicalSystem)) k₂
      ≡ Vector.m₂
    comm₂ :
      Work.fixedOutputCommutator S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem))
        (Audit.cutoff (Field30.finiteSystem physicalSystem)) k₂
      ≡ Vector.g₂

    mixed₃ :
      Work.fixedOutputMixedProduct S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.cutoff (Field30.finiteSystem physicalSystem)) k₃
      ≡ Vector.m₃
    comm₃ :
      Work.fixedOutputCommutator S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem))
        (Audit.cutoff (Field30.finiteSystem physicalSystem)) k₃
      ≡ Vector.g₃

    mixed₄ :
      Work.fixedOutputMixedProduct S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.cutoff (Field30.finiteSystem physicalSystem)) k₄
      ≡ Vector.m₄
    comm₄ :
      Work.fixedOutputCommutator S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem))
        (Audit.cutoff (Field30.finiteSystem physicalSystem)) k₄
      ≡ Vector.g₄

    mixed₅ :
      Work.fixedOutputMixedProduct S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.cutoff (Field30.finiteSystem physicalSystem)) k₅
      ≡ Vector.m₅
    comm₅ :
      Work.fixedOutputCommutator S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem))
        (Audit.cutoff (Field30.finiteSystem physicalSystem)) k₅
      ≡ Vector.g₅

    mixed₆ :
      Work.fixedOutputMixedProduct S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.cutoff (Field30.finiteSystem physicalSystem)) k₆
      ≡ Vector.m₆
    comm₆ :
      Work.fixedOutputCommutator S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem))
        (Audit.cutoff (Field30.finiteSystem physicalSystem)) k₆
      ≡ Vector.g₆

    mixed₇ :
      Work.fixedOutputMixedProduct S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.cutoff (Field30.finiteSystem physicalSystem)) k₇
      ≡ Vector.m₇
    comm₇ :
      Work.fixedOutputCommutator S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem))
        (Audit.cutoff (Field30.finiteSystem physicalSystem)) k₇
      ≡ Vector.g₇

    mixed₈ :
      Work.fixedOutputMixedProduct S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.cutoff (Field30.finiteSystem physicalSystem)) k₈
      ≡ Vector.m₈
    comm₈ :
      Work.fixedOutputCommutator S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem))
        (Audit.cutoff (Field30.finiteSystem physicalSystem)) k₈
      ≡ Vector.g₈

    velocity₁ : Audit.velocityAt (Field30.finiteSystem physicalSystem) k₁ ≡ Energy.u₁
    forcing₁ : Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem) k₁ ≡ Energy.f₁
    velocity₂ : Audit.velocityAt (Field30.finiteSystem physicalSystem) k₂ ≡ Energy.u₂
    forcing₂ : Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem) k₂ ≡ Energy.f₂
    velocity₄ : Audit.velocityAt (Field30.finiteSystem physicalSystem) k₄ ≡ Energy.u₃
    forcing₄ : Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem) k₄ ≡ Energy.f₃
    velocity₅ : Audit.velocityAt (Field30.finiteSystem physicalSystem) k₅ ≡ Energy.u₄
    forcing₅ : Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem) k₅ ≡ Energy.f₄
    velocity₇ : Audit.velocityAt (Field30.finiteSystem physicalSystem) k₇ ≡ Energy.u₅
    forcing₇ : Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem) k₇ ≡ Energy.f₅
    velocity₈ : Audit.velocityAt (Field30.finiteSystem physicalSystem) k₈ ≡ Energy.u₆
    forcing₈ : Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem) k₈ ≡ Energy.f₆

open Repository345VectorEvaluation public

module Consequences
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (E : Repository345VectorEvaluation physicalSystem S) where

  velocity = Audit.velocityAt (Field30.finiteSystem physicalSystem)
  forcing = Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem)
  cutoff = Audit.cutoff (Field30.finiteSystem physicalSystem)

  workAt : Z3.FourierMode → ℚ
  workAt k =
    Work.coherentWork
      (Work.fixedOutputMixedProduct S velocity cutoff k)
      (Work.fixedOutputCommutator S velocity forcing cutoff k)

  work₁Exact : workAt k₁ ≡ - 48
  work₁Exact =
    trans (cong₂ Work.coherentWork (mixed₁ E) (comm₁ E)) Vector.w₁Exact

  work₂Exact : workAt k₂ ≡ (+ 322917) Data.Rational.Base./ 250
  work₂Exact =
    trans (cong₂ Work.coherentWork (mixed₂ E) (comm₂ E)) Vector.w₂Exact

  work₃Exact : workAt k₃ ≡ - 48
  work₃Exact =
    trans (cong₂ Work.coherentWork (mixed₃ E) (comm₃ E)) Vector.w₃Exact

  work₄Exact : workAt k₄ ≡ - ((+ 428272) Data.Rational.Base./ 125)
  work₄Exact =
    trans (cong₂ Work.coherentWork (mixed₄ E) (comm₄ E)) Vector.w₄Exact

  work₅Exact : workAt k₅ ≡ - ((+ 428272) Data.Rational.Base./ 125)
  work₅Exact =
    trans (cong₂ Work.coherentWork (mixed₅ E) (comm₅ E)) Vector.w₅Exact

  work₆Exact : workAt k₆ ≡ - 48
  work₆Exact =
    trans (cong₂ Work.coherentWork (mixed₆ E) (comm₆ E)) Vector.w₆Exact

  work₇Exact : workAt k₇ ≡ (+ 322917) Data.Rational.Base./ 250
  work₇Exact =
    trans (cong₂ Work.coherentWork (mixed₇ E) (comm₇ E)) Vector.w₇Exact

  work₈Exact : workAt k₈ ≡ - 48
  work₈Exact =
    trans (cong₂ Work.coherentWork (mixed₈ E) (comm₈ E)) Vector.w₈Exact

round829DRemainingBoundaryIsOnlyConcreteOperatorEvaluation : Bool
round829DRemainingBoundaryIsOnlyConcreteOperatorEvaluation = true

round829DGlobalHelicalProjectorLawsRequired : Bool
round829DGlobalHelicalProjectorLawsRequired = false

round829DIntroducesEstimate : Bool
round829DIntroducesEstimate = false

round829DClayPromotion : Bool
round829DClayPromotion = false

round829DRemainingBoundaryIsOnlyConcreteOperatorEvaluationIsTrue :
  round829DRemainingBoundaryIsOnlyConcreteOperatorEvaluation ≡ true
round829DRemainingBoundaryIsOnlyConcreteOperatorEvaluationIsTrue = refl
