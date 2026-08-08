module DASHI.Physics.YangMills.BalabanSelectedConstraintAnnihilatorKKTExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Franco Brezzi,
-- "On the Existence, Uniqueness and Approximation of Saddle-Point Problems
-- Arising from Lagrangian Multipliers",
-- RAIRO Analyse Numérique 8 (1974), 129--151.
-- No DOI was assigned to the cited article.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- Prove the finite annihilator theorem needed by the selected-background KKT
-- equation.  If a first-variation covector g annihilates every admissible
-- tangent h in ker L, then the orthogonal KKT projector satisfies P g = 0.
-- Consequently
--
--   g = L* K+ L g.
--
-- Thus g lies in im L* and the canonical multiplier is K+ L g.  A second
-- theorem proves that any two multipliers differ by an element of ker L*.
-- No coordinate Gaussian elimination or hidden row deletion is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
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
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo

stateDotLeftPointwiseCong :
  ∀ {left right : KKT.StateVector} →
  (∀ coordinate → left coordinate ≡ right coordinate) →
  ∀ vector →
  KKT.stateDot left vector ≡ KKT.stateDot right vector
stateDotLeftPointwiseCong {left} {right} pointwise vector =
  Sums.sumRationalCong
    (Matrix.coordinates KKT.physicalStateCarrier)
    (λ coordinate → left coordinate * vector coordinate)
    (λ coordinate → right coordinate * vector coordinate)
    (λ coordinate →
      cong (_* vector coordinate) (pointwise coordinate))

stateDotRightPointwiseCong :
  ∀ {left right : KKT.StateVector} →
  (∀ coordinate → left coordinate ≡ right coordinate) →
  ∀ vector →
  KKT.stateDot vector left ≡ KKT.stateDot vector right
stateDotRightPointwiseCong {left} {right} pointwise vector =
  trans
    (Rect.finiteDotSymmetric KKT.physicalStateCarrier vector left)
    (trans
      (stateDotLeftPointwiseCong pointwise vector)
      (Rect.finiteDotSymmetric KKT.physicalStateCarrier right vector))

record AnnihilatesConstraintKernel
    {Multiplier : Set}
    (data : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (covector : KKT.StateVector) : Set₁ where
  field
    annihilates : ∀ tangent →
      Pseudo.ConstraintKernel data tangent →
      KKT.stateDot covector tangent ≡ 0ℚ

open AnnihilatesConstraintKernel public

projectedCovectorNormZero :
  ∀ {Multiplier}
    (data : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    covector →
  AnnihilatesConstraintKernel data covector →
  KKT.stateNormSq (Pseudo.admissibleProject data covector) ≡ 0ℚ
projectedCovectorNormZero data covector critical =
  let
    projected = Pseudo.admissibleProject data covector

    annihilated :
      KKT.stateDot covector projected ≡ 0ℚ
    annihilated =
      annihilates critical projected
        (Pseudo.projectConstraintZero data covector)

    selfAdjointStep :
      KKT.stateDot projected projected
      ≡ KKT.stateDot
          (Pseudo.admissibleProject data projected)
          covector
    selfAdjointStep =
      Pseudo.projectSelfAdjoint data projected covector

    idempotentLeft :
      KKT.stateDot
        (Pseudo.admissibleProject data projected)
        covector
      ≡ KKT.stateDot projected covector
    idempotentLeft =
      stateDotLeftPointwiseCong
        (Pseudo.projectIdempotent data covector)
        covector
  in
  trans selfAdjointStep
    (trans idempotentLeft
      (trans
        (Rect.finiteDotSymmetric
          KKT.physicalStateCarrier projected covector)
        annihilated))

projectedCovectorPointwiseZero :
  ∀ {Multiplier}
    (data : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    covector →
  AnnihilatesConstraintKernel data covector →
  ∀ coordinate →
  Pseudo.admissibleProject data covector coordinate ≡ 0ℚ
projectedCovectorPointwiseZero data covector critical =
  KKT.stateNormSqZeroPointwise
    (Pseudo.admissibleProject data covector)
    (projectedCovectorNormZero data covector critical)

canonicalKKTMultiplier :
  ∀ {Multiplier} →
  Pseudo.FiniteKKTPseudoinverseData Multiplier →
  KKT.StateVector → Pseudo.MultiplierVector Multiplier
canonicalKKTMultiplier data covector =
  Pseudo.pseudoApply data (Pseudo.constraintApply data covector)

finiteAnnihilatorKernelEqualsAdjointImage :
  ∀ {Multiplier}
    (data : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    covector →
  AnnihilatesConstraintKernel data covector →
  ∀ coordinate →
  covector coordinate
  ≡ Pseudo.constraintAdjointApply data
      (canonicalKKTMultiplier data covector)
      coordinate
finiteAnnihilatorKernelEqualsAdjointImage
    data covector critical coordinate =
  let
    projectedZero =
      projectedCovectorPointwiseZero
        data covector critical coordinate
  in
  trans
    (sym
      (ℚRing.solve-∀
        (covector coordinate)
        (Pseudo.constraintRepair data covector coordinate)))
    (trans
      (cong
        (_+ Pseudo.constraintRepair data covector coordinate)
        projectedZero)
      (ℚRing.solve-∀
        (Pseudo.constraintRepair data covector coordinate)))

record KKTMultiplierWitness
    {Multiplier : Set}
    (data : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (covector : KKT.StateVector) : Set₁ where
  field
    multiplier : Pseudo.MultiplierVector Multiplier
    covectorIsAdjoint : ∀ coordinate →
      covector coordinate
      ≡ Pseudo.constraintAdjointApply data multiplier coordinate

open KKTMultiplierWitness public

selectedKKTMultiplierExistence :
  ∀ {Multiplier}
    (data : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    covector →
  AnnihilatesConstraintKernel data covector →
  KKTMultiplierWitness data covector
selectedKKTMultiplierExistence data covector critical = record
  { multiplier = canonicalKKTMultiplier data covector
  ; covectorIsAdjoint =
      finiteAnnihilatorKernelEqualsAdjointImage
        data covector critical
  }

record MultiplierRedundancy
    {Multiplier : Set}
    (data : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (multiplier : Pseudo.MultiplierVector Multiplier) : Set where
  field
    adjointZero : ∀ coordinate →
      Pseudo.constraintAdjointApply data multiplier coordinate ≡ 0ℚ

open MultiplierRedundancy public

multiplierSubtract :
  ∀ {Multiplier} →
  Pseudo.MultiplierVector Multiplier →
  Pseudo.MultiplierVector Multiplier →
  Pseudo.MultiplierVector Multiplier
multiplierSubtract left right row = left row - right row

adjointSubtractExact :
  ∀ {Multiplier}
    (data : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    left right coordinate →
  Pseudo.constraintAdjointApply data
    (multiplierSubtract left right) coordinate
  ≡ Pseudo.constraintAdjointApply data left coordinate
    - Pseudo.constraintAdjointApply data right coordinate
adjointSubtractExact data left right coordinate =
  Rect.applyRectangularSubtract
    (Pseudo.multiplierCarrier data)
    (Rect.transposeRectangular (Pseudo.constraintMatrix data))
    left right coordinate

selectedKKTMultiplierUniquenessModuloRedundancy :
  ∀ {Multiplier}
    (data : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    covector
    (left right : KKTMultiplierWitness data covector) →
  MultiplierRedundancy data
    (multiplierSubtract
      (multiplier left)
      (multiplier right))
selectedKKTMultiplierUniquenessModuloRedundancy
    data covector left right = record
  { adjointZero = λ coordinate →
      trans
        (adjointSubtractExact data
          (multiplier left) (multiplier right) coordinate)
        (trans
          (cong₂ _-_
            (sym (covectorIsAdjoint left coordinate))
            (sym (covectorIsAdjoint right coordinate)))
          (ℚRing.solve-∀ (covector coordinate)))
  }

annihilatorKernelEqualsAdjointImageLevel : ProofLevel
annihilatorKernelEqualsAdjointImageLevel = machineChecked

kktMultiplierModuloRedundancyLevel : ProofLevel
kktMultiplierModuloRedundancyLevel = machineChecked

selectedFirstVariationAnnihilatesTangentProducerLevel : ProofLevel
selectedFirstVariationAnnihilatesTangentProducerLevel = conditional
