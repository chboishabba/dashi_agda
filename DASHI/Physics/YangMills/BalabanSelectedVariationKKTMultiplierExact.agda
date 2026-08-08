module DASHI.Physics.YangMills.BalabanSelectedVariationKKTMultiplierExact where

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
-- Jerrold E. Marsden and Matthew West,
-- "Discrete Mechanics and Variational Integrators",
-- Acta Numerica 10 (2001), 357--514.
-- DOI: 10.1017/S096249290100006X.
--
-- DASHI CONTRIBUTION
--
-- Replace three independently named stationarity residuals by one finite KKT
-- equation.  If the literal first-variation covector satisfies
--
--   g = L* lambda,
--
-- then the exact KKT projector gives
--
--   dA(P w) = 0,
--   dA((I-P)w) = <lambda, L w>.
--
-- The second identity moves the 3072-coordinate projector-defect estimate into
-- the smaller multiplier space.  The module also generalizes the Round-37
-- raw/projected/discarded split from Boolean masks to the non-diagonal KKT
-- projector.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical

record SelectedKKTStationaryData (Multiplier : Set) : Set₁ where
  field
    projectorData : KKT.FiniteKKTProjectorData Multiplier
    firstVariationCovector : KKT.StateVector
    kktMultiplier : Multiplier → ℚ

    firstVariationIsConstraintAdjoint :
      ∀ coordinate →
      firstVariationCovector coordinate
      ≡ KKT.constraintAdjointApply
          projectorData kktMultiplier coordinate

open SelectedKKTStationaryData public

firstVariation :
  ∀ {Multiplier} →
  SelectedKKTStationaryData Multiplier →
  KKT.StateVector → ℚ
firstVariation data vector =
  KKT.stateDot (firstVariationCovector data) vector

stateDotLeftPointwiseCong :
  ∀ {left right : KKT.StateVector} →
  (∀ coordinate → left coordinate ≡ right coordinate) →
  ∀ vector →
  KKT.stateDot left vector ≡ KKT.stateDot right vector
stateDotLeftPointwiseCong {left} {right} pointwise vector =
  Sums.sumRationalCong
    Physical.physicalSU2Coordinates4
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
    (Rect.finiteDotSymmetric
      KKT.physicalStateCarrier vector left)
    (trans
      (stateDotLeftPointwiseCong pointwise vector)
      (Rect.finiteDotSymmetric
        KKT.physicalStateCarrier right vector))

firstVariationRawSplitsProjectedRepair :
  ∀ {Multiplier}
    (data : SelectedKKTStationaryData Multiplier)
    vector →
  firstVariation data vector
  ≡ firstVariation data
      (KKT.selectedAdmissibleProject
        (projectorData data) vector)
    + firstVariation data
      (KKT.selectedConstraintRepair
        (projectorData data) vector)
firstVariationRawSplitsProjectedRepair data vector =
  trans
    (stateDotRightPointwiseCong
      (KKT.selectedAdmissibleOrthogonalDecompositionPointwise
        (projectorData data) vector)
      (firstVariationCovector data))
    (Rect.finiteDotAddRight
      KKT.physicalStateCarrier
      (firstVariationCovector data)
      (KKT.selectedAdmissibleProject
        (projectorData data) vector)
      (KKT.selectedConstraintRepair
        (projectorData data) vector))

projectedFirstVariationIsRawMinusRepair :
  ∀ {Multiplier}
    (data : SelectedKKTStationaryData Multiplier)
    vector →
  firstVariation data
      (KKT.selectedAdmissibleProject
        (projectorData data) vector)
  ≡ firstVariation data vector
    - firstVariation data
      (KKT.selectedConstraintRepair
        (projectorData data) vector)
projectedFirstVariationIsRawMinusRepair data vector =
  let
    raw = firstVariation data vector
    projected =
      firstVariation data
        (KKT.selectedAdmissibleProject
          (projectorData data) vector)
    repair =
      firstVariation data
        (KKT.selectedConstraintRepair
          (projectorData data) vector)
  in
  trans
    (sym (ℚRing.solve-∀ projected repair))
    (trans
      (cong (_- repair)
        (sym
          (firstVariationRawSplitsProjectedRepair
            data vector)))
      (ℚRing.solve-∀ raw repair))

projectedFirstVariationStationaryFromKKT :
  ∀ {Multiplier}
    (data : SelectedKKTStationaryData Multiplier)
    vector →
  firstVariation data
    (KKT.selectedAdmissibleProject
      (projectorData data) vector)
  ≡ 0ℚ
projectedFirstVariationStationaryFromKKT data vector =
  let
    projected =
      KKT.selectedAdmissibleProject
        (projectorData data) vector

    adjointForm :
      KKT.stateDot
        (firstVariationCovector data) projected
      ≡ KKT.stateDot
          (KKT.constraintAdjointApply
            (projectorData data)
            (kktMultiplier data))
          projected
    adjointForm =
      stateDotLeftPointwiseCong
        (firstVariationIsConstraintAdjoint data)
        projected
  in
  trans adjointForm
    (trans
      (Rect.finiteDotSymmetric
        KKT.physicalStateCarrier
        (KKT.constraintAdjointApply
          (projectorData data)
          (kktMultiplier data))
        projected)
      (KKT.selectedAdmissibleRepairOrthogonal
        (projectorData data)
        projected
        (kktMultiplier data)
        (KKT.selectedProjectorConstraintZero
          (projectorData data) vector)))

projectorDefectFirstVariationMultiplierIdentity :
  ∀ {Multiplier}
    (data : SelectedKKTStationaryData Multiplier)
    vector →
  firstVariation data
    (KKT.selectedConstraintRepair
      (projectorData data) vector)
  ≡ KKT.multiplierDot
      (projectorData data)
      (kktMultiplier data)
      (KKT.constraintApply
        (projectorData data) vector)
projectorDefectFirstVariationMultiplierIdentity data vector =
  let
    projector = projectorData data
    repair = KKT.selectedConstraintRepair projector vector
    multiplier = kktMultiplier data

    replaceCovector :
      KKT.stateDot
        (firstVariationCovector data) repair
      ≡ KKT.stateDot
          (KKT.constraintAdjointApply projector multiplier)
          repair
    replaceCovector =
      stateDotLeftPointwiseCong
        (firstVariationIsConstraintAdjoint data)
        repair
  in
  trans replaceCovector
    (trans
      (Rect.finiteDotSymmetric
        KKT.physicalStateCarrier
        (KKT.constraintAdjointApply projector multiplier)
        repair)
      (trans
        (sym
          (Rect.rectangularAdjointExact
            (KKT.multiplierCarrier projector)
            KKT.physicalStateCarrier
            (KKT.constraintMatrix projector)
            repair multiplier))
        (trans
          (Sums.sumRationalCong
            (Matrix.coordinates
              (KKT.multiplierCarrier projector))
            (λ row →
              KKT.constraintApply projector repair row
                * multiplier row)
            (λ row →
              KKT.constraintApply projector vector row
                * multiplier row)
            (λ row →
              cong (_* multiplier row)
                (KKT.constraintRepairExact
                  projector vector row)))
          (Rect.finiteDotSymmetric
            (KKT.multiplierCarrier projector)
            (KKT.constraintApply projector vector)
            multiplier))))

projectorDefectUpperReducesToMultiplier :
  ∀ {Multiplier}
    (data : SelectedKKTStationaryData Multiplier)
    vector bound →
  - KKT.multiplierDot
      (projectorData data)
      (kktMultiplier data)
      (KKT.constraintApply
        (projectorData data) vector)
    ≤ bound →
  - firstVariation data
      (KKT.selectedConstraintRepair
        (projectorData data) vector)
    ≤ bound
projectorDefectUpperReducesToMultiplier data vector bound multiplierBound =
  subst
    (λ selected → - selected ≤ bound)
    (sym
      (projectorDefectFirstVariationMultiplierIdentity
        data vector))
    multiplierBound

projectedStationarityAndDefectShareKKTMultiplier :
  ∀ {Multiplier}
    (data : SelectedKKTStationaryData Multiplier)
    vector →
  firstVariation data
      (KKT.selectedAdmissibleProject
        (projectorData data) vector)
      ≡ 0ℚ
  ×
  firstVariation data
      (KKT.selectedConstraintRepair
        (projectorData data) vector)
      ≡ KKT.multiplierDot
          (projectorData data)
          (kktMultiplier data)
          (KKT.constraintApply
            (projectorData data) vector)
projectedStationarityAndDefectShareKKTMultiplier data vector =
  projectedFirstVariationStationaryFromKKT data vector
  , projectorDefectFirstVariationMultiplierIdentity data vector

kktStationarityLevel : ProofLevel
kktStationarityLevel = machineChecked

kktMultiplierDefectReductionLevel : ProofLevel
kktMultiplierDefectReductionLevel = machineChecked

selectedKKTMultiplierEquationProducerLevel : ProofLevel
selectedKKTMultiplierEquationProducerLevel = conditional
