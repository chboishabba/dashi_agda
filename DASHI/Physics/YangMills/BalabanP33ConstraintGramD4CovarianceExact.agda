module DASHI.Physics.YangMills.BalabanP33ConstraintGramD4CovarianceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- Carry the Round-39 covariant D4 boundary through the actual multiplier
-- Green contraction.  Constraint and adjoint covariance imply Gram
-- covariance.  Once the Moore--Penrose action is also covariant, simultaneous
-- transport of the source and defect leaves
--
--   <s,K+ delta>
--
-- invariant.  Thus a D4 orbit reduction is licensed only by the complete
-- transported kernel, not by a slot permutation alone.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo

record ConstraintD4Covariance
    {Multiplier : Set}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier) : Set₁ where
  field
    D4Element : Set
    stateTransport : D4Element → KKT.StateVector → KKT.StateVector
    multiplierTransport :
      D4Element → Pseudo.MultiplierVector Multiplier →
      Pseudo.MultiplierVector Multiplier

    constraintCovariant : ∀ symmetry state row →
      Pseudo.constraintApply pseudoData
        (stateTransport symmetry state) row
      ≡ multiplierTransport symmetry
          (Pseudo.constraintApply pseudoData state) row

    adjointCovariant : ∀ symmetry multiplier coordinate →
      Pseudo.constraintAdjointApply pseudoData
        (multiplierTransport symmetry multiplier) coordinate
      ≡ stateTransport symmetry
          (Pseudo.constraintAdjointApply pseudoData multiplier) coordinate

    multiplierDotInvariant : ∀ symmetry left right →
      Rect.finiteDot (Pseudo.multiplierCarrier pseudoData)
        (multiplierTransport symmetry left)
        (multiplierTransport symmetry right)
      ≡ Rect.finiteDot (Pseudo.multiplierCarrier pseudoData) left right

open ConstraintD4Covariance public

constraintGramCovariantUnderD4 :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    (covariance : ConstraintD4Covariance pseudoData)
    symmetry multiplier row →
  Pseudo.gramApply pseudoData
    (multiplierTransport covariance symmetry multiplier) row
  ≡ multiplierTransport covariance symmetry
      (Pseudo.gramApply pseudoData multiplier) row
constraintGramCovariantUnderD4 {pseudoData = pseudoData}
    covariance symmetry multiplier row =
  trans
    (constraintCovariant covariance symmetry
      (Pseudo.constraintAdjointApply pseudoData multiplier) row)
    (cong
      (λ transported →
        multiplierTransport covariance symmetry transported row)
      (Pseudo.constraintGramActionExact pseudoData multiplier row))

record ConstraintPseudoinverseD4Covariance
    {Multiplier : Set}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    (covariance : ConstraintD4Covariance pseudoData) : Set₁ where
  field
    pseudoinverseCovariant : ∀ symmetry multiplier row →
      Pseudo.pseudoApply pseudoData
        (multiplierTransport covariance symmetry multiplier) row
      ≡ multiplierTransport covariance symmetry
          (Pseudo.pseudoApply pseudoData multiplier) row
open ConstraintPseudoinverseD4Covariance public

constraintPseudoinverseCovariantUnderD4 :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {covariance : ConstraintD4Covariance pseudoData} →
  ConstraintPseudoinverseD4Covariance covariance →
  ∀ symmetry multiplier row →
  Pseudo.pseudoApply pseudoData
    (multiplierTransport covariance symmetry multiplier) row
  ≡ multiplierTransport covariance symmetry
      (Pseudo.pseudoApply pseudoData multiplier) row
constraintPseudoinverseCovariantUnderD4 = pseudoinverseCovariant

multiplierGreenPairing :
  ∀ {Multiplier} →
  Pseudo.FiniteKKTPseudoinverseData Multiplier →
  Pseudo.MultiplierVector Multiplier →
  Pseudo.MultiplierVector Multiplier → ℚ
multiplierGreenPairing pseudoData source defect =
  Rect.finiteDot (Pseudo.multiplierCarrier pseudoData)
    source (Pseudo.pseudoApply pseudoData defect)

finiteDotRightPointwiseCong :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    left {right transported} →
  (∀ row → right row ≡ transported row) →
  Rect.finiteDot (Pseudo.multiplierCarrier pseudoData) left right
  ≡ Rect.finiteDot (Pseudo.multiplierCarrier pseudoData) left transported
finiteDotRightPointwiseCong pseudoData left {right} {transported} pointwise =
  Sums.sumRationalCong
    (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
    (λ row → left row * right row)
    (λ row → left row * transported row)
    (λ row → cong (left row *_) (pointwise row))

multiplierGreenPairingOrbitInvariant :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    (covariance : ConstraintD4Covariance pseudoData) →
  ConstraintPseudoinverseD4Covariance covariance →
  ∀ symmetry source defect →
  multiplierGreenPairing pseudoData
    (multiplierTransport covariance symmetry source)
    (multiplierTransport covariance symmetry defect)
  ≡ multiplierGreenPairing pseudoData source defect
multiplierGreenPairingOrbitInvariant
    {pseudoData = pseudoData} covariance pseudoCovariance
    symmetry source defect =
  trans
    (finiteDotRightPointwiseCong pseudoData
      (multiplierTransport covariance symmetry source)
      (constraintPseudoinverseCovariantUnderD4
        pseudoCovariance symmetry defect))
    (multiplierDotInvariant covariance symmetry
      source (Pseudo.pseudoApply pseudoData defect))

record D4CorrectionInvariantGreenPairing
    {Multiplier : Set}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier) : Set₁ where
  field
    Correction : Set
    applyCorrection :
      Correction → Pseudo.MultiplierVector Multiplier →
      Pseudo.MultiplierVector Multiplier
    correctionLeavesPairing : ∀ correction source defect →
      multiplierGreenPairing pseudoData
        (applyCorrection correction source)
        (applyCorrection correction defect)
      ≡ multiplierGreenPairing pseudoData source defect
open D4CorrectionInvariantGreenPairing public

constraintGramD4CovarianceLevel : ProofLevel
constraintGramD4CovarianceLevel = machineChecked

multiplierGreenPairingOrbitInvariantLevel : ProofLevel
multiplierGreenPairingOrbitInvariantLevel = machineChecked

selectedD4PseudoinverseCovarianceProducerLevel : ProofLevel
selectedD4PseudoinverseCovarianceProducerLevel = conditional
