module DASHI.Physics.YangMills.BalabanSelectedMultiplierPairingRedundancyInvariantExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Franco Brezzi,
-- "On the Existence, Uniqueness and Approximation of Saddle-Point Problems
-- Arising from Lagrangian Multipliers",
-- RAIRO Analyse Numérique 8 (1974), 129--151.
-- No DOI was assigned to the cited article.
--
-- DASHI CONTRIBUTION
--
-- Prove that the selected projector-defect pairing is independent of the
-- multiplier representative.  A redundancy r satisfies L* r=0, hence
--
--   <r,Lw> = <L*r,w> = 0.
--
-- Therefore every KKT multiplier representing the same first variation gives
-- exactly the canonical Moore--Penrose defect pairing.  This closes the
-- public authority boundary without deleting redundant constraint rows.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedConstraintAnnihilatorKKTExact as Annihilator

multiplierDefectPairing :
  ∀ {Multiplier} →
  Pseudo.FiniteKKTPseudoinverseData Multiplier →
  Pseudo.MultiplierVector Multiplier →
  KKT.StateVector → ℚ
multiplierDefectPairing pseudoData multiplier vector =
  Rect.finiteDot
    (Pseudo.multiplierCarrier pseudoData)
    multiplier
    (Pseudo.constraintApply pseudoData vector)

stateDotRightPointwiseCong :
  ∀ {left right : KKT.StateVector} →
  (∀ coordinate → left coordinate ≡ right coordinate) →
  ∀ vector →
  KKT.stateDot vector left ≡ KKT.stateDot vector right
stateDotRightPointwiseCong {left} {right} pointwise vector =
  Sums.sumRationalCong
    (Matrix.coordinates KKT.physicalStateCarrier)
    (λ coordinate → vector coordinate * left coordinate)
    (λ coordinate → vector coordinate * right coordinate)
    (λ coordinate →
      cong (vector coordinate *_) (pointwise coordinate))

multiplierDefectPairingIgnoresRedundancy :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    multiplier vector →
  Annihilator.MultiplierRedundancy pseudoData multiplier →
  multiplierDefectPairing pseudoData multiplier vector ≡ 0ℚ
multiplierDefectPairingIgnoresRedundancy
    pseudoData multiplier vector redundancy =
  trans
    (Rect.finiteDotSymmetric
      (Pseudo.multiplierCarrier pseudoData)
      multiplier
      (Pseudo.constraintApply pseudoData vector))
    (trans
      (Rect.rectangularAdjointExact
        (Pseudo.multiplierCarrier pseudoData)
        KKT.physicalStateCarrier
        (KKT.constraintMatrix (Pseudo.projectorData pseudoData))
        vector multiplier)
      (trans
        (stateDotRightPointwiseCong
          (Annihilator.adjointZero redundancy)
          vector)
        (Rect.finiteDotZeroRight
          KKT.physicalStateCarrier vector)))

pairingOfDifferenceIsDifference :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    left right vector →
  multiplierDefectPairing pseudoData
      (Annihilator.multiplierSubtract left right) vector
  ≡ multiplierDefectPairing pseudoData left vector
    - multiplierDefectPairing pseudoData right vector
pairingOfDifferenceIsDifference pseudoData left right vector =
  Rect.finiteDotSubtractLeft
    (Pseudo.multiplierCarrier pseudoData)
    left right
    (Pseudo.constraintApply pseudoData vector)

allKKTMultipliersGiveSameDefect :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    covector
    (left right : Annihilator.KKTMultiplierWitness pseudoData covector)
    vector →
  multiplierDefectPairing pseudoData
    (Annihilator.multiplier left) vector
  ≡ multiplierDefectPairing pseudoData
    (Annihilator.multiplier right) vector
allKKTMultipliersGiveSameDefect
    pseudoData covector left right vector =
  let
    redundancy =
      Annihilator.selectedKKTMultiplierUniquenessModuloRedundancy
        pseudoData covector left right

    differenceZero :
      multiplierDefectPairing pseudoData
        (Annihilator.multiplierSubtract
          (Annihilator.multiplier left)
          (Annihilator.multiplier right))
        vector
      ≡ 0ℚ
    differenceZero =
      multiplierDefectPairingIgnoresRedundancy
        pseudoData
        (Annihilator.multiplierSubtract
          (Annihilator.multiplier left)
          (Annihilator.multiplier right))
        vector redundancy
  in
  trans
    (sym
      (ℚRing.solve-∀
        (multiplierDefectPairing pseudoData
          (Annihilator.multiplier left) vector)
        (multiplierDefectPairing pseudoData
          (Annihilator.multiplier right) vector)))
    (trans
      (cong
        (λ selected → selected
          + multiplierDefectPairing pseudoData
              (Annihilator.multiplier right) vector)
        (trans
          (sym
            (pairingOfDifferenceIsDifference
              pseudoData
              (Annihilator.multiplier left)
              (Annihilator.multiplier right)
              vector))
          differenceZero))
      (ℚRing.solve-∀
        (multiplierDefectPairing pseudoData
          (Annihilator.multiplier right) vector)))

canonicalMultiplierDefectPairing :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    covector vector →
  Annihilator.AnnihilatesConstraintKernel pseudoData covector → ℚ
canonicalMultiplierDefectPairing pseudoData covector vector critical =
  multiplierDefectPairing pseudoData
    (Annihilator.canonicalKKTMultiplier pseudoData covector)
    vector

multiplierPairingRedundancyInvariantLevel : ProofLevel
multiplierPairingRedundancyInvariantLevel = machineChecked
