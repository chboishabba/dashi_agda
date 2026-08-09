module DASHI.Physics.YangMills.BalabanSelectedMultiplierDefectGreenContractionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Replace the opaque KKT-repair norm by the exact two-source contraction
--
--   <K+ Lg,Lw> = <Lg,K+ Lw>,    K=LL*.
--
-- The two visible sources are s=Lg and delta=Lw.  This is the representation
-- on which support separation, D4 pairing and cancellation-before-
-- majorisation act.  It is proved solely from the certified self-adjoint
-- Moore--Penrose matrix; no inverse on redundant multiplier rows is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo

constraintSource : ∀ {Multiplier} →
  Pseudo.FiniteKKTPseudoinverseData Multiplier →
  KKT.StateVector → Pseudo.MultiplierVector Multiplier
constraintSource = Pseudo.constraintApply

constraintGreenSource : ∀ {Multiplier} →
  Pseudo.FiniteKKTPseudoinverseData Multiplier →
  KKT.StateVector → Pseudo.MultiplierVector Multiplier
constraintGreenSource pseudoData vector =
  Pseudo.pseudoApply pseudoData
    (constraintSource pseudoData vector)

canonicalMultiplierDefectContraction : ∀ {Multiplier} →
  Pseudo.FiniteKKTPseudoinverseData Multiplier →
  KKT.StateVector → KKT.StateVector → ℚ
canonicalMultiplierDefectContraction pseudoData covector rawVariation =
  Rect.finiteDot
    (Pseudo.multiplierCarrier pseudoData)
    (constraintGreenSource pseudoData covector)
    (constraintSource pseudoData rawVariation)

twoSourceGreenContraction : ∀ {Multiplier} →
  Pseudo.FiniteKKTPseudoinverseData Multiplier →
  KKT.StateVector → KKT.StateVector → ℚ
twoSourceGreenContraction pseudoData covector rawVariation =
  Rect.finiteDot
    (Pseudo.multiplierCarrier pseudoData)
    (constraintSource pseudoData covector)
    (constraintGreenSource pseudoData rawVariation)

selectedMultiplierDefectGreenContractionExact :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    covector rawVariation →
  canonicalMultiplierDefectContraction
    pseudoData covector rawVariation
  ≡ twoSourceGreenContraction
      pseudoData covector rawVariation
selectedMultiplierDefectGreenContractionExact
    pseudoData covector rawVariation =
  sym
    (Rect.symmetricMatrixMovesAcrossDot
      (Pseudo.multiplierCarrier pseudoData)
      (Pseudo.gramPseudoinverse pseudoData)
      (Pseudo.gramPseudoinverseSymmetric pseudoData)
      (constraintSource pseudoData covector)
      (constraintSource pseudoData rawVariation))

fullInverseMultiplierDefectGreenContractionExact :
  ∀ {Multiplier}
    (projectorData : KKT.FiniteKKTProjectorData Multiplier)
    covector rawVariation →
  canonicalMultiplierDefectContraction
    (Pseudo.fullInverseToPseudoinverse projectorData)
    covector rawVariation
  ≡ twoSourceGreenContraction
      (Pseudo.fullInverseToPseudoinverse projectorData)
      covector rawVariation
fullInverseMultiplierDefectGreenContractionExact projectorData =
  selectedMultiplierDefectGreenContractionExact
    (Pseudo.fullInverseToPseudoinverse projectorData)

multiplierGreenTwoSourceRepresentationLevel : ProofLevel
multiplierGreenTwoSourceRepresentationLevel = machineChecked
