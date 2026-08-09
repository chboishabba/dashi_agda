module DASHI.Physics.YangMills.BalabanSelectedMultiplierGreenContractionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- Rewrite the canonical multiplier spillover as the exact two-source Green
-- contraction
--
--   <K^{-1} Lg,Lw> = <Lg,K^{-1}Lw>
--                    = sum_(x,y) s(x) K^{-1}(x,y) delta(y).
--
-- This is the representation needed for support separation, D4 orbit
-- reduction and cancellation before absolute values.  The equality uses the
-- certified symmetry of the finite multiplier Green matrix and literal finite
-- sums only.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT

constraintSource :
  ∀ {Multiplier} →
  KKT.FiniteKKTProjectorData Multiplier →
  KKT.StateVector → Multiplier → ℚ
constraintSource = KKT.constraintApply

canonicalMultiplier :
  ∀ {Multiplier} →
  KKT.FiniteKKTProjectorData Multiplier →
  KKT.StateVector → Multiplier → ℚ
canonicalMultiplier projectorData vector =
  KKT.multiplierGreenApply projectorData
    (constraintSource projectorData vector)

selectedMultiplierDefectGreenContractionExact :
  ∀ {Multiplier}
    (projectorData : KKT.FiniteKKTProjectorData Multiplier)
    firstVariationCovector rawExtractor →
  KKT.multiplierDot projectorData
    (canonicalMultiplier projectorData firstVariationCovector)
    (constraintSource projectorData rawExtractor)
  ≡ KKT.multiplierDot projectorData
      (constraintSource projectorData firstVariationCovector)
      (KKT.multiplierGreenApply projectorData
        (constraintSource projectorData rawExtractor))
selectedMultiplierDefectGreenContractionExact
    projectorData firstVariationCovector rawExtractor =
  Rect.symmetricMatrixMovesAcrossDot
    (KKT.multiplierCarrier projectorData)
    (KKT.multiplierGreen projectorData)
    (KKT.gramInverseSymmetric projectorData)
    (constraintSource projectorData firstVariationCovector)
    (constraintSource projectorData rawExtractor)

greenContractionAtom :
  ∀ {Multiplier} →
  KKT.FiniteKKTProjectorData Multiplier →
  (Multiplier → ℚ) → (Multiplier → ℚ) →
  Multiplier → Multiplier → ℚ
greenContractionAtom projectorData source defect left right =
  source left
    * (KKT.multiplierGreen projectorData left right * defect right)

greenContractionAtomPairSum :
  ∀ {Multiplier} →
  KKT.FiniteKKTProjectorData Multiplier →
  (Multiplier → ℚ) → (Multiplier → ℚ) → ℚ
greenContractionAtomPairSum projectorData source defect =
  Sums.sumRational
    (Matrix.coordinates (KKT.multiplierCarrier projectorData))
    (λ left →
      Sums.sumRational
        (Matrix.coordinates (KKT.multiplierCarrier projectorData))
        (greenContractionAtom projectorData source defect left))

greenContractionExpandsToAtomPairs :
  ∀ {Multiplier}
    (projectorData : KKT.FiniteKKTProjectorData Multiplier)
    source defect →
  KKT.multiplierDot projectorData source
    (KKT.multiplierGreenApply projectorData defect)
  ≡ greenContractionAtomPairSum projectorData source defect
greenContractionExpandsToAtomPairs projectorData source defect =
  Sums.sumRationalCong
    (Matrix.coordinates (KKT.multiplierCarrier projectorData))
    (λ left →
      source left
        * KKT.multiplierGreenApply projectorData defect left)
    (λ left →
      Sums.sumRational
        (Matrix.coordinates (KKT.multiplierCarrier projectorData))
        (greenContractionAtom projectorData source defect left))
    (λ left →
      sym
        (Sums.sumRationalScale
          (source left)
          (Matrix.coordinates (KKT.multiplierCarrier projectorData))
          (λ right →
            KKT.multiplierGreen projectorData left right
              * defect right)))

selectedMultiplierDefectAtomPairExpansion :
  ∀ {Multiplier}
    (projectorData : KKT.FiniteKKTProjectorData Multiplier)
    firstVariationCovector rawExtractor →
  KKT.multiplierDot projectorData
    (canonicalMultiplier projectorData firstVariationCovector)
    (constraintSource projectorData rawExtractor)
  ≡ greenContractionAtomPairSum projectorData
      (constraintSource projectorData firstVariationCovector)
      (constraintSource projectorData rawExtractor)
selectedMultiplierDefectAtomPairExpansion
    projectorData firstVariationCovector rawExtractor =
  trans
    (selectedMultiplierDefectGreenContractionExact
      projectorData firstVariationCovector rawExtractor)
    (greenContractionExpandsToAtomPairs
      projectorData
      (constraintSource projectorData firstVariationCovector)
      (constraintSource projectorData rawExtractor))

multiplierGreenContractionLevel : ProofLevel
multiplierGreenContractionLevel = machineChecked

multiplierGreenAtomPairExpansionLevel : ProofLevel
multiplierGreenAtomPairExpansionLevel = machineChecked
