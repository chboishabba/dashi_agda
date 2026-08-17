module DASHI.Physics.YangMills.BalabanKKTGramPseudoinversePositiveExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- The Round58 Green lower-bound problem uses the SAME KKT Gram
-- pseudoinverse K+ in all sixteen degree blocks.  Positivity of K+ is not an
-- additional physical assumption.  It follows exactly from the Moore--Penrose
-- action laws already carried by FiniteKKTPseudoinverseData and from
--
--   K = L L*.
--
-- Put z = K+ y.  Since K+ K K+ = K+ and K+ is symmetric,
--
--   <y,K+y>
--     = <K+y,y>
--     = <K+ K K+ y,y>
--     = <K K+ y,K+ y>
--     = <L* K+ y,L* K+ y>
--     >= 0.
--
-- Thus every repository-valid finite KKT Gram pseudoinverse is positive
-- semidefinite on the literal multiplier carrier; no spectral theorem and no
-- floating-point eigenvalue certificate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedConstraintAtomGreenExpansionExact as Green

pseudoTransposeApplyExact :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    vector row →
  Rect.applyRectangular
    (Pseudo.multiplierCarrier pseudoData)
    (Rect.transposeRectangular (Pseudo.gramPseudoinverse pseudoData))
    vector row
  ≡ Pseudo.pseudoApply pseudoData vector row
pseudoTransposeApplyExact pseudoData vector row =
  Sums.sumRationalCong
    (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
    _ _
    (λ column →
      cong (_* vector column)
        (Pseudo.gramPseudoinverseSymmetric pseudoData column row))

pseudoQuadratic :
  ∀ {Multiplier} →
  Pseudo.FiniteKKTPseudoinverseData Multiplier →
  Pseudo.MultiplierVector Multiplier → ℚ
pseudoQuadratic pseudoData vector =
  Rect.finiteDot
    (Pseudo.multiplierCarrier pseudoData)
    vector
    (Pseudo.pseudoApply pseudoData vector)

pseudoQuadraticAsAdjointNormSq :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    vector →
  pseudoQuadratic pseudoData vector
  ≡ Rect.finiteNormSq KKT.physicalStateCarrier
      (Pseudo.constraintAdjointApply pseudoData
        (Pseudo.pseudoApply pseudoData vector))
pseudoQuadraticAsAdjointNormSq pseudoData vector =
  let
    carrier = Pseudo.multiplierCarrier pseudoData
    pseudoVector = Pseudo.pseudoApply pseudoData vector
    gramPseudoVector = Pseudo.gramApply pseudoData pseudoVector
    adjointPseudoVector = Pseudo.constraintAdjointApply pseudoData pseudoVector

    step0 :
      Rect.finiteDot carrier vector pseudoVector
      ≡ Rect.finiteDot carrier pseudoVector vector
    step0 = Rect.finiteDotSymmetric carrier vector pseudoVector

    step1 :
      Rect.finiteDot carrier pseudoVector vector
      ≡ Rect.finiteDot carrier
          (Pseudo.pseudoApply pseudoData gramPseudoVector) vector
    step1 = Green.finiteDotLeftPointwiseCong carrier
      (λ row → sym (Pseudo.pseudoGramPseudoAction pseudoData vector row))

    step2 :
      Rect.finiteDot carrier
          (Pseudo.pseudoApply pseudoData gramPseudoVector) vector
      ≡ Rect.finiteDot carrier gramPseudoVector pseudoVector
    step2 = trans
      (Rect.rectangularAdjointExact
        carrier carrier
        (Pseudo.gramPseudoinverse pseudoData)
        gramPseudoVector vector)
      (Green.finiteDotRightPointwiseCong carrier
        (pseudoTransposeApplyExact pseudoData vector))

    step3 :
      Rect.finiteDot carrier gramPseudoVector pseudoVector
      ≡ Rect.finiteDot carrier
          (Pseudo.constraintApply pseudoData adjointPseudoVector)
          pseudoVector
    step3 = Green.finiteDotLeftPointwiseCong carrier
      (λ row → sym
        (Pseudo.constraintGramActionExact pseudoData pseudoVector row))

    step4 :
      Rect.finiteDot carrier
          (Pseudo.constraintApply pseudoData adjointPseudoVector)
          pseudoVector
      ≡ Rect.finiteDot KKT.physicalStateCarrier
          adjointPseudoVector adjointPseudoVector
    step4 = Rect.rectangularAdjointExact
      carrier KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData)
      adjointPseudoVector pseudoVector
  in
  trans step0 (trans step1 (trans step2 (trans step3 step4)))

pseudoQuadraticNonnegative :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    vector →
  0ℚ ≤ pseudoQuadratic pseudoData vector
pseudoQuadraticNonnegative pseudoData vector =
  subst
    (λ selected → 0ℚ ≤ selected)
    (sym (pseudoQuadraticAsAdjointNormSq pseudoData vector))
    (Rect.finiteNormSqNonnegative KKT.physicalStateCarrier
      (Pseudo.constraintAdjointApply pseudoData
        (Pseudo.pseudoApply pseudoData vector)))
  where
  open import Relation.Binary.PropositionalEquality using (subst)

kktGramPseudoinversePositiveSemidefiniteLevel : ProofLevel
kktGramPseudoinversePositiveSemidefiniteLevel = machineChecked
