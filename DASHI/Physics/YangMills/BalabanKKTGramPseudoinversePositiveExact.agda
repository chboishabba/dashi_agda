module DASHI.Physics.YangMills.BalabanKKTGramPseudoinversePositiveExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- The Round58 G2 Green blocks use the SAME KKT Moore--Penrose pseudoinverse
-- K+ of K = L L*.  Positivity of K+ is not added as a new field.  It follows
-- from the already-carried Moore--Penrose action law
--
--   K+ K K+ y = K+ y
--
-- and the Gram factorization K=L L*:
--
--   <y,K+y>
--     = <K+ y, K K+ y>
--     = <L* K+ y, L* K+ y> >= 0.
--
-- This is the exact algebraic reduction needed before polarization can replace
-- sixteen sign-sensitive Green lower bounds by diagonal energies.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedConstraintAtomGreenExpansionExact as Green

pseudoinverseEnergy :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier) →
  (Multiplier → ℚ) → ℚ
pseudoinverseEnergy pseudoData vector =
  Rect.finiteDot
    (Pseudo.multiplierCarrier pseudoData)
    vector
    (Pseudo.pseudoApply pseudoData vector)

pseudoinverseEnergyAsAdjointNormSq :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    vector →
  pseudoinverseEnergy pseudoData vector
  ≡ Rect.finiteNormSq KKT.physicalStateCarrier
      (Pseudo.constraintAdjointApply pseudoData
        (Pseudo.pseudoApply pseudoData vector))
pseudoinverseEnergyAsAdjointNormSq pseudoData vector =
  let
    carrier = Pseudo.multiplierCarrier pseudoData
    u = Pseudo.pseudoApply pseudoData vector
    gramU = Pseudo.gramApply pseudoData u
    pseudoGramU = Pseudo.pseudoApply pseudoData gramU

    uToPseudoGramU : ∀ row → u row ≡ pseudoGramU row
    uToPseudoGramU row =
      sym (Pseudo.pseudoGramPseudoAction pseudoData vector row)

    gramToConstraintAdjoint : ∀ row →
      gramU row
      ≡ Pseudo.constraintApply pseudoData
          (Pseudo.constraintAdjointApply pseudoData u) row
    gramToConstraintAdjoint row =
      sym (Pseudo.constraintGramActionExact pseudoData u row)
  in
  trans
    (Rect.finiteDotSymmetric carrier vector u)
    (trans
      (Green.finiteDotLeftPointwiseCong carrier uToPseudoGramU)
      (trans
        (sym
          (Rect.symmetricMatrixMovesAcrossDot
            carrier
            (Pseudo.gramPseudoinverse pseudoData)
            (Pseudo.gramPseudoinverseSymmetric pseudoData)
            gramU vector))
        (trans
          (Rect.finiteDotSymmetric carrier gramU u)
          (trans
            (Green.finiteDotRightPointwiseCong
              carrier gramToConstraintAdjoint)
            (trans
              (Rect.finiteDotSymmetric carrier u
                (Pseudo.constraintApply pseudoData
                  (Pseudo.constraintAdjointApply pseudoData u)))
              (Rect.rectangularAdjointExact
                carrier KKT.physicalStateCarrier
                (Pseudo.constraintMatrix pseudoData)
                (Pseudo.constraintAdjointApply pseudoData u)
                u))))))

pseudoinverseEnergyNonnegative :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    vector →
  0ℚ ≤ pseudoinverseEnergy pseudoData vector
pseudoinverseEnergyNonnegative pseudoData vector =
  subst
    (λ value → 0ℚ ≤ value)
    (sym (pseudoinverseEnergyAsAdjointNormSq pseudoData vector))
    (Rect.finiteNormSqNonnegative KKT.physicalStateCarrier
      (Pseudo.constraintAdjointApply pseudoData
        (Pseudo.pseudoApply pseudoData vector)))

kktGramPseudoinversePositiveSemidefiniteLevel : ProofLevel
kktGramPseudoinversePositiveSemidefiniteLevel = machineChecked
