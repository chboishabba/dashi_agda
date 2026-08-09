module DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintFiniteKKTExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Franco Brezzi,
-- "On the Existence, Uniqueness and Approximation of Saddle-Point Problems
-- Arising from Lagrangian Multipliers",
-- RAIRO Analyse Numerique 8 (1974), 129--151.
-- No DOI was assigned to the cited article.
--
-- DASHI CONTRIBUTION
--
-- Put the literal combined constraint matrix on the concrete 780-row finite
-- carrier and close the finite KKT algebra before inversion.  The matrix Gram
-- action is proved equal to L_A(L_A* lambda), the finite adjoint identity is
-- inherited from rectangular Fubini, and the Gram quadratic is proved equal to
-- ||L_A* lambda||^2 and hence nonnegative.  No pseudoinverse, rank floor or
-- redundancy quotient is assumed in these statements.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact as Combined
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows

SelectedMultiplierVector : Set
SelectedMultiplierVector = Combined.SelectedConstraintRow4 → ℚ

selectedCombinedConstraintTransposeApply :
  Physical.RationalSU2Background4 →
  SelectedMultiplierVector → KKT.StateVector
selectedCombinedConstraintTransposeApply background =
  Rect.applyRectangular Rows.selectedCombinedConstraintRowCarrier
    (Rect.transposeRectangular
      (Combined.selectedBackgroundLinearizedConstraintMatrix background))

selectedCombinedConstraintGramApply :
  Physical.RationalSU2Background4 →
  SelectedMultiplierVector → SelectedMultiplierVector
selectedCombinedConstraintGramApply background =
  Rect.applyRectangular Rows.selectedCombinedConstraintRowCarrier
    (Combined.selectedBackgroundConstraintGram background)

selectedCombinedConstraintGramActionExact :
  ∀ background multiplier row →
  selectedCombinedConstraintGramApply background multiplier row
  ≡ Combined.selectedBackgroundCombinedConstraintApply background
      (selectedCombinedConstraintTransposeApply background multiplier) row
selectedCombinedConstraintGramActionExact background multiplier row =
  Rect.applyComposeRectangularExact
    KKT.physicalStateCarrier
    Rows.selectedCombinedConstraintRowCarrier
    (Combined.selectedBackgroundLinearizedConstraintMatrix background)
    (Rect.transposeRectangular
      (Combined.selectedBackgroundLinearizedConstraintMatrix background))
    multiplier row

selectedCombinedConstraintAdjointExact :
  ∀ background state multiplier →
  Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
    (Combined.selectedBackgroundCombinedConstraintApply background state)
    multiplier
  ≡ Rect.finiteDot KKT.physicalStateCarrier state
      (selectedCombinedConstraintTransposeApply background multiplier)
selectedCombinedConstraintAdjointExact background state multiplier =
  Rect.rectangularAdjointExact
    Rows.selectedCombinedConstraintRowCarrier
    KKT.physicalStateCarrier
    (Combined.selectedBackgroundLinearizedConstraintMatrix background)
    state multiplier

selectedCombinedConstraintGramQuadraticExact :
  ∀ background multiplier →
  Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
    (selectedCombinedConstraintGramApply background multiplier)
    multiplier
  ≡ Rect.finiteNormSq KKT.physicalStateCarrier
      (selectedCombinedConstraintTransposeApply background multiplier)
selectedCombinedConstraintGramQuadraticExact background multiplier =
  trans
    (Rect.finiteDotSymmetric
      Rows.selectedCombinedConstraintRowCarrier
      (selectedCombinedConstraintGramApply background multiplier)
      multiplier)
    (trans
      (Rect.applyRectangularVectorCong
        Rows.selectedCombinedConstraintRowCarrier
        (λ left right →
          Rows.selectedCombinedConstraintRowDelta left right)
        {left = multiplier}
        {right = multiplier}
        (λ _ → Agda.Builtin.Equality.refl)
        (Combined.averageConstraintRow
          (DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier.pair
            DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact.coordinateX
            DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact.axis0)))
      (selectedCombinedConstraintAdjointExact background
        (selectedCombinedConstraintTransposeApply background multiplier)
        multiplier))

selectedCombinedConstraintGramQuadraticNonnegative :
  ∀ background multiplier →
  0ℚ ≤ Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
    (selectedCombinedConstraintGramApply background multiplier)
    multiplier
selectedCombinedConstraintGramQuadraticNonnegative background multiplier =
  Relation.Binary.PropositionalEquality.subst
    (λ value → 0ℚ ≤ value)
    (sym (selectedCombinedConstraintGramQuadraticExact background multiplier))
    (Rect.finiteNormSqNonnegative KKT.physicalStateCarrier
      (selectedCombinedConstraintTransposeApply background multiplier))

selectedCombinedConstraintFiniteKKTLevel : ProofLevel
selectedCombinedConstraintFiniteKKTLevel = machineChecked

selectedCombinedConstraintGramPositivityLevel : ProofLevel
selectedCombinedConstraintGramPositivityLevel = machineChecked
