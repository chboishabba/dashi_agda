module DASHI.Physics.YangMills.BalabanSelectedConstraintGramReducedCoercivityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- DASHI CONTRIBUTION
--
-- Close the reduced-coercivity seam in the multiplier-Gram Combes--Thomas
-- lane on the SAME selected combined constraint matrix.
--
-- The selected-background theorem already proves on the reduced multiplier
-- presentation
--
--   (29/1024) ||lambda||^2 <= ||L_A^* lambda||^2.
--
-- The literal finite KKT theorem independently proves
--
--   <K_A lambda,lambda> = ||L_A^* lambda||^2,
--   K_A = L_A L_A^*.
--
-- Reopening the reduced multiplier into the raw 780-row carrier and composing
-- those two exact statements yields
--
--   (29/1024) ||lambda||^2 <= <K_A lambda,lambda>.
--
-- Thus reduced multiplier coercivity is no longer a physical producer for the
-- selected KKT locality theorem.  What remains for Combes--Thomas is the
-- literal finite-range/tilt estimate and a tilted-inverse entry/row bound.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as StateCarrier
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Radius
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintFiniteKKTExact as KKT
import DASHI.Physics.YangMills.BalabanSelectedCombinedMultiplierSplitExact as Split
import DASHI.Physics.YangMills.BalabanSelectedReducedCombinedConstraintFloorExact as Floor

selectedGramReducedFloor : ℚ
selectedGramReducedFloor = Floor.selectedBackgroundReducedCombinedFloor

selectedReducedConstraintGramCoercive :
  ∀ background → Radius.RelaxedInverseLinkRadius background →
  ∀ selected →
  selectedGramReducedFloor
      * Floor.reducedCombinedMultiplierNormSq selected
  ≤ Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
      (KKT.selectedCombinedConstraintGramApply background
        (Split.reopenReducedMultiplier selected))
      (Split.reopenReducedMultiplier selected)
selectedReducedConstraintGramCoercive background radius selected =
  let
    raw = Split.reopenReducedMultiplier selected

    adjointFloor :
      selectedGramReducedFloor
        * Floor.reducedCombinedMultiplierNormSq selected
      ≤ Rect.finiteNormSq StateCarrier.physicalStateCarrier
          (KKT.selectedCombinedConstraintTransposeApply background raw)
    adjointFloor =
      Floor.selectedBackgroundReducedCombinedAdjointFloor
        background radius selected

    gramQuadratic :
      Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
        (KKT.selectedCombinedConstraintGramApply background raw) raw
      ≡ Rect.finiteNormSq StateCarrier.physicalStateCarrier
          (KKT.selectedCombinedConstraintTransposeApply background raw)
    gramQuadratic = KKT.selectedCombinedConstraintGramQuadraticExact background raw
  in
  subst
    (λ upper →
      selectedGramReducedFloor
        * Floor.reducedCombinedMultiplierNormSq selected ≤ upper)
    (sym gramQuadratic)
    adjointFloor

selectedConstraintGramReducedCoercivityLevel : ProofLevel
selectedConstraintGramReducedCoercivityLevel = machineChecked

-- The old generic CT boundary called the reduced floor a producer.  On the
-- selected physical carrier it is now an exact theorem; only the remaining
-- finite-range/tilt/inverse estimates stay open.
selectedConstraintGramReducedFloorProducerLevel : ProofLevel
selectedConstraintGramReducedFloorProducerLevel = machineChecked
