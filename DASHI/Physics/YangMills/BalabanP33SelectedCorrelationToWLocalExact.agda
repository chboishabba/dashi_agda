module DASHI.Physics.YangMills.BalabanP33SelectedCorrelationToWLocalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Balaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories".
-- DOI: 10.1007/BF01229381.
--
-- DASHI CONTRIBUTION
--
-- Isolate the exact replacement for the false radius-only implication.  If a
-- plaquette defect decomposes as
--
--                  defect = linear + remainder,
--
-- selected-background structure proves linear=0, and the grouped sixteen-atom
-- remainder satisfies remainder >= -budget, then the desired W-local lower
-- bound follows.  This transport is proved over exact rationals.  The actual
-- hard producers are now sharply separated:
--
--   (1) physical correlated first-order cancellation;
--   (2) physical grouped remainder estimate with rho/36 and rho/144.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; -_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

closedDefectEqualsRemainder :
  ∀ defect linear remainder →
  defect ≡ linear + remainder →
  linear ≡ 0ℚ →
  defect ≡ remainder
closedDefectEqualsRemainder defect linear remainder decomposition closure =
  trans
    decomposition
    (trans
      (cong (λ selected → selected + remainder) closure)
      (solve (remainder ∷ [])))

correlatedCancellationTransfersLowerBound :
  ∀ defect linear remainder budget →
  defect ≡ linear + remainder →
  linear ≡ 0ℚ →
  - budget ≤ remainder →
  - budget ≤ defect
correlatedCancellationTransfersLowerBound
    defect linear remainder budget decomposition closure remainderLower =
  subst
    (λ selected → - budget ≤ selected)
    (sym (closedDefectEqualsRemainder
      defect linear remainder decomposition closure))
    remainderLower

record PhysicalSelectedCorrelationInputs : Set where
  constructor physicalSelectedCorrelationInputs
  field
    physicalDefect : ℚ
    physicalLinearPart : ℚ
    physicalGroupedRemainder : ℚ
    physicalBudget : ℚ
    physicalDecomposition :
      physicalDefect ≡ physicalLinearPart + physicalGroupedRemainder
    selectedLinearCancellation : physicalLinearPart ≡ 0ℚ
    groupedRemainderLower :
      - physicalBudget ≤ physicalGroupedRemainder

open PhysicalSelectedCorrelationInputs public

physicalInputsImplyWLocalScalar :
  (inputs : PhysicalSelectedCorrelationInputs) →
  - physicalBudget inputs ≤ physicalDefect inputs
physicalInputsImplyWLocalScalar inputs =
  correlatedCancellationTransfersLowerBound
    (physicalDefect inputs)
    (physicalLinearPart inputs)
    (physicalGroupedRemainder inputs)
    (physicalBudget inputs)
    (physicalDecomposition inputs)
    (selectedLinearCancellation inputs)
    (groupedRemainderLower inputs)

-- This closes the logical and signed-order transport only.  It does not
-- fabricate the selected-background cancellation or grouped quaternion atom
-- estimate.
