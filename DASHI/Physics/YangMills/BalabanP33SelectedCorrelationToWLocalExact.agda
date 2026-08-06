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
--                  defect = linear + groupedRemainder,
--
-- and selected-background structure supplies separate signed bounds
--
--   linear           >= -linearBudget,
--   groupedRemainder >= -remainderBudget,
--
-- then
--
--   defect >= -(linearBudget + remainderBudget).
--
-- Exact cancellation of the linear term is retained as a useful sufficient
-- specialization, but is not asserted to be necessary.  The physical problem
-- is therefore split correctly into correlated first-order control (from
-- plaquette curvature/regularity/variational structure) and the grouped
-- sixteen-atom nonlinear remainder estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; -_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

negativeBudgetSumExact :
  ∀ linearBudget remainderBudget →
  - (linearBudget + remainderBudget)
  ≡ - linearBudget + - remainderBudget
negativeBudgetSumExact linearBudget remainderBudget =
  solve (linearBudget ∷ remainderBudget ∷ [])

correlatedControlTransfersLowerBound :
  ∀ defect linear remainder linearBudget remainderBudget →
  defect ≡ linear + remainder →
  - linearBudget ≤ linear →
  - remainderBudget ≤ remainder →
  - (linearBudget + remainderBudget) ≤ defect
correlatedControlTransfersLowerBound
    defect linear remainder linearBudget remainderBudget
    decomposition linearLower remainderLower =
  let
    summedLower :
      - linearBudget + - remainderBudget ≤ linear + remainder
    summedLower = ℚP.+-mono-≤ linearLower remainderLower

    combinedBudgetLower :
      - (linearBudget + remainderBudget) ≤ linear + remainder
    combinedBudgetLower =
      subst
        (λ lower → lower ≤ linear + remainder)
        (sym (negativeBudgetSumExact linearBudget remainderBudget))
        summedLower
  in
  subst
    (λ upper → - (linearBudget + remainderBudget) ≤ upper)
    (sym decomposition)
    combinedBudgetLower

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
    physicalLinearBudget : ℚ
    physicalRemainderBudget : ℚ
    physicalDecomposition :
      physicalDefect ≡ physicalLinearPart + physicalGroupedRemainder
    selectedLinearLower :
      - physicalLinearBudget ≤ physicalLinearPart
    groupedRemainderLower :
      - physicalRemainderBudget ≤ physicalGroupedRemainder

open PhysicalSelectedCorrelationInputs public

physicalInputsImplyWLocalScalar :
  (inputs : PhysicalSelectedCorrelationInputs) →
  - (physicalLinearBudget inputs + physicalRemainderBudget inputs)
  ≤ physicalDefect inputs
physicalInputsImplyWLocalScalar inputs =
  correlatedControlTransfersLowerBound
    (physicalDefect inputs)
    (physicalLinearPart inputs)
    (physicalGroupedRemainder inputs)
    (physicalLinearBudget inputs)
    (physicalRemainderBudget inputs)
    (physicalDecomposition inputs)
    (selectedLinearLower inputs)
    (groupedRemainderLower inputs)

-- This closes the signed-order transport only.  It does not fabricate either
-- the physical correlated first-order bound or the grouped quaternion atom
-- estimate.
