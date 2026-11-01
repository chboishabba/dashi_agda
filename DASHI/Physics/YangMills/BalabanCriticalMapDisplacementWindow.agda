module DASHI.Physics.YangMills.BalabanCriticalMapDisplacementWindow where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Correct B6 displacement-at-zero transport.
--
-- A self-map inequality at one threshold radius does not in general descend to
-- every smaller radius.  The valid producer is a scale-relative estimate:
--
--   displacementBudget(r) <= sigma * r,
--
-- on the whole selected window, together with sigma * r <= r at the chosen
-- radius.  This is exactly the quantitative input needed by the critical-ball
-- theorem and avoids the invalid monotonicity argument of the earlier draft.
------------------------------------------------------------------------

record CriticalMapDisplacementWindow (Bound : Set) : Set₁ where
  field
    selected threshold sigma : Bound
    scale : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    displacementBudget : Bound → Bound

    selectedBelowThreshold : LessEqual selected threshold

    budgetBelowScaledRadius : ∀ radius →
      LessEqual radius threshold →
      LessEqual (displacementBudget radius) (scale sigma radius)

    scaledSelectedBelowSelected :
      LessEqual (scale sigma selected) selected

open CriticalMapDisplacementWindow public

selectedSelfMap :
  ∀ {Bound : Set} →
  (window : CriticalMapDisplacementWindow Bound) →
  LessEqual window
    (displacementBudget window (selected window))
    (selected window)
selectedSelfMap window =
  transitive window
    (budgetBelowScaledRadius window
      (selected window)
      (selectedBelowThreshold window))
    (scaledSelectedBelowSelected window)

record DisplacementWindowCertificate {Bound : Set}
    (window : CriticalMapDisplacementWindow Bound) : Set₁ where
  field
    selfMapBudget :
      LessEqual window
        (displacementBudget window (selected window))
        (selected window)

assembleDisplacementWindowCertificate :
  ∀ {Bound : Set} →
  (window : CriticalMapDisplacementWindow Bound) →
  DisplacementWindowCertificate window
assembleDisplacementWindowCertificate window = record
  { selfMapBudget = selectedSelfMap window }

criticalMapDisplacementWindowAssemblyLevel : ProofLevel
criticalMapDisplacementWindowAssemblyLevel = machineChecked

criticalMapDisplacementThresholdInputsLevel : ProofLevel
criticalMapDisplacementThresholdInputsLevel = conditional
