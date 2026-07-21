module DASHI.Physics.YangMills.BalabanCriticalMapDisplacementWindow where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Correct B6 displacement-at-zero transport.
--
-- This is deliberately separated from the strict contraction window.  To move
--   d(r₀) + rho(r₀) r₀ <= r₀
-- from a threshold radius to a smaller selected radius, mere monotonicity of d
-- is not enough.  The complete budget itself must be monotone, or an explicit
-- comparison witness must be supplied.  This module makes that requirement
-- proof relevant and avoids the invalid direction used by the earlier draft.
------------------------------------------------------------------------

record CriticalMapDisplacementWindow (Bound : Set) : Set₁ where
  field
    selected threshold : Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    displacementBudget : Bound → Bound

    selectedBelowThreshold : LessEqual selected threshold
    budgetMonotone : ∀ {left right} →
      LessEqual left right →
      LessEqual (displacementBudget left) (displacementBudget right)

    thresholdSelfMap : LessEqual (displacementBudget threshold) threshold

open CriticalMapDisplacementWindow public

selectedSelfMap :
  ∀ {Bound : Set} →
  (window : CriticalMapDisplacementWindow Bound) →
  LessEqual window
    (displacementBudget window (selected window))
    (selected window)
selectedSelfMap window =
  transitive window
    (budgetMonotone window (selectedBelowThreshold window))
    (transitive window
      (thresholdSelfMap window)
      (selectedBelowThreshold window))

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
