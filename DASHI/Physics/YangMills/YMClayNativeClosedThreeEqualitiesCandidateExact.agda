module DASHI.Physics.YangMills.YMClayNativeClosedThreeEqualitiesCandidateExact where

------------------------------------------------------------------------
-- R443 / R445: ACTUAL closed original-label finite proof attempts.
--
-- IMPORTANT: these are Agda check targets, NOT a green compiler receipt.
-- NO postulates, metas, trustMe, primTrustMe, or unproved Set fields.
-- The equality reflection is executable against the true original
-- 1024-link canonically enumerated bond vector and original 64-pair
-- 128+896 partition. If an equality does not compute in Agda, the
-- canonical root and targeted CI MUST FAIL (do not weaken the target).
--
-- The existing generic structural sorter and decider are reused;
-- no alternate label convention or arbitrary matrix-link state.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClayNativeC3AdjacentSortProgramExact as C3Sort
import DASHI.Physics.YangMills.YMClayNativeOriginalSortDeciderExact as Decide
import DASHI.Physics.YangMills.YMClayNativeSideFourPairSpectatorSortProgramExact as PairSort

-- Original 1024-label C3 selection trace, computed from *actual*
-- C3.forwardVector and original canonical labels.
-- This is a deliberately strict kernel attempt, not a premise.
originalC3SelectabilityClosed :
  Decide.originalC3SelectableBooleanGoal
originalC3SelectabilityClosed = refl

-- Original canonical-label permutation equality (R443.F07), not a
-- separate synthetic 1024-label problem.
originalC3CanonicalLabelsClosed :
  C3Sort.constructedNativeC3CanonicalLabelGoal
originalC3CanonicalLabelsClosed =
  Decide.originalC3CanonicalFromBoolean originalC3SelectabilityClosed

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  where

  -- Original R445 64 coarse pairs = 128 selected and 896 spectator
  -- labels. No abstract length witness supplied by the caller.
  originalPairSpectatorLengthClosed :
    PairSort.originalPairSpectatorLengthGoal theory
  originalPairSpectatorLengthClosed = refl

  -- Exact original pair/spectator target in actual 1024-link bond
  -- codec, not a generic arbitrary target.
  originalPairSpectatorSelectabilityClosed :
    Decide.originalPairSelectableBooleanGoal
      theory (originalPairSpectatorLengthClosed)
  originalPairSpectatorSelectabilityClosed = refl

  originalPairSpectatorCanonicalLabelsClosed :
    PairSort.originalPairSpectatorCanonicalLabelGoal
      theory (originalPairSpectatorLengthClosed)
  originalPairSpectatorCanonicalLabelsClosed =
    Decide.originalPairCanonicalFromBoolean
      theory originalPairSpectatorLengthClosed
      originalPairSpectatorSelectabilityClosed

-- Acceptance requires exact pinned Agda and transitive imports;
-- not just text/shape checking or Python agreement.
