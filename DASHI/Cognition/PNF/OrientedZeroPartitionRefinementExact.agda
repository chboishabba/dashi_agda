module DASHI.Cognition.PNF.OrientedZeroPartitionRefinementExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.OrientedZeroCanonicalFutureExact as Canonical
import DASHI.Cognition.PNF.OrientedZeroFutureQuotientExact as Wave
import DASHI.Core.GenericFuturePartitionRefinementExact as Refinement

------------------------------------------------------------------------
-- GENERIC PARTITION REFINEMENT INSTANTIATED AT THE ZERO CROSSING
------------------------------------------------------------------------

step : Canonical.Action → Wave.Wave4 → Wave.Wave4
step Canonical.tick = Wave.waveStep

zeroPairRelatedAtDepthZero :
  Refinement.RefinesToDepth 0 Wave.scalar step
    Wave.negativeZero Wave.positiveZero
zeroPairRelatedAtDepthZero = refl

zeroPairSeparatedAtDepthOne :
  Refinement.RefinesToDepth 1 Wave.scalar step
    Wave.negativeZero Wave.positiveZero → ⊥
zeroPairSeparatedAtDepthOne refined =
  Wave.zeroOrientationChangesNextScalar (proj₂ refined Canonical.tick)

negativeOneSelfStableAtEveryDepth :
  (depth : Nat) →
  Refinement.RefinesToDepth depth Wave.scalar step
    Wave.negativeOne Wave.negativeOne
negativeOneSelfStableAtEveryDepth zero = refl
negativeOneSelfStableAtEveryDepth (suc depth) =
  refl , λ Canonical.tick → selfDepth depth (Wave.waveStep Wave.negativeOne)
  where
    selfDepth :
      (n : Nat) → (state : Wave.Wave4) →
      Refinement.RefinesToDepth n Wave.scalar step state state
    selfDepth zero state = refl
    selfDepth (suc n) state = refl , λ Canonical.tick → selfDepth n (Wave.waveStep state)

positiveOneSelfStableAtEveryDepth :
  (depth : Nat) →
  Refinement.RefinesToDepth depth Wave.scalar step
    Wave.positiveOne Wave.positiveOne
positiveOneSelfStableAtEveryDepth zero = refl
positiveOneSelfStableAtEveryDepth (suc depth) =
  refl , λ Canonical.tick → positiveOneSelfStableAtEveryDepth depth

------------------------------------------------------------------------
-- The scalar partition therefore has exactly one immediately unstable block:
-- the zero fibre.  Future refinement spends additional state only there.
------------------------------------------------------------------------
