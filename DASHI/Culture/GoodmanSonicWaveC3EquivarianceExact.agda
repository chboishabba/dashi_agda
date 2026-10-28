module DASHI.Culture.GoodmanSonicWaveC3EquivarianceExact where

------------------------------------------------------------------------
-- T15: genuine, bounded C3 covariance of a THREE-CHANNEL wave field.
--
-- Prior finite wave owner: DASHI.Physics.ShiftDiscreteWaveStep.
-- Prior additive wave transport:
--   DASHI.Reasoning.PNFWaveSynthesisCommutatorExact.
-- PR #1414 owns an independent S3/C3 root-permutation and rational
-- quaternion representation. We do NOT identify its root-label action
-- with this channel relabelling, nor import an unmerged branch.
-- The three channels use the SAME fixed wave-step parameter.
-- No claim of physical three-channel symmetry with unequal couplings.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Physics.ShiftDiscreteWaveStep as Wave
import DASHI.Physics.SchrodingerGapPhaseWaveShiftInstance as Shift

record TripleWave : Set where
  constructor tripleWave
  field
    firstWave secondWave thirdWave : Wave.DiscreteWave
open TripleWave public

-- Explicit cyclic relabelling: 0->1->2->0.
rotate3 : TripleWave → TripleWave
rotate3 (tripleWave a b c) = tripleWave b c a

rotate3ThreeTimes :
  (field : TripleWave) → rotate3 (rotate3 (rotate3 field)) ≡ field
rotate3ThreeTimes (tripleWave a b c) = refl

-- A fixed state-indexed update acts independently on each channel.
transport3 :
  Shift.ShiftWavePhaseState → TripleWave → TripleWave
transport3 state (tripleWave a b c) =
  tripleWave
    (Wave.shiftSchrodingerStep4 state a)
    (Wave.shiftSchrodingerStep4 state b)
    (Wave.shiftSchrodingerStep4 state c)

-- The square commutes by definitional reduction, because all three
-- channels use exactly the same transport law and state parameter.
transport3CommutesWithRotate3 :
  (state : Shift.ShiftWavePhaseState) →
  (field : TripleWave) →
  transport3 state (rotate3 field)
    ≡ rotate3 (transport3 state field)
transport3CommutesWithRotate3 state (tripleWave a b c) = refl

-- Homogeneous channel permutation is thus a C3 action, not a
-- representation of the quaternion root monodromy on wave phases.
-- A heterogeneous medium/source/gain demands separately justified
-- action on those coefficients, and this theorem does not cover it.
