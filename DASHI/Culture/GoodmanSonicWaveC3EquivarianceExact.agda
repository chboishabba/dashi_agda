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

------------------------------------------------------------------------
-- T16: HETEROGENEOUS OPERATORS MUST TRANSFORM WITH THE CHANNELS.
-- A triple of independent wave operators is not invariant under a
-- channel permutation. Equivariance instead has a naturality square:
-- evolve(rotated operators, rotated field) = rotate(evolve(operators,field)).
-- This statement holds for arbitrary operators; no acoustic assumptions.
------------------------------------------------------------------------

record TripleOperator : Set₁ where
  constructor tripleOperator
  field
    firstOperator secondOperator thirdOperator :
      Wave.DiscreteWave → Wave.DiscreteWave
open TripleOperator public

rotateOperators : TripleOperator → TripleOperator
rotateOperators (tripleOperator a b c) = tripleOperator b c a

evolveWith : TripleOperator → TripleWave → TripleWave
evolveWith (tripleOperator f g h) (tripleWave a b c) =
  tripleWave (f a) (g b) (h c)

heterogeneousCovariance :
  (operators : TripleOperator) →
  (field : TripleWave) →
  evolveWith (rotateOperators operators) (rotate3 field)
    ≡ rotate3 (evolveWith operators field)
heterogeneousCovariance (tripleOperator f g h) (tripleWave a b c) = refl

rotateOperatorsThreeTimes :
  (operators : TripleOperator) →
  rotateOperators (rotateOperators (rotateOperators operators))
    ≡ operators
rotateOperatorsThreeTimes (tripleOperator f g h) = refl

-- A fixed heterogeneous operator triple is generally NOT equivariant.
-- Concrete noncommutation: first channel zeroes its input, while second
-- and third leave it unchanged. This is an algebraic witness only.
zeroOperator : Wave.DiscreteWave → Wave.DiscreteWave
zeroOperator w = Wave.mkDiscreteWave (+ 0) (+ 0)

identityOperator : Wave.DiscreteWave → Wave.DiscreteWave
identityOperator w = w

asymmetricOperators : TripleOperator
asymmetricOperators =
  tripleOperator zeroOperator identityOperator identityOperator

unitWave : Wave.DiscreteWave
unitWave = Wave.mkDiscreteWave (+ 1) (+ 0)

asymmetricField : TripleWave
asymmetricField = tripleWave unitWave unitWave unitWave

fixedAsymmetricTransportDoesNotCommute :
  evolveWith asymmetricOperators (rotate3 asymmetricField)
  ≡ rotate3 (evolveWith asymmetricOperators asymmetricField) → ⊥
fixedAsymmetricTransportDoesNotCommute ()

-- To claim an actual physical channel symmetry requires observed or
-- specified coefficients plus an action on the medium and sensor geometry.
-- Neither this naturality square nor a 3/6/9 count supplies that receipt.
