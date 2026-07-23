module DASHI.Physics.Closure.NSPeriodicModeInverseNormScaling where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _*ℝ_; _≤ℝ_; _<ℝ_)
open import DASHI.Physics.Closure.NSIntegerFourierLattice using
  (FourierMode; NonZeroMode)
open import DASHI.Physics.Closure.NSWall1ExactEvaluationCarrier using
  (Vec3)
open import DASHI.Physics.Closure.NSPeriodicRealOrderedNormLaws using
  (realVecNormSquared)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact inverse-|k|² scaling.
--
-- The integer-to-real embedding and positivity of the squared norm of a
-- nonzero integer mode are kept in one coherent carrier record.  From the
-- ordinary ordered-field inverse laws this module derives both required facts
--
--   |k|^{-2} ≥ 0,
--   |k|^{-2}|k|² = 1.
--
-- No Fourier multiplier estimate is assumed here.
------------------------------------------------------------------------

record OrderedRealInverseAuthority : Set₁ where
  field
    reciprocal : ℝ → ℝ

    positiveImpliesNonnegative :
      ∀ {x} → 0ℝ <ℝ x → 0ℝ ≤ℝ x

    reciprocalPositive :
      ∀ {x} → 0ℝ <ℝ x → 0ℝ <ℝ reciprocal x

    reciprocalCancelPositive :
      ∀ {x} → 0ℝ <ℝ x →
      reciprocal x *ℝ x ≡ 1ℝ

open OrderedRealInverseAuthority public

record IntegerModeNormIdentification : Set₁ where
  field
    modeWaveVector : FourierMode → Vec3 ℝ
    modeNormSquared : FourierMode → ℝ

    modeNormSquaredMeaning : ∀ k →
      modeNormSquared k ≡ realVecNormSquared (modeWaveVector k)

    nonzeroModeNormPositive : ∀ k →
      NonZeroMode k →
      0ℝ <ℝ modeNormSquared k

open IntegerModeNormIdentification public

nonzeroModeHasPositiveNormSquared :
  (M : IntegerModeNormIdentification) →
  ∀ k → NonZeroMode k →
  0ℝ <ℝ modeNormSquared M k
nonzeroModeHasPositiveNormSquared = nonzeroModeNormPositive

inverseNormSquared :
  OrderedRealInverseAuthority →
  IntegerModeNormIdentification →
  FourierMode → ℝ
inverseNormSquared I M k = reciprocal I (modeNormSquared M k)

inverseNormSquaredNonnegative :
  (I : OrderedRealInverseAuthority) →
  (M : IntegerModeNormIdentification) →
  ∀ k → NonZeroMode k →
  0ℝ ≤ℝ inverseNormSquared I M k
inverseNormSquaredNonnegative I M k nonzero =
  positiveImpliesNonnegative I
    (reciprocalPositive I
      (nonzeroModeHasPositiveNormSquared M k nonzero))

inverseNormSquaredTimesNormSquared :
  (I : OrderedRealInverseAuthority) →
  (M : IntegerModeNormIdentification) →
  ∀ k → NonZeroMode k →
  inverseNormSquared I M k *ℝ modeNormSquared M k ≡ 1ℝ
inverseNormSquaredTimesNormSquared I M k nonzero =
  reciprocalCancelPositive I
    (nonzeroModeHasPositiveNormSquared M k nonzero)

record ExactModeInverseNormScaling
    (I : OrderedRealInverseAuthority)
    (M : IntegerModeNormIdentification)
    (k : FourierMode)
    (nonzero : NonZeroMode k) : Set where
  field
    inverse-is-nonnegative :
      0ℝ ≤ℝ inverseNormSquared I M k

    inverse-times-norm-is-one :
      inverseNormSquared I M k *ℝ modeNormSquared M k ≡ 1ℝ

open ExactModeInverseNormScaling public

exactModeInverseNormScaling :
  (I : OrderedRealInverseAuthority) →
  (M : IntegerModeNormIdentification) →
  ∀ k → (nonzero : NonZeroMode k) →
  ExactModeInverseNormScaling I M k nonzero
exactModeInverseNormScaling I M k nonzero = record
  { inverse-is-nonnegative =
      inverseNormSquaredNonnegative I M k nonzero
  ; inverse-times-norm-is-one =
      inverseNormSquaredTimesNormSquared I M k nonzero
  }

------------------------------------------------------------------------
-- Status: inverse scaling itself is closed.  The remaining literal carrier
-- obligation is the standard integer-embedding theorem that a nonzero
-- k ∈ Z³ has strictly positive embedded squared norm.
------------------------------------------------------------------------

modeInverseNormScalingLevel : ProofLevel
modeInverseNormScalingLevel = machineChecked
