module DASHI.Physics.Closure.NSTriadKNSmallCriticalDataBarrierRound180Exact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.Closure.NSTriadKNSmallCriticalDataCompanionRound179Exact

------------------------------------------------------------------------
-- Round180: exact consequence compiler for the small-critical-data branch.
--
-- The point of this module is architectural: once the companion budget and the
-- weighted-Young absorption are supplied on the same scalar carrier, the
-- critical barrier follows with no further Navier--Stokes-specific discovery
-- step.  Arbitrary-data Package A is still not claimed.
------------------------------------------------------------------------

record SmallCriticalBarrierCompiler : Set₁ where
  field
    Scalar : Set
    _≤_ : Scalar → Scalar → Set
    _<_ : Scalar → Scalar → Set
    _+_ _*_ _/_ : Scalar → Scalar → Scalar
    zero : Scalar

    CritEnergy CritDiss Companion : Scalar → Scalar
    nu smallThreshold : Scalar

    -- Pointwise production payment after weighted Young.
    absorbed-production :
      ∀ t → _≤_ (Companion t)
                 ((nu * CritDiss t) + CritEnergy t)

    -- The trajectory companion is cutoff-uniform below threshold.
    companion-budget :
      ∀ t₀ t₁ → _<_ (CritEnergy t₀) smallThreshold →
      _≤_ (Companion t₁) (CritEnergy t₀ / nu)

    -- The exact finite-dimensional energy identity/inequality owner.
    critical-energy-balance :
      ∀ t₀ t₁ →
      _≤_ (CritEnergy t₁ + (nu * CritDiss t₁))
          (CritEnergy t₀ + Companion t₁)

open SmallCriticalBarrierCompiler public

record SmallCriticalBarrierWitness
       (C : SmallCriticalBarrierCompiler) : Set where
  open SmallCriticalBarrierCompiler C
  field
    t₀ t₁ : Scalar
    small : _<_ (CritEnergy t₀) smallThreshold
    barrier :
      _≤_ (CritEnergy t₁ + (nu * CritDiss t₁))
          (CritEnergy t₀ + (CritEnergy t₀ / nu))

-- The witness is kept explicit rather than postulated as a global theorem.
-- This prevents the small-data result from being mistaken for arbitrary-data
-- Package-A closure.
