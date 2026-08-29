module DASHI.Physics.Closure.NSTriadKNSmallCriticalDataCompanionRound179Exact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

------------------------------------------------------------------------
-- Round179: formal interface for the small-critical-data companion budget.
--
-- The Lean owner now closes the companion-budget weld below the explicit
-- critical threshold.  This Agda module records the exact dependency shape
-- without promoting arbitrary-data Package A.
------------------------------------------------------------------------

record SmallCriticalDataCompanionInterface : Set₁ where
  field
    Scalar : Set
    _≤_ : Scalar → Scalar → Set
    _<_ : Scalar → Scalar → Set
    _+_ _*_ _/_ : Scalar → Scalar → Scalar
    sq : Scalar → Scalar

    CritEnergy CritDiss Enstrophy : Scalar → Scalar
    nu threshold : Scalar

    -- The explicit small-data threshold owner.
    smallThreshold : Scalar
    threshold-shape : smallThreshold ≡ sq (nu / threshold)

    -- Existing critical interpolation owner.
    enstrophy-critical-interpolation :
      ∀ t → _≤_ (sq (Enstrophy t)) (CritEnergy t * CritDiss t)

    -- Small-data barrier propagated along the interval.
    critical-threshold-propagation :
      ∀ t₀ t → _<_ (CritEnergy t₀) smallThreshold →
      _≤_ (CritEnergy t) smallThreshold

    -- Integrated critical dissipation budget produced by the barrier.
    integrated-critical-dissipation :
      ∀ t₀ t₁ → _<_ (CritEnergy t₀) smallThreshold →
      _≤_ (CritDiss t₁) (CritEnergy t₀ / nu)

    -- Companion budget below threshold.  This is the same payment shape
    -- needed by the conditional critical barrier, but only on the small-data
    -- branch.  It is intentionally not an arbitrary-data theorem.
    small-data-companion-budget :
      ∀ t₀ t₁ → _<_ (CritEnergy t₀) smallThreshold →
      _≤_ (sq (Enstrophy t₁))
          (smallThreshold * (CritEnergy t₀ / nu))

open SmallCriticalDataCompanionInterface public

-- Package-A status remains deliberately fail-closed: Round179 only records
-- that the time-integrated companion weld is discharged below the explicit
-- small-critical-data threshold.  Arbitrary-data signed trajectory payment is
-- still the frontier.
data PackageAStatus : Set where
  arbitraryDataOpen : PackageAStatus

round179-packageA-status : PackageAStatus
round179-packageA-status = arbitraryDataOpen
