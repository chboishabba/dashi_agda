module DASHI.Physics.Closure.NSFilamentFiningCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

open import Base369 using
  ( TriTruth
  ; tri-low
  ; tri-mid
  ; tri-high
  )

------------------------------------------------------------------------
-- Signed-support filament fining.
--
-- The sibling dashiCFD implementation carries a ternary sign field,
-- coherence acceptance, a persistent per-cell lifetime, and irreversible
-- annihilation.  This module records the finite algebraic kernel only.
-- It does not assert that a runtime coherence proxy is physically complete,
-- that codec error controls Navier-Stokes error, or that filament persistence
-- proves regularity.

infixr 6 _∧ᵇ_

_∧ᵇ_ : Bool → Bool → Bool
true  ∧ᵇ b = b
false ∧ᵇ _ = false

signedSupport : TriTruth → Bool
signedSupport tri-low  = false
signedSupport tri-mid  = true
signedSupport tri-high = true

record FilamentCell : Set where
  constructor filamentCell
  field
    sign : TriTruth
    lifetime : Nat

open FilamentCell public

annihilatedCell : FilamentCell
annihilatedCell = filamentCell tri-low zero

survives : TriTruth → Bool → Bool
survives s coherenceAccepted = signedSupport s ∧ᵇ coherenceAccepted

fineCell : Bool → FilamentCell → FilamentCell
fineCell coherenceAccepted (filamentCell s n) with survives s coherenceAccepted
... | true  = filamentCell s (suc n)
... | false = annihilatedCell

------------------------------------------------------------------------
-- Lifetime shaping.
--
-- The concrete runtime currently allows a protected, long-lived cell to use
-- a relaxed coherence decision.  The numerical factor belongs to the runtime
-- policy, not this finite core.  The core records the only invariant needed
-- here: policy may alter acceptance of existing support but may not resurrect
-- annihilated support.

shapedAcceptance : Bool → Bool → Bool → Bool
shapedAcceptance protected strictAccepted relaxedAccepted with protected
... | true  = relaxedAccepted
... | false = strictAccepted

fineCellShaped : Bool → Bool → Bool → FilamentCell → FilamentCell
fineCellShaped protected strictAccepted relaxedAccepted =
  fineCell (shapedAcceptance protected strictAccepted relaxedAccepted)

------------------------------------------------------------------------
-- Exact finite laws.

failed-coherence-annihilates :
  ∀ s n →
  fineCell false (filamentCell s n) ≡ annihilatedCell
failed-coherence-annihilates tri-low  n = refl
failed-coherence-annihilates tri-mid  n = refl
failed-coherence-annihilates tri-high n = refl

positive-support-survives :
  ∀ n →
  fineCell true (filamentCell tri-mid n) ≡
  filamentCell tri-mid (suc n)
positive-support-survives n = refl

negative-support-survives :
  ∀ n →
  fineCell true (filamentCell tri-high n) ≡
  filamentCell tri-high (suc n)
negative-support-survives n = refl

annihilated-support-is-absorbing :
  ∀ accepted n →
  fineCell accepted (filamentCell tri-low n) ≡ annihilatedCell
annihilated-support-is-absorbing false n = refl
annihilated-support-is-absorbing true  n = refl

shaping-cannot-resurrect :
  ∀ protected strictAccepted relaxedAccepted n →
  fineCellShaped protected strictAccepted relaxedAccepted
    (filamentCell tri-low n)
  ≡ annihilatedCell
shaping-cannot-resurrect false false false n = refl
shaping-cannot-resurrect false false true  n = refl
shaping-cannot-resurrect false true  false n = refl
shaping-cannot-resurrect false true  true  n = refl
shaping-cannot-resurrect true  false false n = refl
shaping-cannot-resurrect true  false true  n = refl
shaping-cannot-resurrect true  true  false n = refl
shaping-cannot-resurrect true  true  true  n = refl

------------------------------------------------------------------------
-- Tracking and metrics contracts.

-- Per-cell tracking is canonical for the fining action because the action
-- mutates signed support locally.  Per-block and per-mode lifetimes remain
-- legitimate derived summaries, but are not substitutes for the local state.
data LifetimeTracking : Set where
  perCell : LifetimeTracking
  perBlockSummary : LifetimeTracking
  perModeSummary : LifetimeTracking

canonicalLifetimeTracking : LifetimeTracking
canonicalLifetimeTracking = perCell

record FilamentMetrics : Set where
  constructor filamentMetrics
  field
    alive : Nat
    killed : Nat
    maxLifetime : Nat

open FilamentMetrics public

minimalFilamentMetrics : FilamentMetrics
minimalFilamentMetrics = filamentMetrics zero zero zero

filamentFiningStatement : String
filamentFiningStatement =
  "Filament fining is the irreversible projection of signed support whose coherence fails to persist; surviving support increments a persistent local lifetime, while annihilated support is absorbing."

filamentFiningBoundary : String
filamentFiningBoundary =
  "This finite kernel proves only the ternary support/lifetime transition laws.  It does not prove that a chosen coherence proxy identifies physical filaments, that lifetime improves reconstruction, that a GPU implementation is correct without a parity receipt, or that any Navier-Stokes or Clay theorem follows."
