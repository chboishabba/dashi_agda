module DASHI.Arithmetic.CanonicalResidueZero where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Data.Product using (_×_; _,_)

open import DASHI.Arithmetic.NormalizeAddState
  using
    ( NormalizeAddState
    ; carryBudget
    ; normalizeAddCanonical
    )
open import DASHI.Arithmetic.NormalizeAdd
  using
    ( normalizeAdd
    ; normalizeAdd-canonical
    )

-- Lightest honest proxy for the current state model: the residue-budget
-- proxy is the carry budget field itself.
StateResidueBudget : NormalizeAddState → Set
StateResidueBudget s = carryBudget s ≡ zero

-- Direct extraction from any canonical tuple.
canonicalResidueBudget-fromCanonical :
  ∀ s →
  normalizeAddCanonical s →
  StateResidueBudget s
canonicalResidueBudget-fromCanonical _ (_ , (_ , (budget-zero , _))) = budget-zero

normalizeAdd-residueBudget-zero :
  ∀ s →
  StateResidueBudget (normalizeAdd s)
normalizeAdd-residueBudget-zero s =
  canonicalResidueBudget-fromCanonical (normalizeAdd s) (normalizeAdd-canonical s)

-- Surface theorem: normalizeAdd lands in the zero residue-budget proxy
-- after one step.
normalizeAdd-zeroResidueBudget :
  ∀ s →
  StateResidueBudget (normalizeAdd s)
normalizeAdd-zeroResidueBudget = normalizeAdd-residueBudget-zero

record CanonicalResidueZeroSurface : Set₁ where
  field
    residueBudgetProxy : NormalizeAddState → Set
    canonicalZeroResidueBudget :
      ∀ s →
      normalizeAddCanonical s →
      residueBudgetProxy s
    landsInZeroResidueBudget :
      ∀ s →
      residueBudgetProxy (normalizeAdd s)

canonicalResidueZeroSurface : CanonicalResidueZeroSurface
canonicalResidueZeroSurface = record
  { residueBudgetProxy = StateResidueBudget
  ; canonicalZeroResidueBudget = canonicalResidueBudget-fromCanonical
  ; landsInZeroResidueBudget = normalizeAdd-zeroResidueBudget
  }
