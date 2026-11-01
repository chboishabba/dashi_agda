module DASHI.Physics.Closure.NSTriadKNZeroSafeCollinearityDefectInterface2026Exact where

------------------------------------------------------------------------
-- 2026 ZERO-SAFE COLLINEARITY DEFECT INTERFACE
--
-- Source calibration:
--   RequestProject/NavierStokes/AlmostOrthogonalGramSchur.lean,
--   theorem family herm_re_eq_sub_defect / resForm_eq_cs_sub_defect
--   (Lean sibling module supplied in the 2026-09-06 handoff archive;
--   no stable repository commit identifier was present in this archive).
--
-- The Lean identity is stated on nonzero cells because its displayed defect
-- divides by ||x|| ||y||.  The Agda cross-pollination requested a zero-safe API
-- so later physical producers do not need support surgery merely to state the
-- defect ledger.
--
-- This file does NOT re-prove the Hilbert-space identity.  It defines the
-- exact zero-safe contract a concrete analytic carrier must inhabit and proves
-- that zero rows/columns contribute zero defect by construction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _-_)

------------------------------------------------------------------------
-- Activity is explicit, avoiding division on zero cells.
------------------------------------------------------------------------

data CellActivity : Set where
  zeroCell : CellActivity
  activeCell : CellActivity

zeroSafeDefect :
  ∀ {Index : Set} →
  (activity : Index → CellActivity) →
  (activeDefect : Index → Index → ℚ) →
  Index → Index → ℚ
zeroSafeDefect activity activeDefect i j with activity i | activity j
... | zeroCell | _ = 0ℚ
... | activeCell | zeroCell = 0ℚ
... | activeCell | activeCell = activeDefect i j

zeroSafeDefectZeroLeft :
  ∀ {Index : Set}
    (activity : Index → CellActivity)
    (activeDefect : Index → Index → ℚ)
    (i j : Index) →
  activity i ≡ zeroCell →
  zeroSafeDefect activity activeDefect i j ≡ 0ℚ
zeroSafeDefectZeroLeft activity activeDefect i j refl = refl

zeroSafeDefectZeroRight :
  ∀ {Index : Set}
    (activity : Index → CellActivity)
    (activeDefect : Index → Index → ℚ)
    (i j : Index) →
  activity i ≡ activeCell →
  activity j ≡ zeroCell →
  zeroSafeDefect activity activeDefect i j ≡ 0ℚ
zeroSafeDefectZeroRight activity activeDefect i j refl refl = refl

zeroSafeDefectActivePair :
  ∀ {Index : Set}
    (activity : Index → CellActivity)
    (activeDefect : Index → Index → ℚ)
    (i j : Index) →
  activity i ≡ activeCell →
  activity j ≡ activeCell →
  zeroSafeDefect activity activeDefect i j ≡ activeDefect i j
zeroSafeDefectActivePair activity activeDefect i j refl refl = refl

------------------------------------------------------------------------
-- Analytic identity contract.  `csMajorant`, `realGram`, and `activeDefect`
-- come from the concrete Hilbert carrier.  Only active-active pairs are asked
-- to satisfy the division-bearing identity; the zero-safe extension is total.
------------------------------------------------------------------------

record ActiveCollinearityDefectIdentity
    {Index : Set}
    (activity : Index → CellActivity)
    (realGram csMajorant activeDefect : Index → Index → ℚ) : Set where
  field
    activeIdentity : ∀ i j →
      activity i ≡ activeCell →
      activity j ≡ activeCell →
      realGram i j ≡ csMajorant i j - activeDefect i j

open ActiveCollinearityDefectIdentity public

zeroSafeDefectAPIClosed : Bool
zeroSafeDefectAPIClosed = true

zeroSafeHilbertDefectIdentityReprovedInAgda : Bool
zeroSafeHilbertDefectIdentityReprovedInAgda = false

zeroSafeDefectAPIClosedIsTrue : zeroSafeDefectAPIClosed ≡ true
zeroSafeDefectAPIClosedIsTrue = refl

zeroSafeHilbertDefectIdentityReprovedInAgdaIsFalse :
  zeroSafeHilbertDefectIdentityReprovedInAgda ≡ false
zeroSafeHilbertDefectIdentityReprovedInAgdaIsFalse = refl
