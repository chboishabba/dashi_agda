module DASHI.Physics.Closure.ShiftContractParametricTriadicFamily where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.ShiftContractAnchoredTriadicFamily as SATF
  using
    ( ShiftContractAnchoredTriadicFamily
    ; canonicalShiftContractAnchoredTriadicFamily
    )
open import DASHI.Physics.Closure.ShiftContractDenseTriadicFamily as SDTF
  using
    ( ShiftContractDenseTriadicFamily
    ; canonicalShiftContractDenseTriadicFamily
    )
open import DASHI.Physics.Closure.ShiftContractTriadicFamily as STF
  using
    ( ShiftContractTriadicFamily
    ; canonicalShiftContractTriadicFamily
    )

------------------------------------------------------------------------
-- Parametric surface packaging the positive explicit cyclic branch.
--
-- The noncanonical seam now has theorem-bearing triadic families at support
-- widths 1, 2, and 3.  This module normalizes those into one small parameter
-- surface so later proofs can quantify over the explicit cyclic branch
-- without choosing one width ad hoc.

data SupportWidth : Set where
  width1 width2 width3 : SupportWidth

record ParametricShiftContractTriadicFamily : Set₂ where
  field
    width : SupportWidth
    family : Set₁

triadicFamilyAt : SupportWidth → Set₁
triadicFamilyAt width1 = ShiftContractTriadicFamily
triadicFamilyAt width2 = ShiftContractAnchoredTriadicFamily
triadicFamilyAt width3 = ShiftContractDenseTriadicFamily

canonicalTriadicFamilyAt : (w : SupportWidth) → triadicFamilyAt w
canonicalTriadicFamilyAt width1 = canonicalShiftContractTriadicFamily
canonicalTriadicFamilyAt width2 = canonicalShiftContractAnchoredTriadicFamily
canonicalTriadicFamilyAt width3 = canonicalShiftContractDenseTriadicFamily

canonicalParametricShiftContractTriadicFamily :
  (w : SupportWidth) → ParametricShiftContractTriadicFamily
canonicalParametricShiftContractTriadicFamily w =
  record
    { width = w
    ; family = triadicFamilyAt w
    }
