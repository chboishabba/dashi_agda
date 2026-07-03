module DASHI.Core.ProjectionFibre where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ProjectionCategory as PC

----------------------------------------------------------------------
-- ProjectionFibre: the fibre structure over a projection.
--
-- For a projection π : Carrier → Observable in a projection
-- category, the fibre over an observable o is:
--
--   Fibre(π, o) = { c : Carrier | π(c) ≡ o }
--
-- This requires an underlying-set functor
--   Underlying : Obj → Set
-- so that we can talk about elements of abstract objects.
--
-- The fibre records which hidden/extended carrier states collapse
-- to the same observable surface.  Two carriers c₁, c₂ in the same
-- fibre are "observationally equivalent (under π)" but DASHI refuses
-- to identify them without additional authority/residual closure.
----------------------------------------------------------------------

record ProjectionFibre (𝓒 : PC.ProjectionCategory) : Set₁ where
  open PC.ProjectionCategory 𝓒

  field
    -- Underlying-set functor: gives the points of each object
    Underlying : Obj → Set

    -- The projection map
    Carrier    : Obj
    Observable : Obj
    π          : Hom Carrier Observable

    -- Evaluation of a morphism on underlying points
    apply : ∀ {A B} → Hom A B → Underlying A → Underlying B

    -- Guards
    fibreReading : String

  -- Derived: the fibre over a specific observable point
  Fibre : Underlying Observable → Set
  Fibre o = Σ (Underlying Carrier) λ c → apply π c ≡ o

open ProjectionFibre public

----------------------------------------------------------------------
-- Canonical instance
----------------------------------------------------------------------

canonicalProjectionFibre : ProjectionFibre PC.canonicalProjectionCategory
canonicalProjectionFibre = record
  { Underlying   = λ _ → ⊤
  ; Carrier      = tt
  ; Observable   = tt
  ; π            = tt
  ; apply        = λ _ _ → tt
  ; fibreReading = "Canonical ProjectionFibre: trivial."
  }
