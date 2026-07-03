module DASHI.Core.LoomEncoding where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.ProjectionFibre as PF

----------------------------------------------------------------------
-- LoomEncoding: an n-braid/weave representation of the fibre geometry
-- over a projection category.
--
-- A loom is not the projection category itself.  It is a structured
-- encoding of the fibres of a projection π : Carrier → Observable,
-- their transports under grammar change, residual obstructions, and
-- homological persistence.
--
--   Strand      = an element of a fibre (a hidden carrier point)
--   Weave       = a move/transformation on strands
--   ProjectionSurface = the observable co-domain (⊇ fibre target)
--   residual(α, β)  = obstruction when two weaves disagree
--
-- The loom is a "fibre ledger": it records which hidden strands
-- collapse to the same observable surface and which distinctions
-- survive transport and comparison.
----------------------------------------------------------------------

record LoomEncoding
  (𝓒 : PC.ProjectionCategory)
  (F : PF.ProjectionFibre 𝓒) : Set₁ where

  open PC.ProjectionCategory 𝓒
  open PF.ProjectionFibre F

  field
    -- A strand is a fibre element (a hidden carrier point)
    Strand : Set

    -- A weave move relates two strands
    Weave : Set
    weaveId  : Strand → Weave
    weaveSeq : Weave → Weave → Weave

    -- A projection surface is the observable co-domain
    ProjectionSurface : Set

    -- project maps a strand to its observable value
    project : Strand → ProjectionSurface

    -- Fibre-equivalence: two strands give the same observable
    fibreEquivalent : Strand → Strand → Set

    -- A residual records a mismatch between two weaves
    residual : Weave → Weave → Set
    closed   : Weave → Weave → Set

    -- Guards
    loomReading : String

open LoomEncoding public

----------------------------------------------------------------------
-- Canonical instance (trivial)
----------------------------------------------------------------------

canonicalLoomEncoding : LoomEncoding
  PC.canonicalProjectionCategory
  PF.canonicalProjectionFibre
canonicalLoomEncoding = record
  { Strand             = ⊤
  ; Weave              = ⊤
  ; weaveId            = λ _ → tt
  ; weaveSeq           = λ _ _ → tt
  ; ProjectionSurface  = ⊤
  ; project            = λ _ → tt
  ; fibreEquivalent    = λ _ _ → ⊤
  ; residual           = λ _ _ → ⊤
  ; closed             = λ _ _ → ⊤
  ; loomReading        = "Canonical LoomEncoding: trivial."
  }
