module DASHI.Physics.Bridge where

-- Thin adapter surface above ClosureGlue / Signature31.
-- This module intentionally contains only stable names/types.

open import DASHI.Physics.ClosureGlue using (ClosureAxioms)

open ClosureAxioms public

record BridgeSurface : Set₁ where
  field
    A : ClosureAxioms

open BridgeSurface public
