module MonsterOntologyContracts where

open import MonsterOntos
open import GodelLattice
open import HeckeScan
open import CICADA71
open import PrimeRoles
open import MaassRestoration

------------------------------------------------------------------------
-- A CICADA/MTT “architecture contract” = a bundle of interfaces.

record CICADA71System : Set₁ where
  field
    -- Text ↦ coordinate
    coordLaw : CoordinateLaw

    -- Hecke scan (compatibility detector)
    hecke    : HeckeFamily

    -- Sharding function: Text → bucket
    shard    : Text → Nat
    shard-def : ∀ t → shard t ≡ bucket71 (encode t)

    -- Prime roles mapping is fixed
    roles : SSP → Role

    -- Optional restoration layer
    restoration : Restoration
