module DASHI.Core.ProofLens where

open import DASHI.Core.Prelude
open import DASHI.Core.FormalRole

-- Reusable ways in which a domain-specific role may be supported,
-- constrained, decomposed, or compared.
data ProofLens : Set where
  waveLens
  btBraidLens
  spectralLens
  graphLens
  categoryLens
  hamiltonianLens
  statisticalLens
  pnfLens
  historicalLens
  otherLens : ProofLens

-- Lens semantics remain domain- and role-indexed.  A spectral witness for an
-- observable need not have the same type as a spectral witness for an operator.
record LensFamily (D : RoleFamily) : Set₁ where
  field
    LensWitness : ProofLens → (r : FormalRole) → RoleType D r → Set

open LensFamily public

record RoleLensReceipt (Evidence : Set) : Set₁ where
  field
    domain      : RoleFamily
    lenses      : LensFamily domain
    role        : FormalRole
    payload     : RoleType domain role
    lens        : ProofLens
    witness     : LensWitness lenses lens role payload
    evidence    : Evidence
    Residual    : Set
    residual    : Residual
    Admissible  : Set
    admissible  : Admissible

open RoleLensReceipt public

-- A receipt preserves the selected domain, role, and lens definitionally.
receipt-domain :
  ∀ {Evidence : Set} (r : RoleLensReceipt Evidence) →
  RoleFamily
receipt-domain = domain

receipt-role :
  ∀ {Evidence : Set} (r : RoleLensReceipt Evidence) →
  FormalRole
receipt-role = role

receipt-lens :
  ∀ {Evidence : Set} (r : RoleLensReceipt Evidence) →
  ProofLens
receipt-lens = lens
