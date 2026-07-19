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
    receiptDomain     : RoleFamily
    receiptLenses     : LensFamily receiptDomain
    receiptRole       : FormalRole
    receiptPayload    : RoleType receiptDomain receiptRole
    receiptLens       : ProofLens
    receiptWitness    :
      LensWitness receiptLenses receiptLens receiptRole receiptPayload
    receiptEvidence   : Evidence
    Residual           : Set
    receiptResidual   : Residual
    Admissible         : Set
    receiptAdmissible : Admissible

open RoleLensReceipt public

-- A receipt preserves its selected domain, role, and lens definitionally.
receipt-domain :
  ∀ {Evidence : Set} → RoleLensReceipt Evidence → RoleFamily
receipt-domain = receiptDomain

receipt-role :
  ∀ {Evidence : Set} → RoleLensReceipt Evidence → FormalRole
receipt-role = receiptRole

receipt-lens :
  ∀ {Evidence : Set} → RoleLensReceipt Evidence → ProofLens
receipt-lens = receiptLens
