module DASHI.Core.IndexedRoleEvidence where

open import DASHI.Core.Prelude
open import DASHI.Core.FormalRole
open import DASHI.Core.ProofLens

-- Evidence is indexed by the precise domain, role, and payload it supports.
-- This prevents evidence for one fibre or role from being silently reused for
-- another merely because both share a surface label.
record EvidenceFamily (D : RoleFamily) : Set₁ where
  field
    EvidenceFor : (r : FormalRole) → RoleType D r → Set

open EvidenceFamily public

record IndexedTypedTerm (D : RoleFamily) (E : EvidenceFamily D) : Set₁ where
  field
    indexedRole     : FormalRole
    indexedPayload  : RoleType D indexedRole
    indexedEvidence : EvidenceFor E indexedRole indexedPayload

open IndexedTypedTerm public

-- Residual and admissibility are likewise indexed.  Admissibility is not an
-- arbitrary proposition stored beside a receipt: it is the output of a named
-- gate applied to the evidence and residual for this payload.
record ReceiptPolicy (D : RoleFamily) (E : EvidenceFamily D) : Set₁ where
  field
    ResidualFor : (r : FormalRole) → RoleType D r → Set
    Gate :
      (r : FormalRole) →
      (x : RoleType D r) →
      EvidenceFor E r x →
      ResidualFor r x →
      Set

open ReceiptPolicy public

record GovernedRoleLensReceipt
  (D : RoleFamily)
  (E : EvidenceFamily D)
  (L : LensFamily D)
  (P : ReceiptPolicy D E)
  : Set₁ where
  field
    governedRole       : FormalRole
    governedPayload    : RoleType D governedRole
    governedLens       : ProofLens
    governedWitness    :
      LensWitness L governedLens governedRole governedPayload
    governedEvidence   : EvidenceFor E governedRole governedPayload
    governedResidual   : ResidualFor P governedRole governedPayload
    governedAdmissible :
      Gate P governedRole governedPayload governedEvidence governedResidual

open GovernedRoleLensReceipt public

-- Forgetful projection to the compact prototype receipt.  Governance remains
-- explicit in the source object; no promotion theorem is introduced.
forgetGovernance :
  ∀ {D : RoleFamily}
    {E : EvidenceFamily D}
    {L : LensFamily D}
    {P : ReceiptPolicy D E} →
  GovernedRoleLensReceipt D E L P →
  RoleLensReceipt
    (Σ FormalRole (λ r → Σ (RoleType D r) (EvidenceFor E r)))
forgetGovernance {D} {E} {L} {P} g =
  record
    { receiptDomain     = D
    ; receiptLenses     = L
    ; receiptRole       = governedRole g
    ; receiptPayload    = governedPayload g
    ; receiptLens       = governedLens g
    ; receiptWitness    = governedWitness g
    ; receiptEvidence   =
        governedRole g , governedPayload g , governedEvidence g
    ; Residual           = ResidualFor P (governedRole g) (governedPayload g)
    ; receiptResidual   = governedResidual g
    ; Admissible         =
        Gate P
          (governedRole g)
          (governedPayload g)
          (governedEvidence g)
          (governedResidual g)
    ; receiptAdmissible = governedAdmissible g
    }
