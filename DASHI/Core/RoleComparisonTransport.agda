module DASHI.Core.RoleComparisonTransport where

open import DASHI.Core.Prelude
open import DASHI.Core.FormalRole
open import DASHI.Core.ProofLens

-- Same-domain role transport requires an explicit payload map.
record RoleBridge (D : RoleFamily) (from to : FormalRole) : Set₁ where
  field
    bridgePayload : RoleType D from → RoleType D to

open RoleBridge public

transportRole :
  ∀ {Evidence : Set}
    {D : RoleFamily}
    {from to : FormalRole} →
  RoleBridge D from to →
  (e : Evidence) →
  RoleType D from →
  TypedTerm Evidence
transportRole {D = D} {to = to} bridge e x =
  record
    { domain   = D
    ; role     = to
    ; evidence = e
    ; payload  = bridgePayload bridge x
    }

-- Cross-domain transport is stronger: both the carrier interpretation and the
-- role payload must be mapped explicitly.  Shared role names alone provide no
-- transport.
record DomainRoleBridge
  (D₁ D₂ : RoleFamily)
  (r₁ r₂ : FormalRole)
  : Set₁ where
  field
    carrierMap : Carrier D₁ → Carrier D₂
    payloadMap : RoleType D₁ r₁ → RoleType D₂ r₂

open DomainRoleBridge public

transportAcrossDomains :
  ∀ {Evidence₁ Evidence₂ : Set}
    {D₁ D₂ : RoleFamily}
    {r₁ r₂ : FormalRole} →
  DomainRoleBridge D₁ D₂ r₁ r₂ →
  (Evidence₁ → Evidence₂) →
  Evidence₁ →
  RoleType D₁ r₁ →
  TypedTerm Evidence₂
transportAcrossDomains {D₂ = D₂} {r₂ = r₂} bridge evidenceMap e x =
  record
    { domain   = D₂
    ; role     = r₂
    ; evidence = evidenceMap e
    ; payload  = payloadMap bridge x
    }

-- Lens comparison is evidence about witnesses, not equality of lenses or
-- domains.
record LensComparison
  (D : RoleFamily)
  (L : LensFamily D)
  (r : FormalRole)
  (x : RoleType D r)
  (left right : ProofLens)
  : Set₁ where
  field
    Comparison : Set
    compareWitnesses :
      LensWitness L left r x →
      LensWitness L right r x →
      Comparison

open LensComparison public

-- Minimal theorem-shaped guards.
sharedRoleRequiresBridge :
  ∀ {D₁ D₂ : RoleFamily} {r : FormalRole} →
  (RoleType D₁ r → RoleType D₂ r) →
  RoleType D₁ r → RoleType D₂ r
sharedRoleRequiresBridge bridge = bridge

sharedLensRequiresWitnessMap :
  ∀ {D : RoleFamily}
    {L : LensFamily D}
    {r : FormalRole}
    {x : RoleType D r}
    {left right : ProofLens} →
  (LensWitness L left r x → LensWitness L right r x) →
  LensWitness L left r x → LensWitness L right r x
sharedLensRequiresWitnessMap bridge = bridge
