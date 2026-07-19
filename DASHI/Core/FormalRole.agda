module DASHI.Core.FormalRole where

open import DASHI.Core.Prelude

-- The formal job played by a term inside a domain/fibre.
-- Domain nouns are not baked into this vocabulary.
data FormalRole : Set where
  carrierSpaceRole
  stateRole
  operatorRole
  observableRole
  spectrumToolRole
  boundaryGateRole
  obstructionRole
  algebraRole
  proofObligationRole
  decompositionRole
  hamiltonianRole
  metricRole
  projectionRole
  residualRole
  receiptRole
  functorRole
  transitionRole
  invariantRole
  symmetryRole
  modeRole
  sourceRole
  sinkRole
  flowRole
  constraintRole
  remedyRole : FormalRole

-- A domain supplies the meaning of every formal role lazily through RoleType.
record RoleFamily : Set₁ where
  field
    Carrier  : Set
    RoleType : FormalRole → Set

open RoleFamily public

-- TypedTerm is the product of a domain/fibre, a formal role, evidence,
-- and a payload inhabiting the domain-specific interpretation of that role.
record TypedTerm (Evidence : Set) : Set₁ where
  field
    domain   : RoleFamily
    role     : FormalRole
    evidence : Evidence
    payload  : RoleType domain role

open TypedTerm public

-- Reclassification changes the role only when an explicit bridge is supplied.
reclassify :
  ∀ {Evidence : Set} →
  (t : TypedTerm Evidence) →
  (r′ : FormalRole) →
  (RoleType (domain t) (role t) → RoleType (domain t) r′) →
  TypedTerm Evidence
reclassify t r′ bridge =
  record
    { domain   = domain t
    ; role     = r′
    ; evidence = evidence t
    ; payload  = bridge (payload t)
    }
