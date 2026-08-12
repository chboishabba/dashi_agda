module DASHI.Governance.ProvenanceRestitutionBoundary where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import DASHI.Governance.ProvenancePolicyTransport

------------------------------------------------------------------------
-- Reparative provenance transport.
--
-- Historical/damage provenance may legitimately alter present policy.  The
-- safety distinction is proposition-local remedy versus unbounded transfer of
-- responsibility or coercive permission across identity/group membership.
------------------------------------------------------------------------

record DamageRepairSystem : Set₁ where
  field
    Actor : Set
    Damage : Set
    damaged : Damage → Actor → Actor → Set
    Repair : Set
    repairClaim : Damage → Actor → Actor → Repair

open DamageRepairSystem public

record PropositionLocalRestitution (D : DamageRepairSystem) : Set₁ where
  field
    source injured : Actor D
    damage : Damage D
    damageWitness : damaged D damage source injured
    repair : Repair D
    repairIsLocal : repair ≡ repairClaim D damage injured source

open PropositionLocalRestitution public

------------------------------------------------------------------------
-- Material repair, admission of liability, release of restricted assets and
-- compensation are distinct legal/policy propositions.  None is promoted from
-- another without an application-supplied bridge.
------------------------------------------------------------------------

record RepairSemantics : Set₁ where
  field
    MaterialRepair : Set
    AdmissionOfLiability : Set
    RestrictedAssetRelease : Set
    Compensation : Set

open RepairSemantics public

data MaterialRepairAutomaticallyAdmitsLiability
    (R : RepairSemantics)
    (m : MaterialRepair R) : Set where

data AssetReleaseAutomaticallyIsCompensation
    (R : RepairSemantics)
    (a : RestrictedAssetRelease R) : Set where

materialRepairDoesNotAutomaticallyAdmitLiability :
  ∀ {R} {m : MaterialRepair R} →
  MaterialRepairAutomaticallyAdmitsLiability R m → ⊥
materialRepairDoesNotAutomaticallyAdmitLiability ()

assetReleaseDoesNotAutomaticallyBecomeCompensation :
  ∀ {R} {a : RestrictedAssetRelease R} →
  AssetReleaseAutomaticallyIsCompensation R a → ⊥
assetReleaseDoesNotAutomaticallyBecomeCompensation ()

------------------------------------------------------------------------
-- A reparative route is explicitly one route kind in the existing neutral
-- ProvenancePolicyTransport algebra.  Operationalising provenance therefore
-- cannot itself be used as a witness of weaponisation.
------------------------------------------------------------------------

record ReparativeRouteWitness (S : ProvenancePolicySystem) : Set₁ where
  field
    actor : Actor S
    evidence : PresentEvidence S
    RepairAction : Action S → Set
    repairAction :
      RepairAction
        (route S (provenance S actor) evidence (classify S evidence actor))

open ReparativeRouteWitness public

data ReparativeRouteAutomaticallyWeaponisation
    {S : ProvenancePolicySystem}
    (r : ReparativeRouteWitness S) : Set where

reparativeRouteDoesNotAutomaticallyWitnessWeaponisation :
  ∀ {S} {r : ReparativeRouteWitness S} →
  ReparativeRouteAutomaticallyWeaponisation r → ⊥
reparativeRouteDoesNotAutomaticallyWitnessWeaponisation ()

------------------------------------------------------------------------
-- Bargaining remains live when an enemy/adversary classification can route to
-- a negotiated/reparative action.  Aggressive classification alone therefore
-- does not prove an absorbing permanent-war policy.
------------------------------------------------------------------------

record LiveBargainingRoute (S : ProvenancePolicySystem) : Set₁ where
  field
    actor : Actor S
    evidence : PresentEvidence S
    NegotiatedAction : Action S → Set
    negotiated :
      NegotiatedAction
        (route S (provenance S actor) evidence (classify S evidence actor))

open LiveBargainingRoute public
