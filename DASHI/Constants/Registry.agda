module DASHI.Constants.Registry where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Physics.Closure.PhotonuclearEmpiricalConstantsRegistry as PECR

------------------------------------------------------------------------
-- Repo-wide constants registry owner.
--
-- This module is intentionally conservative: it does not introduce a new
-- physics claim or duplicate empirical constants. It only names the existing
-- photonuclear empirical registry as the current repo-wide linked constant
-- surface, with explicit provenance and boundary tags.

data RegistryBoundary : Set where
  referenceOnly : RegistryBoundary
  noPhysicsClaim : RegistryBoundary

record ConstantsRegistryLink : Set₁ where
  field
    linkLabel : String
    sourceModule : String
    sourceRegistry : PECR.PhotonuclearConstantsRegistry
    sourceBoundary : PECR.ClaimBoundary
    provenanceNotes : List String

open ConstantsRegistryLink public

linkedRegistryEntryCount : ConstantsRegistryLink → Nat
linkedRegistryEntryCount link =
  PECR.registryEntryCount (ConstantsRegistryLink.sourceRegistry link)

record ConstantsRegistry : Set₁ where
  field
    registryLabel : String
    registryBoundary : RegistryBoundary
    linkedRegistry : ConstantsRegistryLink
    linkedRegistryCount : Nat
    linkedEntryCount : Nat
    noGlobalClaim : RegistryBoundary

open ConstantsRegistry public

canonicalPhotonuclearLink : ConstantsRegistryLink
canonicalPhotonuclearLink = record
  { linkLabel = "photonuclear-empirical"
  ; sourceModule =
      "DASHI.Physics.Closure.PhotonuclearEmpiricalConstantsRegistry"
  ; sourceRegistry = PECR.photonuclearConstantsRegistry
  ; sourceBoundary = PECR.notPhysicsClaim
  ; provenanceNotes =
      "current repo-side empirical constants owner"
      ∷ "registry is linked, not re-derived"
      ∷ "no new physics claim introduced"
      ∷ []
  }

repoWideConstantsRegistry : ConstantsRegistry
repoWideConstantsRegistry = record
  { registryLabel = "DASHI repo-wide constants owner"
  ; registryBoundary = noPhysicsClaim
  ; linkedRegistry = canonicalPhotonuclearLink
  ; linkedRegistryCount = suc zero
  ; linkedEntryCount = linkedRegistryEntryCount canonicalPhotonuclearLink
  ; noGlobalClaim = noPhysicsClaim
  }
