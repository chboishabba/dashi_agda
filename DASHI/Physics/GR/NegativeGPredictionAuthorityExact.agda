module DASHI.Physics.GR.NegativeGPredictionAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.GravitationalPredictionAttributionBidiExact as Attr
import DASHI.Physics.GR.GravitationalEpistemicLineageExact as Lineage

------------------------------------------------------------------------
-- NEGATIVE-G INTERNAL AUTHORITY
--
-- The signed-G counterfactuals constructed in this repo are internal theorem
-- lineages.  An arbitrary internal theorem is not enough: the lineage must
-- identify one of the actual signed-G owners, and any claim-specific prediction
-- scope requires an explicit adapter receipt.
------------------------------------------------------------------------

data NegativeGInternalOwner : Set where
  signedEinsteinWeakFieldOwner : NegativeGInternalOwner
  signedNewtonianOwner : NegativeGInternalOwner
  signedGravitationalWaveOwner : NegativeGInternalOwner
  signedCosmologyOwner : NegativeGInternalOwner
  universalSignedGCrossScaleOwner : NegativeGInternalOwner

ownerModulePath : NegativeGInternalOwner → String
ownerModulePath signedEinsteinWeakFieldOwner =
  "DASHI/Physics/GR/SignedEinsteinCouplingBidiExact.agda"
ownerModulePath signedNewtonianOwner =
  "DASHI/Physics/GR/SignedNewtonianLimitBidiExact.agda"
ownerModulePath signedGravitationalWaveOwner =
  "DASHI/Physics/GR/SignedGravitationalWaveCouplingBidiExact.agda"
ownerModulePath signedCosmologyOwner =
  "DASHI/Physics/GR/SignedCosmologicalMatterCouplingBidiExact.agda"
ownerModulePath universalSignedGCrossScaleOwner =
  "DASHI/Physics/GR/UniversalSignedGCrossScaleFingerprintBidiExact.agda"

ownerTheoremFamily : NegativeGInternalOwner → String
ownerTheoremFamily signedEinsteinWeakFieldOwner =
  "frozen signed-Einstein coupling weak-field sign probe"
ownerTheoremFamily signedNewtonianOwner =
  "signed Newtonian/Poisson limit sign probe"
ownerTheoremFamily signedGravitationalWaveOwner =
  "signed-G wave generation/propagation separation"
ownerTheoremFamily signedCosmologyOwner =
  "signed cosmological matter-coupling sign probe"
ownerTheoremFamily universalSignedGCrossScaleOwner =
  "universal signed-G cross-scale fingerprint"

record NegativeGInternalPredictionAuthority
    (prediction : Attr.AttributedGravitationalPrediction) : Set₁ where
  constructor negative-g-internal-prediction-authority
  field
    owner : NegativeGInternalOwner
    lineage : Lineage.InternalTheoremProofLineage

    predictionAuthorityIsThisLineage :
      Attr.authority prediction ≡ Attr.internalTheoremAuthority lineage

    modulePathMatchesOwner :
      Lineage.modulePath lineage ≡ ownerModulePath owner

    theoremFamilyMatchesOwner :
      Lineage.theoremName lineage ≡ ownerTheoremFamily owner

    predictionScopeMatchesLineage :
      Attr.predictionAuthorityClaimScope (Attr.authority prediction)
        ≡ Lineage.proofStatementScope lineage

    ScopeAdapter : Set
    scopeAdapterReceipt : ScopeAdapter

open NegativeGInternalPredictionAuthority public

record NegativeGPredictionAuthorityBoundary : Set where
  constructor negative-g-prediction-authority-boundary
  field
    anyInternalTheoremMayAuthorizeNegativeGPrediction : Bool
    exactSignedGOwnerRequired : Bool
    exactInternalModulePathRequired : Bool
    exactTheoremFamilyRequired : Bool
    claimSpecificScopeAdapterRequired : Bool
    internalLineageCountsAsExternalScientificCitation : Bool
    negativeGAuthorityAutomaticallyEstablishesPhysicalNegativeG : Bool

canonicalNegativeGPredictionAuthorityBoundary : NegativeGPredictionAuthorityBoundary
canonicalNegativeGPredictionAuthorityBoundary =
  negative-g-prediction-authority-boundary
    false true true true true false false
