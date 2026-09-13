module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGAuthorityClosureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.GR.GravitationalEpistemicLineageExact as Lineage
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGModelProvenanceBidiExact as Provenance
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGModelAuthorityProofSearchExact as AuthoritySearch
import DASHI.Physics.ExoticGravity.SuperconductingConstitutiveNegativeGProofSearchExact as PhysicalSearch

------------------------------------------------------------------------
-- ACTUAL DASHI MODEL AUTHORITY CLOSURE
--
-- The generic authority router says an internally-derived model requires exact
-- module/theorem/scope identity.  The current DASHI material-effective-G model
-- now has that proof-lineage object.  This closes attribution/authority shape;
-- it does not close any physical residual.
------------------------------------------------------------------------

record DASHIInternalModelAuthorityReceipt : Set where
  constructor dashi-internal-model-authority-receipt
  field
    proofLineage : Lineage.InternalTheoremProofLineage
    proofLineageMatchesCanonical :
      proofLineage ≡ Provenance.materialEffectiveGProofLineage
    moduleIdentityMatches :
      Lineage.modulePath proofLineage
        ≡ "DASHI/Physics/ExoticGravity/SuperconductingConstitutiveNegativeGScopeWeldExact.agda"
    theoremIdentityMatches :
      Lineage.theoremName proofLineage ≡ "ConstitutiveNegativeGReceipt"
    scopeIdentityMatches :
      Lineage.proofStatementScope proofLineage
        ≡ "typed constitutive sign-reversal to material-effective negative-coupling interpretation only"
    noFreshExternalBibliographyRequired :
      Lineage.freshExternalBibliographyRequired proofLineage ≡ false

open DASHIInternalModelAuthorityReceipt public

canonicalDASHIInternalModelAuthorityReceipt : DASHIInternalModelAuthorityReceipt
canonicalDASHIInternalModelAuthorityReceipt =
  dashi-internal-model-authority-receipt
    Provenance.materialEffectiveGProofLineage refl refl refl refl refl

------------------------------------------------------------------------
-- Recompute: authority is not the current physical frontier.
------------------------------------------------------------------------

currentPhysicalStageAfterAuthorityClosure : PhysicalSearch.ConstitutiveNegativeGStage
currentPhysicalStageAfterAuthorityClosure = PhysicalSearch.currentConstitutiveNegativeGStage

currentPhysicalStageStillSourceCurrent :
  currentPhysicalStageAfterAuthorityClosure ≡ PhysicalSearch.sourceCurrentStage
currentPhysicalStageStillSourceCurrent = PhysicalSearch.currentStageIsSourceCurrent

genericInternalAuthorityRouteStillStartsAtIdentity :
  AuthoritySearch.currentDASHIEffectiveGAuthorityResidual
    ≡ AuthoritySearch.missingInternalModuleIdentity
genericInternalAuthorityRouteStillStartsAtIdentity =
  AuthoritySearch.currentDASHIEffectiveGAuthorityStartsAtInternalIdentity

record MaterialEffectiveGAuthorityClosureBoundary : Set where
  constructor material-effective-g-authority-closure-boundary
  field
    internalAuthorityShapeClosed : Bool
    authorityClosureEqualsPhysicalValidation : Bool
    authorityClosurePaysSourceCurrent : Bool
    authorityClosurePaysStressEnergy : Bool
    authorityClosurePaysConstitutiveSignMeasurement : Bool
    authorityClosureAllowsExternalLiTorrAttribution : Bool
    physicalFrontierRemainsOpen : Bool

canonicalMaterialEffectiveGAuthorityClosureBoundary :
  MaterialEffectiveGAuthorityClosureBoundary
canonicalMaterialEffectiveGAuthorityClosureBoundary =
  material-effective-g-authority-closure-boundary
    true false false false false false true
