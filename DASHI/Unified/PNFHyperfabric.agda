module DASHI.Unified.PNFHyperfabric where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PNFHyperfabric369 as Hyperfabric
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Interop.UnifiedMathLanguageAssertedProofs as Asserted
import DASHI.Interop.UnifiedMathLanguageSpine as Unified
import DASHI.Unified.InvariantSpine as Spine
import DASHI.Cognition.PNF.SetwiseGroupedFibreProjectionExact as DeltaProjection
import DASHI.Cognition.PNF.AffectedBoundaryLocalReductionExact as LocalReduction
import DASHI.Cognition.PNF.SentenceAnaphorSetwiseProjectionExact as Anaphor

pnfHyperfabricSurface : Hyperfabric.PNFHyperfabric369Surface
pnfHyperfabricSurface =
  Hyperfabric.canonicalPNFHyperfabric369Surface

pnfHyperfabricObject : Spine.UnifiedObjectInvariant
pnfHyperfabricObject =
  Spine.unifiedObjectInvariant
    "pnf-hyperfabric-369-parent"
    Unified.legalPnfItirLane
    "PNF 369 hyperfabric observations"
    "PNF/dialectic/tri-truth/document-time -> hyperfabric object"
    Unified.hyperfabricCarrier
    (Hyperfabric.objectRoleVector Hyperfabric.universalMathLanguageHyperfabric)
    Residual.exact
    Asserted.internalDefinitionalProof
    Spine.stronglyInvariant
    (Spine.softJProjection "PNF hyperfabric tracks SSP/Monster carriers without literal modular-j authority")
    (Spine.softFormalProjectionBundle "PNF hyperfabric inherits Hecke/Bott/Kolmogorov/category projections as carrier structure")

canonicalPNFHyperfabricObjects : List Spine.UnifiedObjectInvariant
canonicalPNFHyperfabricObjects =
  pnfHyperfabricObject ∷ []

pnfHyperfabricJPromotionBlocked :
  Spine.objectExternalJPromotion pnfHyperfabricObject ≡ false
pnfHyperfabricJPromotionBlocked =
  refl


------------------------------------------------------------------------
-- SensibLaw delta-fed PNF execution surface.
--
-- The unified layer is a consumer.  The theorem owners remain in
-- DASHI.Cognition.PNF.
------------------------------------------------------------------------

pnfDeltaFedProjectionOwner :
  Set₁
pnfDeltaFedProjectionOwner =
  DeltaProjection.DeltaFedProjection Set Set Set Set

pnfAffectedLocalReducerOwner :
  Set₁
pnfAffectedLocalReducerOwner =
  LocalReduction.AffectedLocalReducer Set Set Set

pnfAnaphorSurfaceIdentityPromotionImpossible :
  Anaphor.SurfaceSpellingIsWitnessIdentity → ⊥
pnfAnaphorSurfaceIdentityPromotionImpossible =
  Anaphor.surfaceSpellingIsNotWitnessIdentity

pnfAnaphorCandidateResolutionPromotionImpossible :
  Anaphor.CandidateEvidenceResolvesProjectedAnaphor → ⊥
pnfAnaphorCandidateResolutionPromotionImpossible =
  Anaphor.candidateEvidenceCannotResolveProjection

pnfAnaphorRecursiveSelfUpdateImpossible :
  Anaphor.SetwiseProjectionRequiresRecursiveDemandUpdate → ⊥
pnfAnaphorRecursiveSelfUpdateImpossible =
  Anaphor.setwiseProjectionNeedsNoRecursiveDemandRewrite

pnfAnaphorProceduralProjectionCannotClaimSetBased :
  Anaphor.ProceduralPerOccurrenceProjectionIsSetBased → ⊥
pnfAnaphorProceduralProjectionCannotClaimSetBased =
  Anaphor.perOccurrenceProceduralProjectionIsNotSetBased
