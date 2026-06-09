module DASHI.Unified.PNFHyperfabric where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PNFHyperfabric369 as Hyperfabric
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Interop.UnifiedMathLanguageAssertedProofs as Asserted
import DASHI.Interop.UnifiedMathLanguageSpine as Unified
import DASHI.Unified.InvariantSpine as Spine

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
