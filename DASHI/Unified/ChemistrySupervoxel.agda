module DASHI.Unified.ChemistrySupervoxel where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Interop.UnifiedMathLanguageAssertedProofs as Asserted
import DASHI.Interop.UnifiedMathLanguageSpine as Unified
import DASHI.Unified.InvariantSpine as Spine

chemistryProofSurface : Asserted.ChemistryDefinitionalProofSurface
chemistryProofSurface =
  Asserted.canonicalChemistryDefinitionalProofSurface

supervoxelChemistryProofSurface :
  Asserted.SupervoxelChemistryDefinitionalProofSurface
supervoxelChemistryProofSurface =
  Asserted.canonicalSupervoxelChemistryDefinitionalProofSurface

chemistryObject : Spine.UnifiedObjectInvariant
chemistryObject =
  Spine.unifiedObjectInvariant
    "chemistry-definitional-parent"
    Unified.chemistryLane
    "DNA chemistry quotient and Hamiltonian observations"
    "feature quotient -> concrete representative -> definitional law"
    Unified.chemistryChannelCarrier
    (Spine.defaultRoleVector "chemistry-definitional-parent")
    Residual.exact
    Asserted.internalDefinitionalProof
    Spine.stronglyInvariant
    (Spine.softJProjection "chemistry is strongly invariant locally, but not a literal modular-j theorem")
    (Spine.softFormalProjectionBundle "chemistry inherits Hecke/Bott/Kolmogorov/category projections as non-promoting carriers")

supervoxelChemistryObject : Spine.UnifiedObjectInvariant
supervoxelChemistryObject =
  Spine.unifiedObjectInvariant
    "supervoxel-chemistry-parent"
    Unified.chemistryLane
    "supervoxel coupling, reverse-complement, and streaming checksum observations"
    "supervoxel -> coupled chemistry carrier -> definitional receipt"
    Unified.supervoxelCarrier
    (Spine.defaultRoleVector "supervoxel-chemistry-parent")
    Residual.exact
    Asserted.internalDefinitionalProof
    Spine.stronglyInvariant
    (Spine.softJProjection "supervoxel chemistry keeps j as a non-promoting analogy axis only")
    (Spine.softFormalProjectionBundle "supervoxel chemistry inherits the DASHI formal projection parent family")

canonicalChemistrySupervoxelObjects : List Spine.UnifiedObjectInvariant
canonicalChemistrySupervoxelObjects =
  chemistryObject ∷ supervoxelChemistryObject ∷ []

chemistryJPromotionBlocked :
  Spine.objectExternalJPromotion chemistryObject ≡ false
chemistryJPromotionBlocked =
  refl

supervoxelChemistryJPromotionBlocked :
  Spine.objectExternalJPromotion supervoxelChemistryObject ≡ false
supervoxelChemistryJPromotionBlocked =
  refl
