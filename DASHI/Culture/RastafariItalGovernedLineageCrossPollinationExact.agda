module DASHI.Culture.RastafariItalGovernedLineageCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GovernedObservationProvenanceExact as Governed
import DASHI.Culture.RastafariItalMaterialProvenanceConservationExact as Material

------------------------------------------------------------------------
-- ITAL / GOVERNED COORDINATE-LINEAGE CROSS-POLLINATION
--
-- The merged governed-observation core now owns the exact multi-stage rule:
--
--   erase inherited provenance -> add provenance later
--   = introduced provenance, not restored inherited provenance.
--
-- This module applies that rule as a boundary for material/knowledge histories
-- associated with the Ital lane.  It does not assert that every transformation
-- erases provenance; applications must declare the actual coordinate effect.
------------------------------------------------------------------------

erasedThenReaddedProvenanceIsIntroduced :
  Governed.applyTwoEffects
    Governed.erasesCoordinate
    Governed.addsCoordinate
    Governed.inheritedCoordinate
  ≡ Governed.introducedCoordinate
erasedThenReaddedProvenanceIsIntroduced =
  Governed.additionAfterErasureIsIntroducedNotInherited

erasedThenReaddedProvenanceIsNotRestoredInherited :
  Governed.applyTwoEffects
    Governed.erasesCoordinate
    Governed.addsCoordinate
    Governed.inheritedCoordinate
  ≡ Governed.inheritedCoordinate → ⊥
erasedThenReaddedProvenanceIsNotRestoredInherited =
  Governed.additionAfterErasureDoesNotRestoreInheritedLineage

------------------------------------------------------------------------
-- Material provenance receipts remain the application-level evidence carrier.
------------------------------------------------------------------------

materialReceiptCarriesExplicitSource :
  Material.MaterialProvenanceReceipt → String
materialReceiptCarriesExplicitSource = Material.sourceReference

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data SameMaterialLabelRestoresErasedLineage : Set where

data LaterDocumentationRestoresOriginalAuthority : Set where

data SuccessfulReturnRestoresMissingPermission : Set where

sameMaterialLabelDoesNotRestoreErasedLineage :
  SameMaterialLabelRestoresErasedLineage → ⊥
sameMaterialLabelDoesNotRestoreErasedLineage ()

laterDocumentationDoesNotRestoreOriginalAuthority :
  LaterDocumentationRestoresOriginalAuthority → ⊥
laterDocumentationDoesNotRestoreOriginalAuthority ()

successfulReturnDoesNotRestoreMissingPermission :
  SuccessfulReturnRestoresMissingPermission → ⊥
successfulReturnDoesNotRestoreMissingPermission ()

record ItalGovernedLineageBoundary : Set where
  constructor italGovernedLineageBoundary
  field
    eraseThenAddRestoresInheritedProvenance : Bool
    eraseThenAddRestoresInheritedProvenanceIsFalse :
      eraseThenAddRestoresInheritedProvenance ≡ false

    provenanceLineageIsIndependentOfMaterialLabel : Bool
    provenanceLineageIsIndependentOfMaterialLabelIsTrue :
      provenanceLineageIsIndependentOfMaterialLabel ≡ true

    laterDocumentationCanAddNewProvenance : Bool
    laterDocumentationCanAddNewProvenanceIsTrue :
      laterDocumentationCanAddNewProvenance ≡ true

canonicalItalGovernedLineageBoundary : ItalGovernedLineageBoundary
canonicalItalGovernedLineageBoundary =
  italGovernedLineageBoundary false refl true refl true refl
