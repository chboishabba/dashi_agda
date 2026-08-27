module DASHI.Culture.KimmererBraidTransferResidualBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Culture.KimmererNarrativeMetaphorCalibrationExact as Kimmerer
import DASHI.Reasoning.MetaphorTransferResidualExact as Residual
import DASHI.Reasoning.StructuralMetaphorSourceRegistryExact as Sources

------------------------------------------------------------------------
-- KIMMERER BRAID / TRANSFER-RESIDUAL BOUNDARY
--
-- This module does not add a new reading to Braiding Sweetgrass.  It connects
-- the existing source-bounded DASHI calibration reading to the generic
-- missing-vs-spurious transfer distinction.
--
-- Two opposite errors are kept separate:
--
--   1. UNDER-TRANSFER: reading 'braid' as mere multiplicity can omit the
--      reciprocity / held-relation structure the calibrated reading retains.
--
--   2. OVER-TRANSFER: forcing a braid/recoverability frame onto a genuinely
--      ruptured target can import a relation that is no longer supported.
--
-- The latter is especially important after Fatima (2026), DOI
-- 10.46809/jcsll.v7i2.430: methodological calibration includes knowing when a
-- structural vocabulary should withdraw rather than compel recoverability.
------------------------------------------------------------------------

kimmererSource : Sources.SourceReference
kimmererSource = Sources.kimmerer2013

underTransferProfile : Residual.TransferResidualProfile
underTransferProfile = Residual.missingReciprocityProfile

overTransferProfile : Residual.TransferResidualProfile
overTransferProfile = Residual.spuriousRecoverabilityProfile

calibrationReading : String
calibrationReading =
  "The DASHI braid interpretation is bounded on both sides: a coarse multiplicity reading can omit relevant relational structure, while a forced universal braid reading can spuriously import recoverability after rupture."

record KimmererTransferResidualBoundary : Set where
  constructor kimmererTransferResidualBoundary
  field
    coarseBraidReadingMayMissRelationalStructure : Bool
    coarseBraidReadingMayMissRelationalStructureIsTrue :
      coarseBraidReadingMayMissRelationalStructure ≡ true

    braidFrameMaySpuriouslyImposeRecoverability : Bool
    braidFrameMaySpuriouslyImposeRecoverabilityIsTrue :
      braidFrameMaySpuriouslyImposeRecoverability ≡ true

    everyRuptureShouldBeReframedAsLatentBraiding : Bool
    everyRuptureShouldBeReframedAsLatentBraidingIsFalse :
      everyRuptureShouldBeReframedAsLatentBraiding ≡ false

    kimmererStatesMissingSpuriousResidualFormalism : Bool
    kimmererStatesMissingSpuriousResidualFormalismIsFalse :
      kimmererStatesMissingSpuriousResidualFormalism ≡ false

    dashiResidualBridgeIsInterpretiveExtension : Bool
    dashiResidualBridgeIsInterpretiveExtensionIsTrue :
      dashiResidualBridgeIsInterpretiveExtension ≡ true

canonicalKimmererTransferResidualBoundary : KimmererTransferResidualBoundary
canonicalKimmererTransferResidualBoundary =
  kimmererTransferResidualBoundary
    true refl
    true refl
    false refl
    false refl
    true refl

existingKimmererCalibrationBoundary : Kimmerer.KimmererNarrativeCalibrationBoundary
existingKimmererCalibrationBoundary = Kimmerer.canonicalKimmererNarrativeCalibrationBoundary
