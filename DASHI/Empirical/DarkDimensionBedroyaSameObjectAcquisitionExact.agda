module DASHI.Empirical.DarkDimensionBedroyaSameObjectAcquisitionExact where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.SourceAcquisitionGeometryExact as Acquisition
import DASHI.Interop.SourceDiligenceProofSearchBridgeExact as SourceSearch
import DASHI.Empirical.DarkDimensionResidualDebtRoutingExact as DebtRouting
import DASHI.Empirical.DarkDimensionFadingDMParentLineageExact as ParentLineage

------------------------------------------------------------------------
-- BEDROYA 2026 SAME-OBJECT ACQUISITION ADAPTER
--
-- Thin adapter over existing source-acquisition and proof-directed-search
-- machinery.  The target is the exact child numerical object required by the
-- live reconstruction consumer.  Parent/ancestor lineage may guide where to
-- search, but cannot substitute for child implementation, normalization or
-- same-fit manifest custody.
------------------------------------------------------------------------

bedroya2026SameObjectTarget : Acquisition.SourceAcquisitionTarget
bedroya2026SameObjectTarget =
  Acquisition.sourceAcquisitionTarget
    "2026 Bedroya-Obied-Vafa-Wu same-fit parameter manifest and normalization map"
    "DESI+CMB+Pantheon+ negative-c best-fit chain/config or machine-readable manifest"
    Acquisition.directDigitalArchive
    Acquisition.publisherBackfile
    false
    false
    false

bedroyaIdentitySearchDemand : SourceSearch.SourceDiligenceSearchDemand
bedroyaIdentitySearchDemand = DebtRouting.bedroyaManifestIdentitySearchDemand

childSameObjectStillUnacquired :
  Acquisition.fullTextAcquired bedroya2026SameObjectTarget ≡ false
childSameObjectStillUnacquired = refl

childPrimaryObjectStillUninspected :
  Acquisition.primaryTextInspected bedroya2026SameObjectTarget ≡ false
childPrimaryObjectStillUninspected = refl

childTranscriptionStillUnextracted :
  Acquisition.transcriptionExtracted bedroya2026SameObjectTarget ≡ false
childTranscriptionStillUnextracted = refl

parentLineageMayGuideSearchButCannotSubstitute :
  ParentLineage.exactImplementationInheritanceDemonstrated
    ParentLineage.canonicalFadingDMParentLineageStatus
  ≡ false
parentLineageMayGuideSearchButCannotSubstitute =
  ParentLineage.parentImplementationInheritanceStillOpen

------------------------------------------------------------------------
-- WrongType / same-object firewalls.
------------------------------------------------------------------------

data ParentImplementationPaysChildSameObjectDemand : Set where

data ParentNormalizationPaysChildSameObjectDemand : Set where

parentImplementationCannotPayChildSameObjectDemand :
  ParentImplementationPaysChildSameObjectDemand → ⊥
parentImplementationCannotPayChildSameObjectDemand ()

parentNormalizationCannotPayChildSameObjectDemand :
  ParentNormalizationPaysChildSameObjectDemand → ⊥
parentNormalizationCannotPayChildSameObjectDemand ()
