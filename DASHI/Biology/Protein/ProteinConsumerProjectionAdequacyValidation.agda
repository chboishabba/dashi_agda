module DASHI.Biology.Protein.ProteinConsumerProjectionAdequacyValidation where

open import DASHI.Core.Prelude

import DASHI.Biology.Protein.ProteinConsumerProjectionAdequacyExact as Portfolio

------------------------------------------------------------------------
-- RED-first contract for the protein consumer-projection portfolio.
------------------------------------------------------------------------

boundary = Portfolio.canonicalProteinConsumerProjectionBoundary

thermalIdentityDefectRetained : Bool
thermalIdentityDefectRetained =
  Portfolio.ProteinConsumerProjectionBoundary.thermalIdentityProjectionInadequate boundary

conformationSequenceDefectRetained : Bool
conformationSequenceDefectRetained =
  Portfolio.ProteinConsumerProjectionBoundary.sequenceProjectionInadequateForConformation boundary

rateTopologyDefectRetained : Bool
rateTopologyDefectRetained =
  Portfolio.ProteinConsumerProjectionBoundary.topologyProjectionInadequateForRate boundary

thiolCysteinePresenceDefectRetained : Bool
thiolCysteinePresenceDefectRetained =
  Portfolio.ProteinConsumerProjectionBoundary.cysteinePresenceProjectionInadequateForModification boundary

thermalRepairRetained : Bool
thermalRepairRetained =
  Portfolio.ProteinConsumerProjectionBoundary.residueAwareThermalRepairRetained boundary

conformationRepairRetained : Bool
conformationRepairRetained =
  Portfolio.ProteinConsumerProjectionBoundary.environmentAwareConformationRepairRetained boundary

rateRepairRetained : Bool
rateRepairRetained =
  Portfolio.ProteinConsumerProjectionBoundary.rateCoordinateRepairRetained boundary

thiolRepairRetained : Bool
thiolRepairRetained =
  Portfolio.ProteinConsumerProjectionBoundary.accessibilityAwareModificationRepairRetained boundary

thirdProteinSystemRetained : Bool
thirdProteinSystemRetained =
  Portfolio.ProteinConsumerProjectionBoundary.thirdIndependentProteinSystemRetained boundary

sourceRolesRemainDistinct : Bool
sourceRolesRemainDistinct =
  Portfolio.ProteinConsumerProjectionBoundary.sourceRolesRemainDomainLocal boundary

attributionDoesNotTransfer : Bool
attributionDoesNotTransfer =
  Portfolio.ProteinConsumerProjectionBoundary.crossDomainAttributionTransfer boundary

identityDoesNotCreateAuthority : Bool
identityDoesNotCreateAuthority =
  Portfolio.ProteinConsumerProjectionBoundary.externalIdentityCreatesBiologicalAuthority boundary
