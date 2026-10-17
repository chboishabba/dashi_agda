module DASHI.Physics.CondensedMatter.MATBG2026SourceDataAvailabilityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record MATBGSourceDataAvailabilityReceipt : Set where
  constructor matbg-source-data-availability-receipt
  field
    sourceDOI : String
    sourceRole : String
    publisherDataStatement : String
    publisherVisibleWorkbookCount : Nat
    bytesAcquiredInRepository : Bool
    sameSampleAsOther2026Study : Bool

open MATBGSourceDataAvailabilityReceipt public

xiao2026QTMSourceDataAvailability : MATBGSourceDataAvailabilityReceipt
xiao2026QTMSourceDataAvailability =
  matbg-source-data-availability-receipt
    "10.1038/s41586-026-10378-x"
    "QTM momentum/energy-resolved band imaging"
    "Data shown in the paper are provided with the paper; further plot/analysis data are available from the corresponding author on request"
    0
    false
    false

zhang2026EntropySourceDataAvailability : MATBGSourceDataAvailabilityReceipt
zhang2026EntropySourceDataAvailability =
  matbg-source-data-availability-receipt
    "10.1038/s41467-026-76179-y"
    "planar-tunnelling inverse-compressibility / chemical-potential / entropy spectroscopy"
    "Publisher page states source data are provided and exposes four Source Data XLSX downloads; additional supporting data are available from the corresponding author on request"
    4
    false
    false

record MATBGSourceDataAvailabilityBoundary : Set where
  constructor matbg-source-data-availability-boundary
  field
    qtmDataAvailabilitySourcePaid : Bool
    entropyDataAvailabilitySourcePaid : Bool
    entropyWorkbookCountSourcePaid : Bool
    qtmBytesAcquired : Bool
    entropyBytesAcquired : Bool
    qtmExperimentalReplayPaid : Bool
    entropyExperimentalReplayPaid : Bool
    crossStudySameSamplePaid : Bool

open MATBGSourceDataAvailabilityBoundary public

canonicalMATBGSourceDataAvailabilityBoundary : MATBGSourceDataAvailabilityBoundary
canonicalMATBGSourceDataAvailabilityBoundary =
  matbg-source-data-availability-boundary
    true true true false false false false false

record MATBGSourceDataAttributionBoundary : Set where
  constructor matbg-source-data-attribution-boundary
  field
    xiaoEtAlOwnQTMData : Bool
    zhangEtAlOwnEntropyData : Bool
    availabilityDoesNotTransferDataOwnership : Bool
    availabilityDoesNotCreateByteAcquisition : Bool
    separatePublisherDatasetsDoNotCreateSameSampleIdentity : Bool

open MATBGSourceDataAttributionBoundary public

canonicalMATBGSourceDataAttributionBoundary : MATBGSourceDataAttributionBoundary
canonicalMATBGSourceDataAttributionBoundary =
  matbg-source-data-attribution-boundary true true true true true
