module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoMaxCutStatusExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoBNS194268SameObjectExact as BNS
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoBlochRepresentationBoundaryExact as Bloch
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoARPESWitnessGateExact as ARPES

record CoQuarterTaSeTwoMaxCutStatus : Set where
  constructor co-quarter-tase-two-max-cut-status
  field
    bnsMetadataFixed : Bool
    independentOperationEqualityClosed : Bool
    blochPhaseImplemented : Bool
    sewingCocycleReceiptExpected : Bool
    materialHamiltonianClosed : Bool
    rawARPESPayloadPresent : Bool
    exactSpectralObserverClosed : Bool
    quantitativeFitClosed : Bool
    umbrellaIntegrated : Bool

canonicalCoQuarterTaSeTwoMaxCutStatus : CoQuarterTaSeTwoMaxCutStatus
canonicalCoQuarterTaSeTwoMaxCutStatus =
  co-quarter-tase-two-max-cut-status
    true
    false
    true
    true
    false
    false
    false
    false
    true

existingBNSStatus : BNS.OperationSameObjectStatus
existingBNSStatus = BNS.canonicalOperationSameObjectStatus

existingBlochStatus : Bloch.BlochSewingContract
existingBlochStatus = Bloch.canonicalBlochSewingContract

existingARPESStatus : ARPES.CoARPESAcquisitionStatus
existingARPESStatus = ARPES.canonicalCoARPESAcquisitionStatus
