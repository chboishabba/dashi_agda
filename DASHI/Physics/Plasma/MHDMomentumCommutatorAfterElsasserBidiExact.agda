module DASHI.Physics.Plasma.MHDMomentumCommutatorAfterElsasserBidiExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Plasma.MHDHelicalElsasserTriadHypervoxelExact as V
import DASHI.Physics.Plasma.MHDHelicalElsasserInteractionAdmissibilityExact as A

------------------------------------------------------------------------
-- MOMENTUM-SIDE COMMUTATOR SURVIVAL AFTER ELSASSER RECHART
--
-- The algebraic zero-sum may survive recharting only after the literal MHD
-- momentum coefficients and amplitude channels are welded to the same triad.
------------------------------------------------------------------------

record MomentumThreeSlotKernel : Set₁ where
  constructor momentum-three-slot-kernel
  field
    Coefficient Amplitude : Set
    ck cp cq : Coefficient
    bk bp bq : Amplitude
    coefficientSumZero : Set
    slotDifferenceRewrite : Set

open MomentumThreeSlotKernel public

record ElsasserMomentumCommutatorReceipt
    (voxel : V.MHDHelicalElsasserTriadHypervoxel) : Set₁ where
  constructor elsasser-momentum-commutator-receipt
  field
    sectorIsMomentum : V.equationSector voxel ≡ V.momentumSector
    admittedInteraction : A.AdmittedMHDTriadInteraction voxel
    kernel : MomentumThreeSlotKernel
    literalCoefficientIdentification : Set
    literalAmplitudeIdentification : Set
    rechartPreservesLiteralTriadObject : Set
    commutatorSameObjectReceipt : Set

open ElsasserMomentumCommutatorReceipt public

record MomentumCommutatorBidiBoundary : Set where
  constructor momentum-commutator-bidi-boundary
  field
    abstractZeroSumProvesLiteralMHDCommutator : Bool
    abstractZeroSumProvesLiteralMHDCommutatorIsFalse :
      abstractZeroSumProvesLiteralMHDCommutator ≡ false

    elsasserRechartAloneCreatesCancellation : Bool
    elsasserRechartAloneCreatesCancellationIsFalse :
      elsasserRechartAloneCreatesCancellation ≡ false

    admittedMomentumReceiptMayExposeCommutator : Bool
    admittedMomentumReceiptMayExposeCommutatorIsTrue :
      admittedMomentumReceiptMayExposeCommutator ≡ true

canonicalMomentumCommutatorBidiBoundary : MomentumCommutatorBidiBoundary
canonicalMomentumCommutatorBidiBoundary =
  momentum-commutator-bidi-boundary false refl false refl true refl
