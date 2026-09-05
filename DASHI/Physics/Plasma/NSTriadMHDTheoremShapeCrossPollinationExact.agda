module DASHI.Physics.Plasma.NSTriadMHDTheoremShapeCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNCriticalHelicitySlotCommutatorRound138Exact as NS138

------------------------------------------------------------------------
-- NS <-> MHD THEOREM-SHAPE CROSS-POLLINATION
--
-- Round138 owns an exact zero-sum three-slot coefficient identity and rewrites
-- production through slot DIFFERENCES.  This module extracts that pattern as a
-- reusable theorem shape.  The NS proof term remains NS-owned; MHD must supply
-- its own physical slot map and triad coefficient receipt.
------------------------------------------------------------------------

record ThreeSlotZeroSumShape : Set₁ where
  constructor three-slot-zero-sum-shape
  field
    Scalar : Set
    zero : Scalar
    add : Scalar → Scalar → Scalar
    sub : Scalar → Scalar → Scalar
    mul : Scalar → Scalar → Scalar
    ck cp cq : Scalar
    coefficientsSumZero : add ck (add cp cq) ≡ zero
    shapeReference : String

open ThreeSlotZeroSumShape public

record SlotDifferenceFactorisation
    (shape : ThreeSlotZeroSumShape) : Set₁ where
  constructor slot-difference-factorisation
  field
    SlotAmplitude : Set
    action : Scalar shape → SlotAmplitude → SlotAmplitude
    combine : SlotAmplitude → SlotAmplitude → SlotAmplitude
    difference : SlotAmplitude → SlotAmplitude → SlotAmplitude
    zeroAmplitude : SlotAmplitude

    factorisationReceipt : Set
    commonSlotCancels : Set
    factorisationReference : String

open SlotDifferenceFactorisation public

------------------------------------------------------------------------
-- MHD instantiation obligation.
-- In Elsasser/helical MHD, the relevant nonlinear channels are not obtained by
-- renaming NS velocity amplitudes.  A local application must identify:
--   * literal MHD triad;
--   * +/- Elsasser/helicity channel;
--   * MHD interaction coefficient;
--   * slot observer;
--   * local zero-sum / commutator identity.
------------------------------------------------------------------------

record MHDTriadInstantiation : Set₁ where
  constructor mhd-triad-instantiation
  field
    Wavevector : Set
    ElsasserSign : Set
    HelicitySign : Set
    Amplitude : Set
    Coefficient : Set

    k p q : Wavevector
    plusMinusChannel : ElsasserSign
    helicityChannel : HelicitySign
    bk bp bq : Amplitude
    ck cp cq : Coefficient

    triadClosure : Set
    incompressibilityReceipt : Set
    mhdInteractionCoefficientReceipt : Set
    localZeroSumReceipt : Set
    slotDifferenceReceipt : Set
    applicationReference : String

open MHDTriadInstantiation public

------------------------------------------------------------------------
-- BIDI boundary.
------------------------------------------------------------------------

record NSTriadMHDBidiBoundary : Set where
  constructor ns-triad-mhd-bidi-boundary
  field
    round138ExactAlgebraIsReusableTheoremShape : Bool
    round138ExactAlgebraIsReusableTheoremShapeIsTrue :
      round138ExactAlgebraIsReusableTheoremShape ≡ true

    round138NSReceiptIsMHDReceipt : Bool
    round138NSReceiptIsMHDReceiptIsFalse :
      round138NSReceiptIsMHDReceipt ≡ false

    dimensionOrSignSimilarityProvesSameInteractionCoefficient : Bool
    dimensionOrSignSimilarityProvesSameInteractionCoefficientIsFalse :
      dimensionOrSignSimilarityProvesSameInteractionCoefficient ≡ false

    mhdNeedsLiteralTriadCoefficientWeld : Bool
    mhdNeedsLiteralTriadCoefficientWeldIsTrue :
      mhdNeedsLiteralTriadCoefficientWeld ≡ true

    commonModeCancellationShouldBeTestedBeforeAbsoluteValues : Bool
    commonModeCancellationShouldBeTestedBeforeAbsoluteValuesIsTrue :
      commonModeCancellationShouldBeTestedBeforeAbsoluteValues ≡ true

canonicalNSTriadMHDBidiBoundary : NSTriadMHDBidiBoundary
canonicalNSTriadMHDBidiBoundary =
  ns-triad-mhd-bidi-boundary true refl false refl false refl true refl true refl

-- Explicit provenance pin: the donor is the exact NS Round138 owner, but no
-- field from that module is imported as an MHD application receipt.
nsRound138DonorReference : String
nsRound138DonorReference =
  "DASHI.Physics.Closure.NSTriadKNCriticalHelicitySlotCommutatorRound138Exact"

nsRound138DonorClosed : Bool
nsRound138DonorClosed = NS138.round138HelicitySlotDifferenceCommutatorClosed

nsRound138DonorClosedIsTrue : nsRound138DonorClosed ≡ true
nsRound138DonorClosedIsTrue = NS138.round138HelicitySlotDifferenceCommutatorClosedIsTrue
