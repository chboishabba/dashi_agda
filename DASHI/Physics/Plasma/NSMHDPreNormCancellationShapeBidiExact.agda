module DASHI.Physics.Plasma.NSMHDPreNormCancellationShapeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.MHDElsasserSkewPairCancellationKernelExact as Kernel

------------------------------------------------------------------------
-- NS <-> MHD CROSS-POLLINATION: PRE-NORM SIGNED CANCELLATION SHAPE
--
-- NS Round428/429 provide one concrete application in which two partial-adjoint
-- channels hit the same signed trilinear symbol before norms.  MHD Elsasser
-- coupling provides another application shaped by skew exchange of paired
-- slots.  Only the theorem shape is shared.
------------------------------------------------------------------------

record PreNormCancellationShape : Set₁ where
  constructor pre-norm-cancellation-shape
  field
    Channel State Weight : Set
    firstChannel secondChannel : Channel
    signedBalanceReceipt : Set
    commonWeightPreservesBalanceReceipt : Set
    cancellationBeforeNormReceipt : Set
    shapeReference : String

open PreNormCancellationShape public

record NSMHDShapeBridge : Set₁ where
  constructor ns-mhd-shape-bridge
  field
    nsShape : PreNormCancellationShape
    mhdShape : PreNormCancellationShape
    sharedAbstractKernel : Set
    nsApplicationReceiptTransferredToMHD : Bool
    nsApplicationReceiptTransferredToMHDIsFalse :
      nsApplicationReceiptTransferredToMHD ≡ false
    mhdApplicationReceiptTransferredToNS : Bool
    mhdApplicationReceiptTransferredToNSIsFalse :
      mhdApplicationReceiptTransferredToNS ≡ false
    bridgeReference : String

open NSMHDShapeBridge public

record CrossPollinationBoundary : Set where
  constructor cross-pollination-boundary
  field
    sharedCancellationShapeMeansSamePDE : Bool
    sharedCancellationShapeMeansSamePDEIsFalse :
      sharedCancellationShapeMeansSamePDE ≡ false

    preNormSignedCancellationIsReusableShape : Bool
    preNormSignedCancellationIsReusableShapeIsTrue :
      preNormSignedCancellationIsReusableShape ≡ true

    weightedCancellationRequiresWeightSymmetry : Bool
    weightedCancellationRequiresWeightSymmetryIsTrue :
      weightedCancellationRequiresWeightSymmetry ≡ true

canonicalCrossPollinationBoundary : CrossPollinationBoundary
canonicalCrossPollinationBoundary =
  cross-pollination-boundary false refl true refl true refl
