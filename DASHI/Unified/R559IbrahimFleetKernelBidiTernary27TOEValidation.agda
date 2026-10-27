{-# OPTIONS --safe #-}
module DASHI.Unified.R559IbrahimFleetKernelBidiTernary27TOEValidation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Unified.R559IbrahimFleetKernelBidiTernary27TOEExact as Exact

validationReceipt :
  Exact.R559IbrahimFleetKernelBidiTernary27TOEReceipt
validationReceipt =
  Exact.canonicalR559IbrahimFleetKernelBidiTernary27TOEReceipt

validationFleetFormalGaps : Exact.Base.fleetFormalGaps ≡ 58
validationFleetFormalGaps = Exact.fleetFormalGapsStill58

validationFleetDischargedFibres : Exact.Base.fleetDischargedFibres ≡ 584
validationFleetDischargedFibres = Exact.fleetDischargedFibresStill584

validationRustBindingUnpaid :
  Exact.ABI.rustU8BindingPaid Exact.triadicByteBoundary ≡ false
validationRustBindingUnpaid = Exact.rustU8BindingStillUnpaid

validationKernelIntertwinerUnpaid :
  Exact.KernelBidi.characterIsotypyConstructsActionIntertwiner
    Exact.kernelBidiBoundary ≡ false
validationKernelIntertwinerUnpaid =
  Exact.kernelCharacterIsotypyStillDoesNotConstructActionIntertwiner

validationSingleProducerUninhabited :
  Exact.SingleProducer.actualSingleProducerInhabitedHere
    Exact.singleProducerBoundary ≡ false
validationSingleProducerUninhabited =
  Exact.singleActionProducerStillUninhabited
